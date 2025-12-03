# Hardware Gap Resolution: Q16.16 μ-ALU Integration

## Overview

This document describes the implementation of Q16.16 fixed-point arithmetic in the Thiele CPU hardware to achieve bit-exact compatibility with the Python VM implementation.

## Problem Statement

The original hardware implementation used simple 32-bit integer arithmetic for μ-bit accumulation, which does NOT match the Q16.16 fixed-point specification defined in `spec/mu_alu_v1.md` and implemented in `thielecpu/mu_fixed.py`.

**Gaps Identified:**
1. No Q16.16 fixed-point arithmetic operations
2. No log₂ LUT implementation
3. No information_gain calculation for PDISCOVER operations  
4. MDLACC using integer bit-counting instead of Q16.16 format
5. No saturation handling matching Python implementation

## Solution: μ-ALU Module

### Files Created

1. **`thielecpu/hardware/mu_alu.v`** - Q16.16 fixed-point arithmetic unit
   - Implements all arithmetic operations (add, sub, mul, div)
   - Contains 256-entry log₂ LUT matching Python implementation
   - Provides information_gain calculation
   - Handles saturation at Q16_MAX/Q16_MIN

2. **`thielecpu/hardware/mu_alu_tb.v`** - Testbench for μ-ALU
   - Tests basic arithmetic operations
   - Verifies division by zero handling
   - Tests information gain calculation

3. **`thielecpu/hardware/HARDWARE_INTEGRATION.md`** - This document

### μ-ALU Interface

```verilog
module mu_alu (
    input wire clk,
    input wire rst_n,
    
    // Operation control
    input wire [2:0] op,           // 0=add, 1=sub, 2=mul, 3=div, 4=log2, 5=info_gain
    input wire [31:0] operand_a,   // Q16.16 operand A (or integer for info_gain)
    input wire [31:0] operand_b,   // Q16.16 operand B (or integer for info_gain)
    input wire valid,              // Operation valid
    
    // Result
    output reg [31:0] result,      // Q16.16 result
    output reg ready,              // Result ready
    output reg overflow            // Overflow/saturation occurred
);
```

### Operation Codes

| Operation | Code | Description |
|-----------|------|-------------|
| ADD | 3'd0 | Q16.16 addition with saturation |
| SUB | 3'd1 | Q16.16 subtraction with saturation |
| MUL | 3'd2 | Q16.16 multiplication: (a * b) >> 16 |
| DIV | 3'd3 | Q16.16 division: (a << 16) / b |
| LOG2 | 3'd4 | log₂(x) using LUT |
| INFO_GAIN | 3'd5 | log₂(before/after) for integer counts |

## Integration Steps

### Step 1: Add μ-ALU Instance to thiele_cpu.v

```verilog
// Add to thiele_cpu.v internal wires
wire [31:0] mu_alu_result;
wire mu_alu_ready;
wire mu_alu_overflow;
reg [2:0] mu_alu_op;
reg [31:0] mu_alu_operand_a;
reg [31:0] mu_alu_operand_b;
reg mu_alu_valid;

// Instantiate μ-ALU
mu_alu mu_alu_inst (
    .clk(clk),
    .rst_n(rst_n),
    .op(mu_alu_op),
    .operand_a(mu_alu_operand_a),
    .operand_b(mu_alu_operand_b),
    .valid(mu_alu_valid),
    .result(mu_alu_result),
    .ready(mu_alu_ready),
    .overflow(mu_alu_overflow)
);
```

### Step 2: Update MDLACC Implementation

Replace the current integer-based MDLACC with Q16.16:

```verilog
task execute_mdlacc;
    input [7:0] module_id;
    begin
        if (module_id < next_module_id) begin
            module_size = module_table[module_id];
            
            if (module_size > 0) begin
                // Calculate MDL cost in Q16.16 format
                integer max_element;
                integer bit_length;
                integer k;
                
                max_element = 0;
                for (k = 0; k < module_size; k = k + 1) begin
                    if (region_table[module_id][k] > max_element) begin
                        max_element = region_table[module_id][k];
                    end
                end
                
                // Compute bit length
                if (max_element == 0) begin
                    bit_length = 1;
                end else begin
                    bit_length = $clog2(max_element + 1);
                end
                
                // Convert to Q16.16: mdl_cost = (bit_length * module_size) << 16
                mdl_cost = (bit_length * module_size) << 16;
            end else begin
                mdl_cost = 0;
            end
            
            // Use μ-ALU for accumulation with saturation
            mu_alu_op <= 3'd0;  // ADD
            mu_alu_operand_a <= mu_accumulator;
            mu_alu_operand_b <= mdl_cost;
            mu_alu_valid <= 1'b1;
            
            // Wait for result
            @(posedge mu_alu_ready);
            mu_alu_valid <= 1'b0;
            
            if (mu_alu_overflow) begin
                csr_error <= 32'h6; // μ-bit overflow
            end else begin
                mu_accumulator <= mu_alu_result;
                csr_status <= 32'h5; // MDL accumulation successful
                mdl_ops_counter <= mdl_ops_counter + 1;
            end
        end else begin
            csr_error <= 32'h7; // Invalid module
        end
    end
endtask
```

### Step 3: Add PDISCOVER Operation (New)

Add a new opcode and implementation for partition discovery:

```verilog
// Add to opcodes
localparam [7:0] OPCODE_PDISCOVER = 8'h06;

// Add to main state machine
OPCODE_PDISCOVER: begin
    // operand_a = before (number of possibilities before partition)
    // operand_b = after (number of possibilities after partition)
    execute_pdiscover(operand_a, operand_b);
    pc_reg <= pc_reg + 4;
end

// New task for PDISCOVER
task execute_pdiscover;
    input [31:0] before;
    input [31:0] after;
    begin
        if (before > 0 && after > 0 && after <= before) begin
            // Use μ-ALU to compute information gain
            mu_alu_op <= 3'd5;  // INFO_GAIN
            mu_alu_operand_a <= before;
            mu_alu_operand_b <= after;
            mu_alu_valid <= 1'b1;
            
            // Wait for result
            @(posedge mu_alu_ready);
            mu_alu_valid <= 1'b0;
            
            if (mu_alu_overflow) begin
                csr_error <= 32'h8; // Information gain overflow
            end else begin
                // Accumulate information gain
                mu_alu_op <= 3'd0;  // ADD
                mu_alu_operand_a <= mu_accumulator;
                mu_alu_operand_b <= mu_alu_result;
                mu_alu_valid <= 1'b1;
                
                @(posedge mu_alu_ready);
                mu_alu_valid <= 1'b0;
                
                if (mu_alu_overflow) begin
                    csr_error <= 32'h6; // μ-bit overflow
                end else begin
                    mu_accumulator <= mu_alu_result;
                    csr_status <= 32'h6; // Discovery successful
                    partition_ops_counter <= partition_ops_counter + 1;
                end
            end
        end else begin
            csr_error <= 32'h9; // Invalid discovery parameters
        end
    end
endtask
```

### Step 4: Update CSR Interface

Update the info_gain CSR to provide Q16.16 value:

```verilog
// Update CSR assignments
assign info_gain = mu_accumulator;  // Already in Q16.16 format
```

## Testing

### Compile and Simulate

```bash
cd thielecpu/hardware

# Compile μ-ALU testbench
iverilog -o mu_alu_tb mu_alu.v mu_alu_tb.v

# Run simulation
./mu_alu_tb

# Expected output:
# μ-ALU Test Bench
# ================
# Test 1: Addition 1.0 + 1.0
#   ✓ PASS
# Test 2: Subtraction 3.0 - 1.5
#   ✓ PASS
# Test 3: Multiplication 2.0 * 3.0
#   ✓ PASS
# Test 4: Division 6.0 / 2.0
#   ✓ PASS
# Test 5: Division by zero
#   ✓ PASS
```

### Integration Test

After integrating into thiele_cpu.v, compile and run the full testbench:

```bash
# Compile full CPU with μ-ALU
iverilog -o thiele_cpu_tb thiele_cpu.v mu_alu.v thiele_cpu_tb.v

# Run simulation
./thiele_cpu_tb
```

## Verification Against Python

Create a cross-validation test:

```python
# test_hardware_python_consistency.py
from thielecpu.mu_fixed import FixedPointMu
import subprocess

def run_verilog_test(before, after):
    """Run Verilog simulation and extract result."""
    # Generate testbench with specific inputs
    # Run iverilog
    # Parse output
    pass

def test_consistency():
    """Verify Python and Verilog produce identical results."""
    calc = FixedPointMu()
    
    test_cases = [
        (7, 5),   # Hash collision case
        (4, 1),   # Factoring case
        (100, 50),
        (21, 7),
    ]
    
    for before, after in test_cases:
        # Python result
        python_result = calc.information_gain_q16(before, after)
        
        # Verilog result
        verilog_result = run_verilog_test(before, after)
        
        # Compare
        assert python_result == verilog_result, \
            f"Mismatch: {before}->{after}: Python=0x{python_result:08X}, Verilog=0x{verilog_result:08X}"
        
    print("✅ All tests pass - Python and Verilog are bit-exact")
```

## Current Limitations

The current μ-ALU implementation has simplified LOG2 and INFO_GAIN operations. For full compatibility:

1. **LOG2 operation**: Needs complete implementation of:
   - Leading zero count (priority encoder)
   - Normalization to [1.0, 2.0) range
   - LUT lookup with proper indexing
   - Combine integer and fractional parts

2. **INFO_GAIN operation**: Currently computes ratio but doesn't call LOG2
   - Should pipeline: compute ratio → call LOG2 → return result

3. **Multi-cycle operations**: LOG2 and INFO_GAIN need proper state machine
   - Current implementation has placeholders
   - Full implementation requires 5-10 cycles per operation

## Next Steps

1. **Complete LOG2 implementation** in mu_alu.v
2. **Integrate μ-ALU** into thiele_cpu.v
3. **Add PDISCOVER opcode** and handler
4. **Update MDLACC** to use Q16.16 format
5. **Run verification suite** comparing Python vs Verilog
6. **Update synthesis reports** with new resource utilization

## Success Criteria

✅ **Phase 1 Complete** when:
- Python and Verilog produce identical μ-accumulator values (within 1 LSB)
- verify_alu_integrity.py passes on hardware simulation
- Long run test (1M operations) shows 0 LSB difference
- All test cases (7->5, 4->1, 11->1) produce correct results

## References

- Specification: `spec/mu_alu_v1.md`
- Python implementation: `thielecpu/mu_fixed.py`
- Test suite: `tests/test_mu_fixed.py`
- Verification script: `verify_alu_integrity.py`
