// Test bench for μ-ALU module
// Verifies Q16.16 fixed-point arithmetic operations

`timescale 1ns / 1ps

module mu_alu_tb;

reg clk;
reg rst_n;
reg [2:0] op;
reg [31:0] operand_a;
reg [31:0] operand_b;
reg valid;

wire [31:0] result;
wire ready;
wire overflow;

// Instantiate the μ-ALU
mu_alu uut (
    .clk(clk),
    .rst_n(rst_n),
    .op(op),
    .operand_a(operand_a),
    .operand_b(operand_b),
    .valid(valid),
    .result(result),
    .ready(ready),
    .overflow(overflow)
);

// Clock generation
initial begin
    clk = 0;
    forever #5 clk = ~clk;
end

// Test vectors
initial begin
    $display("μ-ALU Test Bench");
    $display("================");
    
    // Initialize
    rst_n = 0;
    op = 0;
    operand_a = 0;
    operand_b = 0;
    valid = 0;
    
    #20 rst_n = 1;
    #10;
    
    // Test 1: Addition - 1.0 + 1.0 = 2.0
    $display("\nTest 1: Addition 1.0 + 1.0");
    op = 3'd0;  // OP_ADD
    operand_a = 32'h00010000;  // 1.0
    operand_b = 32'h00010000;  // 1.0
    valid = 1;
    #10 valid = 0;
    wait(ready);
    $display("  Expected: 0x00020000 (2.0)");
    $display("  Got:      0x%08h", result);
    if (result == 32'h00020000 && !overflow)
        $display("  ✓ PASS");
    else
        $display("  ✗ FAIL");
    #10;
    
    // Test 2: Subtraction - 3.0 - 1.5 = 1.5
    $display("\nTest 2: Subtraction 3.0 - 1.5");
    op = 3'd1;  // OP_SUB
    operand_a = 32'h00030000;  // 3.0
    operand_b = 32'h00018000;  // 1.5
    valid = 1;
    #10 valid = 0;
    wait(ready);
    $display("  Expected: 0x00018000 (1.5)");
    $display("  Got:      0x%08h", result);
    if (result == 32'h00018000 && !overflow)
        $display("  ✓ PASS");
    else
        $display("  ✗ FAIL");
    #10;
    
    // Test 3: Multiplication - 2.0 * 3.0 = 6.0
    $display("\nTest 3: Multiplication 2.0 * 3.0");
    op = 3'd2;  // OP_MUL
    operand_a = 32'h00020000;  // 2.0
    operand_b = 32'h00030000;  // 3.0
    valid = 1;
    #10 valid = 0;
    wait(ready);
    $display("  Expected: 0x00060000 (6.0)");
    $display("  Got:      0x%08h", result);
    if (result == 32'h00060000 && !overflow)
        $display("  ✓ PASS");
    else
        $display("  ✗ FAIL");
    #10;
    
    // Test 4: Division - 6.0 / 2.0 = 3.0
    $display("\nTest 4: Division 6.0 / 2.0");
    op = 3'd3;  // OP_DIV
    operand_a = 32'h00060000;  // 6.0
    operand_b = 32'h00020000;  // 2.0
    valid = 1;
    #10 valid = 0;
    wait(ready);
    $display("  Expected: 0x00030000 (3.0)");
    $display("  Got:      0x%08h", result);
    if (result == 32'h00030000 && !overflow)
        $display("  ✓ PASS");
    else
        $display("  ✗ FAIL");
    #10;
    
    // Test 5: Division by zero
    $display("\nTest 5: Division by zero");
    op = 3'd3;  // OP_DIV
    operand_a = 32'h00010000;  // 1.0
    operand_b = 32'h00000000;  // 0.0
    valid = 1;
    #10 valid = 0;
    wait(ready);
    $display("  Expected: overflow flag set");
    $display("  Got:      overflow=%b", overflow);
    if (overflow)
        $display("  ✓ PASS");
    else
        $display("  ✗ FAIL");
    #10;
    
    // Test 6: Information gain - 4 -> 1 should be log2(4) = 2.0
    $display("\nTest 6: Information Gain 4 -> 1");
    op = 3'd5;  // OP_INFO_GAIN
    operand_a = 32'd4;  // before = 4 (integer)
    operand_b = 32'd1;  // after = 1 (integer)
    valid = 1;
    #10 valid = 0;
    wait(ready);
    $display("  Expected: ~0x00020000 (2.0 bits)");
    $display("  Got:      0x%08h", result);
    // Note: This is a placeholder test - full implementation needed
    #10;
    
    $display("\n================");
    $display("Tests Complete");
    $display("================");
    $finish;
end

// Timeout
initial begin
    #10000;
    $display("ERROR: Testbench timeout");
    $finish;
end

endmodule
