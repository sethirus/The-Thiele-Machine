# Thiele Machine Three-Layer Architecture

## Overview

The Thiele Machine implements a **three-layer verification architecture** where each layer provides different guarantees while maintaining **isomorphic behavior** with respect to μ-cost (information-theoretic cost).

```
┌─────────────────────────────────────────────────────────────┐
│                     Layer 1: Coq Proofs                      │
│  Formal Verification (45,284 lines of mechanized proofs)     │
│  - Kernel semantics                                          │
│  - Subsumption: TURING ⊊ THIELE                             │
│  - Bell inequality S=16/5                                    │
│  - μ-ledger conservation                                     │
└──────────────────────┬──────────────────────────────────────┘
                       │ Extraction (partially manual)
                       ▼
┌─────────────────────────────────────────────────────────────┐
│                  Layer 2: Verilog RTL                        │
│  Hardware Description (synthesizable to FPGA/ASIC)           │
│  - μ-ALU (arithmetic with μ-cost tracking)                   │
│  - Partition discovery units                                │
│  - Memory management unit (MMU)                              │
│  - Logic execution engine (LEI)                              │
└──────────────────────┬──────────────────────────────────────┘
                       │ Behavioral equivalence
                       ▼
┌─────────────────────────────────────────────────────────────┐
│                   Layer 3: Python VM                         │
│  Software Implementation (~3,000 lines, 1,107 tests)         │
│  - Instruction execution                                     │
│  - Partition operations                                      │
│  - Symbolic execution                                        │
│  - μ-ledger accounting                                       │
└─────────────────────────────────────────────────────────────┘
```

## The μ-Cost Invariant

All three layers must preserve the **μ-cost conservation law**:

```
∀ operation op, ∀ state s:
  μ_cost(op, s) = -log₂(Pr[reverse op from result state])
```

This ensures that:
1. **Reversible operations** (e.g., XOR) have μ-cost = 0
2. **Irreversible operations** (e.g., erasure) have μ-cost > 0
3. **Total μ-cost is monotonically non-decreasing**

## Layer 1: Coq Formal Proofs

### Location
- `coq/kernel/` - Core kernel proofs
- `coq/thielemachine/coqproofs/` - Machine-specific proofs
- `coq/modular_proofs/` - Modular proof structure

### Key Theorems

#### Subsumption (kernel/Subsumption.v)
```coq
Theorem thiele_subsumes_turing :
  forall (M : TuringMachine),
    exists (T : ThieleMachine),
      behaviorally_equivalent M T.
```

#### μ-Ledger Conservation (kernel/MuLedgerConservation.v)
```coq
Theorem vm_step_respects_mu_ledger :
  forall state state',
    vm_step state = state' ->
    mu_ledger state' >= mu_ledger state.
```

#### Bell Inequality (thielemachine/coqproofs/BellInequality.v)
```coq
Theorem bell_s_equals_16_5 :
  let dist := geometric_no_signaling_distribution in
  CHSH_value dist = 16/5.
```

### Build Commands
```bash
# Build core kernel proofs
make -C coq core

# Build specific proof
make -C coq kernel/Subsumption.vo

# Build with timing
make -C coq TIMED=1 core
```

### Current Status
- ✅ Kernel proofs compile (8 files, ~5K lines)
- ✅ Subsumption proven
- ✅ Bell inequality proven
- ⚠️ Some bridge proofs use checkpoints (for performance)
- ⚠️ Minor admits tracked in ADMIT_REPORT.txt

## Layer 2: Verilog RTL

### Location
- `thielecpu/hardware/` - All RTL modules
- `scripts/synth_*.ys` - Yosys synthesis scripts

### Key Modules

#### μ-ALU (mu_alu.v)
Arithmetic Logic Unit with μ-cost tracking
- **Inputs**: 32-bit operands, operation code
- **Outputs**: 32-bit result, μ-cost value, flags
- **Operations**: ADD, SUB, MUL, DIV, INFO_GAIN
- **Size**: 777 cells, 1499 wires (after synthesis)
- **Status**: ✅ Synthesized and simulated

#### μ-Core (mu_core.v)
Main execution core
- Instruction fetch/decode/execute
- Register file (32 registers)
- μ-ledger tracking
- **Status**: ⏳ Needs synthesis test

#### Partition Discovery (partition_discovery/)
Hardware accelerators for partition operations
- Geometric oracle implementation
- CHSH inequality computation
- **Status**: ⏳ Needs integration

### Synthesis Flow

```bash
# Synthesize μ-ALU
yosys -s scripts/synth_mu_alu.ys

# Simulate μ-ALU testbench
cd thielecpu/hardware
iverilog -o mu_alu_test mu_alu.v mu_alu_tb.v
./mu_alu_test
# View waveforms in mu_alu_tb.vcd
```

### Current Status
- ✅ μ-ALU synthesized (777 cells)
- ✅ μ-ALU testbench passing (6/6 tests)
- ⏳ Full CPU synthesis pending (SystemVerilog compatibility)
- ⏳ FPGA resource utilization report needed

## Layer 3: Python VM

### Location
- `thielecpu/vm.py` - Main VM implementation
- `thielecpu/primitives.py` - Core primitives
- `thielecpu/discovery.py` - Partition discovery
- `tests/` - Test suite (1,107 tests)

### Key Classes

#### VM (vm.py)
Main virtual machine executor
```python
class VM:
    def execute_python(self, code_or_path: str) -> Any
    def pdiscover(self, module_id, axioms, cert_dir, ...) -> Dict
    def _simulate_witness_step(self, ...) -> Dict
```

#### MuLedger (mu.py)
μ-cost tracking
```python
def step(self, logical_step: int) -> Dict[int, float]:
    """Track μ-cost for each operation"""
```

### Test Suite
```bash
# Run all tests
pytest tests/

# Run specific test
pytest tests/test_vm.py -v

# Run with coverage
pytest --cov=thielecpu tests/
```

### Current Status
- ✅ VM imports successfully
- ✅ 1,107 tests passing
- ⏳ μ-cost tracker needs validation against RTL
- ⏳ Partition discovery needs RTL comparison

## Cross-Layer Validation

### VM ↔ RTL Equivalence

The key challenge is proving that VM and RTL implementations produce **equivalent μ-cost values** for the same operations.

#### Validation Script
```bash
python scripts/test_vm_rtl_equivalence.py
```

#### Test Cases Needed
1. **Arithmetic operations** - ADD, SUB, MUL, DIV
2. **Partition operations** - PNEW, PSPLIT, PMERGE
3. **Logical operations** - LASSERT, LJOIN
4. **Discovery operations** - PDISCOVER
5. **Complete programs** - End-to-end execution

#### Current Status
- ✅ Basic equivalence test framework created
- ✅ μ-ALU addition/overflow tests passing
- ⏳ Comprehensive test suite needed
- ⏳ Automated RTL result parsing needed

### Coq → Verilog Extraction

Two approaches are possible:

#### Approach 1: Direct Extraction (Preferred)
Extract Coq definitions to OCaml/Haskell, then convert to Verilog
- ✅ Preserves formal guarantees
- ❌ Complex toolchain
- ⏳ Status unknown - needs investigation

#### Approach 2: Manual Implementation (Current)
Hand-write Verilog to match Coq specification
- ✅ Optimized for hardware
- ❌ Manual proof of equivalence required
- ✅ Currently used for μ-ALU

### Equivalence Proof Strategy

```
Coq Spec (S)  ─────matches────→  Verilog RTL (V)
     │                                  │
     │                                  │
   extract                           simulate
     │                                  │
     ▼                                  ▼
Python Model (P) ───equivalent───→  RTL Behavior (B)

Prove: ∀ input i, S(i) = V(i) = P(i) = B(i) (w.r.t. μ-cost)
```

## Integration Workflow

### Step 1: Verify Coq Proofs
```bash
make -C coq core
# Ensure all kernel proofs compile
```

### Step 2: Synthesize RTL
```bash
yosys -s scripts/synth_mu_alu.ys
# Check synthesis reports
```

### Step 3: Simulate RTL
```bash
cd thielecpu/hardware
iverilog -o test mu_alu.v mu_alu_tb.v
./test
```

### Step 4: Run VM Tests
```bash
pytest tests/
# Ensure all VM tests pass
```

### Step 5: Cross-Validate
```bash
python scripts/test_vm_rtl_equivalence.py
# Compare VM and RTL results
```

## Development Guidelines

### When Modifying Layer 1 (Coq)
1. Update affected proofs
2. Rebuild with `make -C coq core`
3. Update ADMIT_REPORT.txt if admits change
4. Consider impact on Verilog extraction

### When Modifying Layer 2 (Verilog)
1. Update synthesis scripts
2. Re-synthesize affected modules
3. Run testbenches
4. Update resource utilization reports
5. Verify VM equivalence still holds

### When Modifying Layer 3 (VM)
1. Update tests
2. Run full test suite
3. Update μ-cost tracking if needed
4. Verify RTL equivalence still holds
5. Update receipts/certificates if needed

## Future Work

### Short Term
- [ ] Complete full CPU RTL synthesis
- [ ] Implement automated RTL result parsing
- [ ] Create comprehensive VM-RTL test suite
- [ ] Document Coq extraction mechanism

### Medium Term
- [ ] Automate Coq → Verilog extraction
- [ ] FPGA implementation and testing
- [ ] Hardware acceleration benchmarks
- [ ] Formal equivalence proof (Coq ↔ RTL)

### Long Term
- [ ] ASIC tape-out
- [ ] Quantum-resistant algorithm testing
- [ ] Large-scale partition discovery experiments
- [ ] Academic publication

## References

- **Coq Documentation**: `coq/README.md`
- **Verilog Guide**: `thielecpu/hardware/README.md`
- **VM Guide**: `thielecpu/README.md`
- **Test Suite**: `tests/README.md`
- **Milestones**: `MILESTONES.md`
- **TODO List**: `TODO.md`

---

**Last Updated**: 2025-12-11  
**Status**: Phase 4 - VM-RTL Alignment  
**Next**: Complete cross-layer validation
