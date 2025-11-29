# Isomorphism Validation: Coq, Verilog, and Python VM

This document describes the isomorphism between the three implementations of the
Thiele Machine and how to validate it.

## Overview

The Thiele Machine is implemented in three isomorphic layers:

1. **Coq** - Formal proofs and semantics (`coq/thielemachine/coqproofs/`)
2. **Verilog RTL** - Hardware implementation (`thielecpu/hardware/`)
3. **Python VM** - Reference implementation (`thielecpu/vm.py`)

All three implementations produce **identical results** for the same inputs.

## Isomorphism Properties

### 1. Opcode Alignment

Every opcode is defined identically across all layers:

| Opcode | Python (isa.py) | Verilog (thiele_cpu.v) | Coq (HardwareBridge.v) |
|--------|-----------------|------------------------|------------------------|
| PNEW   | 0x00            | 8'h00                  | 0%N                    |
| PSPLIT | 0x01            | 8'h01                  | 1%N                    |
| PMERGE | 0x02            | 8'h02                  | 2%N                    |
| LASSERT| 0x03            | 8'h03                  | 3%N                    |
| LJOIN  | 0x04            | 8'h04                  | 4%N                    |
| MDLACC | 0x05            | 8'h05                  | 5%N                    |
| EMIT   | 0x0E            | 8'h0E                  | 14%N                   |
| PYEXEC | 0x08            | 8'h08                  | 8%N                    |
| XOR_ADD| 0x0B            | 8'h0B                  | 11%N                   |
| HALT   | 0xFF            | 8'hFF                  | 255%N                  |

### 2. μ-Cost Formula

The μ-cost formula is identical across all implementations:

```
μ_total(q, N, M) = 8 × |canon(q)| + log₂(N/M)
```

Where:
- `q` = Question being asked
- `canon(q)` = Canonical S-expression form
- `N` = Possibilities before step
- `M` = Possibilities after step

### 3. Partition Semantics

Partition operations (PNEW, PSPLIT, PMERGE) behave identically:
- PNEW creates a new module from a region
- PSPLIT divides a module by a predicate
- PMERGE combines two modules

## Validation Tests

### Python VM Tests
```bash
pytest tests/test_vm.py -v
pytest tests/test_isomorphism_complete.py -v
```

### Verilog RTL Tests
```bash
cd thielecpu/hardware
iverilog -g2012 -o thiele_cpu_test thiele_cpu.v thiele_cpu_tb.v
vvp thiele_cpu_test
```

### Coq Proof Compilation
```bash
cd coq
coqc -Q thielemachine/coqproofs ThieleMachine thielemachine/coqproofs/ThieleMachine.v
coqc -Q thielemachine/coqproofs ThieleMachine thielemachine/coqproofs/HardwareBridge.v
```

### Cross-Layer Alignment Tests
```bash
pytest tests/alignment/test_comprehensive_alignment.py -v
pytest tests/test_hardware_alignment.py -v
```

## Standard Program Isomorphism

The `demos/standard_programs/` directory contains normal programs that run
in both standard Python and the Thiele VM, demonstrating:

1. **Identical Results** - Same algorithm produces same output
2. **Same Operation Count** - Same number of comparisons, iterations, etc.
3. **Additional Tracking** - Thiele VM adds μ-cost tracking

### Example: Sorting Algorithms

```python
# Standard Python
result_std = bubble_sort([5, 2, 8, 1, 9])
# Result: [1, 2, 5, 8, 9], comparisons: 10

# Thiele VM
result_vm = run_in_thiele_vm(bubble_sort, [5, 2, 8, 1, 9])
# Result: [1, 2, 5, 8, 9], comparisons: 10, μ-cost: 141 bits
```

The results are identical, but the Thiele VM tracks information-theoretic cost.

## Key Theorems (Coq Proofs)

1. **thiele_simulates_turing** - Every Turing computation can be performed
2. **turing_is_strictly_contained** - Thiele has capabilities Turing lacks
3. **mu_ledger_conservation** - μ-bits are conserved
4. **hardware_bridge_correct** - RTL matches Coq semantics

## Running Full Validation

```bash
# Run all isomorphism tests
python3 -m pytest tests/test_isomorphism_complete.py -v

# Run all alignment tests
python3 -m pytest tests/alignment/ -v

# Run standard program tests
python3 -m pytest tests/test_standard_programs_isomorphism.py -v

# Run Verilog simulation
cd thielecpu/hardware && iverilog -g2012 -o test thiele_cpu.v thiele_cpu_tb.v && vvp test
```

## Separation: What Thiele Adds

| Feature | Standard Python | Thiele VM |
|---------|-----------------|-----------|
| Computation | ✓ | ✓ |
| Results | ✓ | ✓ (identical) |
| μ-cost tracking | ✗ | ✓ |
| Partition logic | ✗ | ✓ |
| Information accounting | ✗ | ✓ |
| Structure exploitation | ✗ | ✓ |

The Thiele VM is a strict superset - it can do everything Python can do,
plus it tracks information-theoretic costs and enables structure exploitation.
