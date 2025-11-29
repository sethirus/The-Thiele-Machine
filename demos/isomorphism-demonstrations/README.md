# Isomorphism Demonstrations

This directory contains programs demonstrating the Thiele Machine's capabilities
across different complexity levels, from simple standard Python to intractable
solution spaces. Each program showcases how the Coq, Verilog, and Python VM
layers are isomorphic.

## Program Categories

### 1. SIMPLE - Standard Python Computation
- `demo_arithmetic.py` - Basic arithmetic operations
- `demo_strings.py` - String manipulation
- `demo_lists.py` - List operations and comprehensions

### 2. INTERMEDIATE - Partition Logic
- `demo_sudoku.py` - Constraint propagation with partitions
- `demo_graph_coloring.py` - Graph coloring using modules

### 3. ADVANCED - μ-Bit Accounting
- `demo_factorization.py` - Prime factorization with information cost
- `demo_sat_solving.py` - SAT solving with μ-ledger tracking

### 4. EXPERT - Intractable Spaces
- `demo_tseitin.py` - Exponential speedup on Tseitin formulas
- `demo_structured_random.py` - Structured vs random problem comparison

## Isomorphism Properties Demonstrated

1. **Opcode Alignment**: Python VM opcodes match Verilog RTL and Coq definitions
2. **μ-Formula Consistency**: μ-cost calculated identically across all layers
3. **Partition Semantics**: PNEW, PSPLIT, PMERGE work identically
4. **Receipt Format**: Step receipts can be verified by all implementations

## Running the Demonstrations

```bash
# Run all demonstrations
python3 -m pytest tests/test_isomorphism_complete.py -v

# Run specific demonstration
python3 demos/isomorphism-demonstrations/demo_arithmetic.py
```

## Verification

Each demonstration produces receipts that can be verified against:
- Coq proofs in `coq/thielemachine/coqproofs/`
- Verilog simulation in `thielecpu/hardware/`
- Python VM in `thielecpu/vm.py`
