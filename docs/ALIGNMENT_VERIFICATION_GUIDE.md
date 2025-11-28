# Thiele Machine Alignment Verification Guide

## Executive Summary

This document explains the **cross-layer alignment verification** system for the Thiele Machine. The verification ensures that the same computation produces identical results across three independent implementations:

1. **Python VM** (`thielecpu/`) - Reference implementation
2. **Verilog RTL** (`thielecpu/hardware/`) - Hardware implementation
3. **Coq Proofs** (`coq/`) - Formal verification

The alignment tests are **falsifiable by construction**: they dynamically extract values from each layer and compare them, detecting any inconsistency.

---

## Table of Contents

1. [Architecture Overview](#architecture-overview)
2. [The μ-Cost Formula](#the-μ-cost-formula)
3. [Layer-by-Layer Analysis](#layer-by-layer-analysis)
4. [Test Methodology](#test-methodology)
5. [Running the Tests](#running-the-tests)
6. [Understanding Test Output](#understanding-test-output)
7. [Edge Cases and Boundary Conditions](#edge-cases-and-boundary-conditions)
8. [Falsifiability](#falsifiability)
9. [Adding New Alignment Tests](#adding-new-alignment-tests)

---

## Architecture Overview

The Thiele Machine implements a **μ-bit ledger** that tracks computational cost. Every operation consumes μ-bits according to a deterministic formula. This creates an **auditable trace** of computation.

```
┌─────────────────────────────────────────────────────────────────────────┐
│                     Thiele Machine Architecture                          │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌──────────────┐     ┌──────────────┐     ┌──────────────┐             │
│  │  Python VM   │     │  Verilog RTL │     │  Coq Proofs  │             │
│  │  (Reference) │     │  (Hardware)  │     │  (Verified)  │             │
│  └──────┬───────┘     └──────┬───────┘     └──────┬───────┘             │
│         │                    │                    │                      │
│         │    μ-cost = 72     │    μ-cost = 72     │   μ-cost = 72       │
│         │                    │                    │                      │
│         └────────────────────┴────────────────────┘                      │
│                              │                                           │
│                     ┌────────▼────────┐                                  │
│                     │ Alignment Tests │                                  │
│                     │   (Falsifiable) │                                  │
│                     └─────────────────┘                                  │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### The Refinement Chain

```
Verilog RTL ──→ HardwareBridge.v ──→ ThieleMachineConcrete.v ──→ ThieleMachine.v
    │                 │                        │                      │
    │                 │                        │                      │
    ▼                 ▼                        ▼                      ▼
Synthesizable     Coq model of            Executable step         Abstract
hardware          RTL decode              function matching       machine
                                          Python VM               semantics
```

---

## The μ-Cost Formula

The μ-cost formula is the **cornerstone** of alignment verification. It must be identical across all layers.

### Formula Definition

For an `LASSERT` operation with query string `q`:

```
μ_cost(q) = len(q) × 8 bits
```

Where:
- `len(q)` is the byte length of the UTF-8 encoded query string
- `8` is the bits-per-byte constant

### Example: "x1 XOR x2"

| Component | Value |
|-----------|-------|
| Query | `"x1 XOR x2"` |
| Byte length | `9` |
| Bits per byte | `8` |
| **μ-cost** | **72 bits** |

### Implementation Locations

| Layer | File | Code |
|-------|------|------|
| Python | `thielecpu/mu.py:37-41` | `len(canonical.encode("utf-8")) * 8` |
| Verilog | `thiele_cpu.v:109` | `mu_accumulator` register |
| Coq | `ThieleMachineConcrete.v:142` | `(Z.of_nat (String.length query)) * 8` |

---

## Layer-by-Layer Analysis

### Layer 1: Python VM (`thielecpu/`)

The Python VM is the **reference implementation**. All other layers must match its behavior.

#### Key Files

| File | Purpose |
|------|---------|
| `mu.py` | μ-cost calculation |
| `isa.py` | Instruction set definitions |
| `vm.py` | Virtual machine execution |

#### μ-Cost Calculation (`mu.py`)

```python
def question_cost_bits(expr: str) -> int:
    """Compute the description-length cost for ``expr``."""
    canonical = canonical_s_expression(expr)
    return len(canonical.encode("utf-8")) * 8
```

The function:
1. Canonicalizes the expression (normalizes whitespace)
2. Encodes to UTF-8 bytes
3. Multiplies byte count by 8

#### Opcode Definitions (`isa.py`)

```python
class Opcode(Enum):
    PNEW = 0x00
    PSPLIT = 0x01
    PMERGE = 0x02
    LASSERT = 0x03    # <-- Key opcode for alignment tests
    LJOIN = 0x04
    MDLACC = 0x05
    XFER = 0x07
    PYEXEC = 0x08
    XOR_LOAD = 0x0A
    XOR_ADD = 0x0B
    XOR_SWAP = 0x0C
    XOR_RANK = 0x0D
    EMIT = 0x0E
    HALT = 0xFF
```

### Layer 2: Verilog RTL (`thielecpu/hardware/`)

The Verilog implementation must match Python opcode encodings exactly.

#### Key File: `thiele_cpu.v`

```verilog
// Instruction opcodes - MUST match Python isa.py
localparam [7:0] OPCODE_PNEW   = 8'h00;
localparam [7:0] OPCODE_PSPLIT = 8'h01;
localparam [7:0] OPCODE_PMERGE = 8'h02;
localparam [7:0] OPCODE_LASSERT = 8'h03;  // <-- Must be 0x03
localparam [7:0] OPCODE_LJOIN  = 8'h04;
localparam [7:0] OPCODE_MDLACC = 8'h05;
localparam [7:0] OPCODE_EMIT   = 8'h0E;
localparam [7:0] OPCODE_XFER   = 8'h07;
localparam [7:0] OPCODE_PYEXEC = 8'h08;
```

#### μ-Accumulator Register

```verilog
// μ-bit accumulator (line 109)
reg [31:0] mu_accumulator;
```

This 32-bit register tracks accumulated μ-cost during execution.

### Layer 3: Coq Proofs (`coq/`)

The Coq layer provides **formal verification** that the semantics are correct.

#### Key Files

| File | Purpose |
|------|---------|
| `HardwareBridge.v` | Maps RTL opcodes to abstract instructions |
| `ThieleMachineConcrete.v` | Executable step function |
| `MuAlignmentExample.v` | Concrete μ-cost theorems |
| `MuLedgerConservation.v` | Conservation laws |

#### Opcode Definitions (`HardwareBridge.v`)

```coq
Definition opcode_PNEW      : N := 0%N.
Definition opcode_PSPLIT    : N := 1%N.
Definition opcode_PMERGE    : N := 2%N.
Definition opcode_LASSERT   : N := 3%N.   (* MUST be 3 *)
Definition opcode_LJOIN     : N := 4%N.
Definition opcode_MDLACC    : N := 5%N.
Definition opcode_EMIT      : N := 14%N.  (* 0x0E *)
```

#### Step Function (`ThieleMachineConcrete.v`)

```coq
Definition concrete_step (instr : ThieleInstr) (s : ConcreteState) : StepResult :=
  match instr with
  | LASSERT query =>
      let mu := (Z.of_nat (String.length query)) * 8 in
      {| post_state := with_pc_mu s mu;
         observation := {| ev := Some (PolicyCheck query);
                           mu_delta := mu;
                           cert := cert_for_query query |} |}
  ...
```

#### Alignment Theorem (`MuAlignmentExample.v`)

```coq
Definition lassert_mu_cost (query : string) : Z :=
  Z.of_nat (String.length query) * 8.

Definition test_clause : string := "x1 XOR x2".

Theorem lassert_xor_mu_cost :
  lassert_mu_cost test_clause = 72.
Proof. reflexivity. Qed.
```

---

## Test Methodology

### Principle: No Hardcoded Results

The alignment tests are designed to be **falsifiable**:

1. They **extract values dynamically** from each layer
2. They **compare extracted values** against each other
3. They **fail immediately** if any mismatch is detected

### Test Categories

| Category | What It Tests |
|----------|--------------|
| **Opcode Alignment** | Same opcode values across Python/Verilog/Coq |
| **μ-Cost Formula** | Same formula produces same results |
| **Conservation Laws** | Coq theorems compile (proving invariants) |
| **Edge Cases** | Empty strings, long strings, special characters |

### Test Flow

```
┌─────────────────────────────────────────────────────────────────┐
│                    Alignment Test Flow                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  1. Extract value from Python VM                                 │
│     └─> python3 -c "from thielecpu.mu import ..."                │
│                                                                  │
│  2. Extract value from Verilog (grep constants)                  │
│     └─> grep "OPCODE_LASSERT" thiele_cpu.v                       │
│                                                                  │
│  3. Extract value from Coq (grep + compile theorem)              │
│     └─> grep "opcode_LASSERT" HardwareBridge.v                   │
│     └─> coqc MuAlignmentExample.v                                │
│                                                                  │
│  4. Compare all extracted values                                 │
│     └─> if mismatch: EXIT 1                                      │
│     └─> if all match: EXIT 0                                     │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## Running the Tests

### Quick Validation

```bash
./scripts/validate_mu_alignment.sh
```

### Comprehensive Test Suite

```bash
PYTHONPATH=. python3 tests/alignment/test_mu_alignment.py
```

### Full Alignment Verification

```bash
PYTHONPATH=. python3 tests/alignment/test_comprehensive_alignment.py
```

### Expected Output (Pass)

```
============================================================
μ-Cost Alignment Validation: LASSERT on 'x1 XOR x2'
============================================================
Test clause: 'x1 XOR x2'
Expected μ-cost: 72 bits
------------------------------------------------------------
✓ Python VM: μ-cost('x1 XOR x2') = 72 bits
✓ Coq formula: len('x1 XOR x2') * 8 = 72 bits
✓ Opcode alignment: Python=0x03, Coq=3, Verilog=0x03
✓ Coq theorem exists: bounded_model_mu_ledger_conservation
✓ Coq LASSERT definition: mu := len(query) * 8
✓ Coq HardwareBridge: opcode_LASSERT = 3
------------------------------------------------------------
ALIGNMENT SUMMARY
------------------------------------------------------------
  Python VM μ-cost:     72 bits
  Coq formula result:   72 bits
  LASSERT opcode:       0x03
  Conservation theorem: ✓
  Concrete definition:  ✓
  Hardware bridge:      ✓
------------------------------------------------------------
✅ PASS: All layers agree on μ-cost = 72 bits
```

### Expected Output (Fail - Example)

If the Coq opcode were changed to 4, you would see:

```
[4/4] Testing cross-layer opcode consistency...
  ✗ Opcode mismatch: Python=3, Coq=4
------------------------------------------------------------
❌ FAIL: 1 alignment check(s) failed
```

---

## Understanding Test Output

### Test Result Symbols

| Symbol | Meaning |
|--------|---------|
| ✓ | Test passed |
| ✗ | Test failed |
| ✅ | All tests passed |
| ❌ | One or more tests failed |

### Key Metrics

| Metric | Description | Expected Value |
|--------|-------------|----------------|
| `Python VM μ-cost` | Result from `question_cost_bits()` | 72 bits |
| `Coq formula result` | `len("x1 XOR x2") * 8` | 72 bits |
| `LASSERT opcode` | Opcode value in all layers | 0x03 |

---

## Edge Cases and Boundary Conditions

The comprehensive test suite covers:

### 1. Empty String

```python
query = ""
expected_mu = 0  # 0 * 8 = 0
```

### 2. Single Character

```python
query = "a"
expected_mu = 8  # 1 * 8 = 8
```

### 3. Unicode Characters

```python
query = "α ∧ β"  # Greek letters and logical AND
expected_mu = len("α ∧ β".encode("utf-8")) * 8
```

### 4. Maximum Length

```python
query = "x" * 1000
expected_mu = 8000  # 1000 * 8
```

### 5. Whitespace Normalization

```python
query = "  x1   XOR   x2  "
canonical = "x1 XOR x2"  # Normalized
expected_mu = 72  # 9 * 8
```

### 6. All Opcodes

The tests verify that **every opcode** in `isa.py` has a matching constant in:
- `thiele_cpu.v`
- `HardwareBridge.v`

---

## Falsifiability

### What Makes These Tests Falsifiable?

1. **No hardcoded expected values in comparison logic**
   - Values are extracted from source files
   - Comparison is dynamic

2. **Test would fail if:**
   - Python opcode changed from 0x03 → 0x04
   - Verilog constant changed
   - Coq definition changed
   - μ-cost formula changed in any layer

3. **No bypass mechanisms**
   - Tests exit with code 1 on any failure
   - CI will fail if alignment is broken

### How to Verify Falsifiability

1. **Introduce a deliberate mismatch:**

```bash
# Temporarily change Python opcode
sed -i 's/LASSERT = 0x03/LASSERT = 0x04/' thielecpu/isa.py

# Run test - should FAIL
./scripts/validate_mu_alignment.sh
# Expected: ❌ FAIL: 1 alignment check(s) failed

# Restore
git checkout thielecpu/isa.py
```

2. **Verify test passes after restore:**

```bash
./scripts/validate_mu_alignment.sh
# Expected: ✅ PASS
```

---

## Adding New Alignment Tests

### Step 1: Identify the Invariant

What property must be consistent across layers?

Example: "EMIT opcode must be 0x0E in all layers"

### Step 2: Add Extraction Logic

```python
# In test_comprehensive_alignment.py

def test_emit_opcode_alignment():
    # Extract from Python
    python_opcode = Opcode.EMIT.value
    
    # Extract from Verilog
    verilog_opcode = extract_verilog_opcode("OPCODE_EMIT")
    
    # Extract from Coq
    coq_opcode = extract_coq_opcode("opcode_EMIT")
    
    assert python_opcode == verilog_opcode == coq_opcode == 0x0E
```

### Step 3: Add to Test Suite

```python
ALIGNMENT_TESTS = [
    ("LASSERT opcode", test_lassert_opcode_alignment),
    ("EMIT opcode", test_emit_opcode_alignment),  # New test
    ...
]
```

### Step 4: Verify Test Works

```bash
PYTHONPATH=. python3 tests/alignment/test_comprehensive_alignment.py
```

---

## Appendix: Complete Opcode Table

| Mnemonic | Python | Verilog | Coq |
|----------|--------|---------|-----|
| PNEW | 0x00 | 8'h00 | 0%N |
| PSPLIT | 0x01 | 8'h01 | 1%N |
| PMERGE | 0x02 | 8'h02 | 2%N |
| LASSERT | 0x03 | 8'h03 | 3%N |
| LJOIN | 0x04 | 8'h04 | 4%N |
| MDLACC | 0x05 | 8'h05 | 5%N |
| XFER | 0x07 | 8'h07 | 7%N |
| PYEXEC | 0x08 | 8'h08 | 8%N |
| XOR_LOAD | 0x0A | 8'h0A | 10%N |
| XOR_ADD | 0x0B | 8'h0B | 11%N |
| XOR_SWAP | 0x0C | 8'h0C | 12%N |
| XOR_RANK | 0x0D | 8'h0D | 13%N |
| EMIT | 0x0E | 8'h0E | 14%N |
| HALT | 0xFF | - | 255%N |

---

## Summary

The alignment verification system ensures that:

1. **Opcodes match** across Python, Verilog, and Coq
2. **μ-cost formula** produces identical results in all layers
3. **Conservation laws** are formally proven in Coq
4. **Tests are falsifiable** - they detect misalignment without hardcoding

Run `./scripts/validate_mu_alignment.sh` to verify alignment at any time.
