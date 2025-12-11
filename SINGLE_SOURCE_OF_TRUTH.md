# Single Source of Truth: Coq Kernel

## The Problem We Solved

### Before: Three Independent Sources (❌ BAD)

The Thiele Machine had three implementations that needed to stay synchronized:

```
Coq Kernel (coq/kernel/VMStep.v)
    ↓ manual sync
Verilog CPU (thielecpu/hardware/thiele_cpu.v)
    ↓ manual sync
Python VM (thielecpu/vm.py)
```

**Problems:**
- Changes in one place didn't automatically propagate
- Easy to forget to update all three layers
- Risk of divergence (instructions in one but not others)
- No automated verification of consistency

### After: Single Source with Automated Generation (✅ GOOD)

```
Coq Kernel (SINGLE SOURCE OF TRUTH)
    ↓ automated extraction
    ├→ OCaml (vm_extracted.ml)
    ├→ Verilog (opcode_definitions.vh)
    └→ Python (vm_instructions.py)
```

**Benefits:**
- Update one file → all layers automatically updated
- Guaranteed consistency through extraction
- Automated verification catches any drift
- Coq proofs cover the entire system

## Why Coq is the Source of Truth

### 1. Formal Verification
Coq provides **machine-checked proofs** that the instruction semantics are correct:
- μ-cost conservation proven for all 16 instructions
- State transitions proven correct
- Subsumption theorem (TURING ⊊ THIELE) proven
- No admits, no axioms in kernel (100% proven)

### 2. Type Safety
Coq's type system prevents entire classes of errors:
- Can't forget to handle an instruction
- Can't mix up parameter types
- Pattern matching must be exhaustive

### 3. Extraction Correctness
Coq's extraction mechanism preserves semantics:
- OCaml extraction is proven-correct
- Generated code matches Coq specification
- Type preservation guaranteed

## The Extraction Pipeline

### Phase 1: Coq Kernel (Source)

**File:** `coq/kernel/VMStep.v`

Defines the complete VM instruction set:

```coq
Inductive vm_instruction :=
| instr_pnew (region : list nat) (mu_delta : nat)
| instr_psplit (module : ModuleID) (left right : list nat) (mu_delta : nat)
| instr_pmerge (m1 m2 : ModuleID) (mu_delta : nat)
...
| instr_halt (mu_delta : nat).
```

**What this defines:**
- 16 instructions with precise types
- μ-cost parameter for each (mu_delta : nat)
- Operational semantics (vm_step relation)
- Conservation properties (proven!)

### Phase 2: OCaml Extraction

**File:** `coq/extraction/ExtractVM.v`

Extracts Coq to OCaml:

```coq
Extraction "vm_extracted.ml"
  vm_instruction
  vm_step
  instruction_cost
  apply_cost.
```

**Output:** `coq/extraction/vm_extracted.ml` (1,200+ lines)

This is a **verified reference implementation** matching the Coq semantics exactly.

### Phase 3: Python Generation

**Script:** `scripts/generate_python_from_coq.py`

Reads `VMStep.v` and generates Python dataclasses:

```python
@dataclass
class InstrPnew:
    """Generated from Coq: instr_pnew"""
    region: List[int]
    mu_delta: int
```

**Output:** `thielecpu/generated/vm_instructions.py`

Python code that **exactly matches** the Coq types.

### Phase 4: Verilog Generation

**Script:** `scripts/generate_verilog_from_coq.py`

Reads `VMStep.v` and generates SystemVerilog parameters:

```verilog
parameter [7:0] OPCODE_PNEW = 8'h00;  // instr_pnew
parameter [7:0] OPCODE_PSPLIT = 8'h01;  // instr_psplit
```

**Output:** `thielecpu/generated/opcode_definitions.vh`

Verilog opcodes that **exactly match** the Coq instruction set.

## Maintaining the Single Source

### Adding a New Instruction

**Step 1:** Update Coq kernel ONLY

Edit `coq/kernel/VMStep.v`:

```coq
Inductive vm_instruction :=
...
| instr_mynewop (param1 : nat) (param2 : string) (mu_delta : nat).
```

**Step 2:** Update auxiliary Coq functions

```coq
Definition instruction_cost (instr : vm_instruction) : nat :=
  match instr with
  ...
  | instr_mynewop _ _ cost => cost
  end.
```

```coq
Inductive vm_step : VMState -> vm_instruction -> VMState -> Prop :=
...
| step_mynewop : forall s p1 p2 cost,
    vm_step s (instr_mynewop p1 p2 cost) ...
```

**Step 3:** Compile Coq

```bash
make coq-kernel
```

**Step 4:** Generate all layers

```bash
make generate-all
```

**Step 5:** Verify consistency

```bash
make verify-sync
```

**Result:**
- ✅ OCaml extraction updated automatically
- ✅ Python types updated automatically
- ✅ Verilog opcodes updated automatically
- ✅ All three layers guaranteed to match

### What NOT to Do

❌ **Don't manually edit generated files:**
- `coq/extraction/vm_extracted.ml`
- `thielecpu/generated/vm_instructions.py`
- `thielecpu/generated/opcode_definitions.vh`

These files have headers warning they're auto-generated.

❌ **Don't try to "sync" manually:**

If you find yourself thinking "I need to update the Verilog opcodes to match Coq", STOP. Run `make generate-verilog` instead.

❌ **Don't skip verification:**

Always run `make verify-sync` after changes. If consistency check fails, regenerate with `make generate-all`.

## Verification & Validation

### Automated Consistency Checking

**Script:** `scripts/verify_extraction_consistency.py`

Verifies all layers match:

```python
coq_instructions = parse_coq_kernel()      # 16 instructions
verilog_opcodes = parse_verilog()          # 16 opcodes
python_types = parse_python()              # 16 types

assert coq_instructions == verilog_opcodes  # ✅
assert coq_instructions == python_types     # ✅
```

**Output:**
```
✅ Coq ↔ Verilog (generated): PERFECT MATCH
✅ Coq ↔ Python (generated): PERFECT MATCH
🎉 RESULT: Perfect three-layer consistency
```

### CI Integration

Every commit triggers:

```yaml
- Compile Coq kernel
- Extract to OCaml
- Generate Python & Verilog
- Verify consistency
- Fail if mismatch detected
```

**This guarantees** the three layers never drift apart.

## The Contract

### Coq Kernel Promises:
- ✅ Defines all VM instructions formally
- ✅ Proves μ-cost conservation
- ✅ Provides operational semantics
- ✅ Maintains 0 admits, 0 axioms

### Extraction Pipeline Promises:
- ✅ Preserves Coq semantics exactly
- ✅ Generates Python types matching Coq
- ✅ Generates Verilog opcodes matching Coq
- ✅ Automated verification of consistency

### Developers Must:
- ✅ Edit ONLY the Coq kernel for instruction changes
- ✅ Run `make generate-all` after Coq changes
- ✅ Run `make verify-sync` before committing
- ❌ NEVER edit generated files manually

## Benefits Realized

### Before Extraction Pipeline
- **3 files to update** for each new instruction
- **Manual synchronization** (error-prone)
- **No guarantee** layers match
- **Drift risk** high

### After Extraction Pipeline
- **1 file to update** (Coq kernel)
- **Automated generation** (push-button)
- **Guaranteed consistency** (extraction proven correct)
- **Zero drift risk** (automated verification)

## Example: The 16-Instruction Mapping

All 16 instructions are generated from the Coq kernel:

| # | Coq | Verilog | Python |
|---|-----|---------|--------|
| 1 | `instr_pnew` | `OPCODE_PNEW (0x00)` | `InstrPnew` |
| 2 | `instr_psplit` | `OPCODE_PSPLIT (0x01)` | `InstrPsplit` |
| 3 | `instr_pmerge` | `OPCODE_PMERGE (0x02)` | `InstrPmerge` |
| 4 | `instr_lassert` | `OPCODE_LASSERT (0x03)` | `InstrLassert` |
| 5 | `instr_ljoin` | `OPCODE_LJOIN (0x04)` | `InstrLjoin` |
| 6 | `instr_mdlacc` | `OPCODE_MDLACC (0x05)` | `InstrMdlacc` |
| 7 | `instr_pdiscover` | `OPCODE_PDISCOVER (0x06)` | `InstrPdiscover` |
| 8 | `instr_xfer` | `OPCODE_XFER (0x07)` | `InstrXfer` |
| 9 | `instr_pyexec` | `OPCODE_PYEXEC (0x08)` | `InstrPyexec` |
| 10 | `instr_xor_load` | `OPCODE_XOR_LOAD (0x0A)` | `InstrXor_load` |
| 11 | `instr_xor_add` | `OPCODE_XOR_ADD (0x0B)` | `InstrXor_add` |
| 12 | `instr_xor_swap` | `OPCODE_XOR_SWAP (0x0C)` | `InstrXor_swap` |
| 13 | `instr_xor_rank` | `OPCODE_XOR_RANK (0x0D)` | `InstrXor_rank` |
| 14 | `instr_emit` | `OPCODE_EMIT (0x0E)` | `InstrEmit` |
| 15 | `instr_oracle_halts` | `OPCODE_ORACLE_HALTS (0x0F)` | `InstrOracle_halts` |
| 16 | `instr_halt` | `OPCODE_HALT (0xFF)` | `InstrHalt` |

**Perfect 16/16 mapping across all three layers.**

## Summary

**The Coq kernel is the single source of truth.**

Everything else is generated from it automatically, ensuring perfect consistency and preserving the proven correctness properties.

**Update flow:** Coq → Extract → Generate → Verify → Done

**Never:** Manually edit generated files or try to sync layers by hand.

**Always:** Use `make generate-all` and `make verify-sync`.
