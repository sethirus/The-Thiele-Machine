# Extraction Guide: Coq → Verilog/Python Pipeline

**Single Source of Truth Architecture**

The Thiele Machine has a strict extraction pipeline where the Coq kernel is the canonical source of truth for all instruction semantics. Verilog and Python implementations are generated from the Coq specification to ensure perfect consistency.

## Architecture

```
┌──────────────────────────────────────────┐
│      Coq Kernel (Source of Truth)       │
│      coq/kernel/VMStep.v                 │
│                                           │
│  • 16 instructions (vm_instruction)      │
│  • Operational semantics (vm_step)       │
│  • μ-cost functions (instruction_cost)   │
│  • Conservation proofs                    │
└─────────────┬────────────────────────────┘
              │
       [Extraction & Generation]
              │
        ┌─────┴──────┬──────────────┐
        │            │              │
        ▼            ▼              ▼
   ┌─────────┐  ┌─────────┐   ┌─────────┐
   │  OCaml  │  │ Verilog │   │ Python  │
   │   .ml   │  │   .vh   │   │   .py   │
   └─────────┘  └─────────┘   └─────────┘
```

## Files

### Source (Coq)
- `coq/kernel/VMStep.v` - **SINGLE SOURCE OF TRUTH**
  - Defines all 16 instructions
  - Specifies operational semantics
  - Proves μ-cost conservation

### Extraction Infrastructure
- `coq/extraction/ExtractVM.v` - Coq extraction module
  - Extracts to OCaml for validation

### Generation Scripts
- `scripts/generate_python_from_coq.py` - Python generator
  - Reads VMStep.v
  - Generates Python dataclasses
  - Outputs: `thielecpu/generated/vm_instructions.py`

- `scripts/generate_verilog_from_coq.py` - Verilog generator
  - Reads VMStep.v
  - Generates SystemVerilog parameters
  - Outputs: `thielecpu/generated/opcode_definitions.vh`

### Generated Artifacts (DO NOT EDIT MANUALLY)
- `coq/extraction/vm_extracted.ml` - OCaml extraction (1,200+ lines)
- `thielecpu/generated/vm_instructions.py` - Python types (146 lines)
- `thielecpu/generated/opcode_definitions.vh` - Verilog opcodes (70 lines)

### Verification
- `scripts/verify_extraction_consistency.py` - Cross-layer validator
  - Checks all 16 instructions match
  - Reports any inconsistencies

## Workflow

### Adding a New Instruction

**DO THIS:**
1. Edit ONLY `coq/kernel/VMStep.v`:
   ```coq
   | instr_new_operation (param : nat) (mu_delta : nat)
   ```

2. Add to `instruction_cost` function:
   ```coq
   | instr_new_operation _ cost => cost
   ```

3. Add step rule to `vm_step`:
   ```coq
   | step_new_operation : forall s param cost,
       vm_step s (instr_new_operation param cost) ...
   ```

4. Run automated generation:
   ```bash
   make generate-all
   ```

**DO NOT DO THIS:**
- ❌ Manually edit Verilog opcode definitions
- ❌ Manually edit Python instruction types
- ❌ Try to "sync" the three layers by hand
- ❌ Edit any file marked "AUTO-GENERATED"

### Building Everything

```bash
# Full pipeline
make coq-kernel           # Compile Coq kernel
make extract-coq          # Extract to OCaml
make generate-all         # Generate Python & Verilog
make verify-sync          # Verify consistency

# Or all at once
make full-extraction
```

### Verifying Consistency

```bash
# Check all layers match
python3 scripts/verify_extraction_consistency.py

# Expected output:
# ✅ Coq ↔ Verilog (generated): PERFECT MATCH
# ✅ Coq ↔ Python (generated): PERFECT MATCH
# 🎉 RESULT: Perfect three-layer consistency
```

## Makefile Targets

| Target | Description |
|--------|-------------|
| `extract-coq` | Extract Coq kernel to OCaml |
| `generate-python` | Generate Python from Coq |
| `generate-verilog` | Generate Verilog from Coq |
| `generate-all` | Generate Python + Verilog |
| `verify-sync` | Verify three-layer consistency |
| `full-extraction` | Complete extraction pipeline |

## Benefits

### Single Source of Truth ✅
- Update one file (Coq)
- Generate all others automatically
- Guaranteed consistency

### Proof-Carrying Code ✅
- Coq proofs cover all instructions
- Generated code inherits correctness
- μ-cost conservation proven

### Reduced Errors ✅
- No manual synchronization
- Automated verification
- Type-safe generation

## CI Integration

The extraction pipeline runs automatically in CI:

```yaml
- name: Build Coq Kernel
  run: make coq-kernel

- name: Extract & Generate
  run: make full-extraction

- name: Verify Consistency
  run: make verify-sync
```

Any inconsistency fails the build.

## Generated File Headers

All generated files have headers:

```python
"""
AUTO-GENERATED from Coq kernel/VMStep.v
Generated: 2025-12-11T06:15:00

DO NOT EDIT THIS FILE MANUALLY
Regenerate with: make generate-python
"""
```

**If you see this header, DO NOT EDIT THE FILE.**

## Example: Current Instruction Set

All 16 instructions are generated from Coq:

1. instr_pnew → OPCODE_PNEW (0x00) → InstrPnew
2. instr_psplit → OPCODE_PSPLIT (0x01) → InstrPsplit
3. instr_pmerge → OPCODE_PMERGE (0x02) → InstrPmerge
4. instr_lassert → OPCODE_LASSERT (0x03) → InstrLassert
5. instr_ljoin → OPCODE_LJOIN (0x04) → InstrLjoin
6. instr_mdlacc → OPCODE_MDLACC (0x05) → InstrMdlacc
7. instr_pdiscover → OPCODE_PDISCOVER (0x06) → InstrPdiscover
8. instr_xfer → OPCODE_XFER (0x07) → InstrXfer
9. instr_pyexec → OPCODE_PYEXEC (0x08) → InstrPyexec
10. instr_xor_load → OPCODE_XOR_LOAD (0x0A) → InstrXor_load
11. instr_xor_add → OPCODE_XOR_ADD (0x0B) → InstrXor_add
12. instr_xor_swap → OPCODE_XOR_SWAP (0x0C) → InstrXor_swap
13. instr_xor_rank → OPCODE_XOR_RANK (0x0D) → InstrXor_rank
14. instr_emit → OPCODE_EMIT (0x0E) → InstrEmit
15. instr_oracle_halts → OPCODE_ORACLE_HALTS (0x0F) → InstrOracle_halts
16. instr_halt → OPCODE_HALT (0xFF) → InstrHalt

**Perfect 16/16 mapping across all three layers.**

## Troubleshooting

### "Inconsistency detected" error

```bash
# Regenerate all artifacts
make generate-all

# Verify again
make verify-sync
```

### Generated files out of date

```bash
# Check if Coq kernel changed
git status coq/kernel/VMStep.v

# If yes, regenerate
make full-extraction
```

### Build fails after adding instruction

1. Check Coq compiles: `make coq-kernel`
2. If Coq error, fix in VMStep.v
3. If extraction error, check ExtractVM.v
4. Regenerate: `make generate-all`

## Summary

**Golden Rule**: The Coq kernel (`coq/kernel/VMStep.v`) is the single source of truth. Everything else is generated from it. Never edit generated files manually.

**Workflow**: Edit Coq → Compile Coq → Extract → Generate → Verify

**Verification**: Run `make verify-sync` after any changes to ensure three-layer consistency.
