# Coq Verification Status - December 13, 2025

## Campaign ZERO ADMITS - Current Status

**Admitted proofs**: 0 (per `./scripts/audit_coq_proofs.sh`)  
**Axioms declared**: non-zero (audit currently reports 24)  
**Build**: `make -C coq core` and `make -C coq Extraction.vo` succeed

---

## What’s Mechanically Proven vs Executably Checked

### Coq proofs (mechanized)
- `setup_state_mem_structure` - CPU memory = `[program][rules][tape]`
- `setup_state_tape_region` - Tape extraction from address 1000
- `tape_window_ok_setup_state` - Tape window correctness
- `inv_full_setup_state` - Full initialization invariant

### Helper Lemmas (12 total)
- Register access: `setup_state_reg_q/head/pc/temp1/addr`
- Memory regions: `setup_state_program_prefix`, `setup_state_rules_window`
- Opaque handling: `tape_window_ok_intro`

---

### Cross-layer executable checks (real execution)

- Foundry pipeline: `bash scripts/forge_artifact.sh`
   - Rebuilds Coq extraction → generates shared opcode artifacts → compiles + runs RTL sim → runs pytest gate
- Coq-extracted semantics runner: `build/extracted_vm_runner`
   - Runs the extracted OCaml semantics from `build/thiele_core.ml`
   - Gate test: `tests/test_extracted_vm_runner.py` currently checks a concrete `PNEW/PNEW/PMERGE` trace matches Python `thielecpu.state.State` on region sets and total μ

## Monitoring Tools

### `./scripts/coq_monitor.sh <target.vo>`
Tracks: Memory (MB), CPU (%), Lemmas, Proofs, Errors  
Output: Live terminal + logs in `/tmp/coq_monitor_*`

### `./scripts/audit_coq_proofs.sh`
Reports: Admits, Axioms, Opaque defs, Proof stats

---

## The Proof Chain

```
Coq proofs/specs → extracted semantics (OCaml) → Python VM / Verilog RTL
      ↓                    ↓                     ↓
  mechanized            executable oracle     executable gates
```

**Status**: Toolchain is operational; alignment is enforced by executable gates on a growing subset.

## Remaining gaps to “100% isomorphic”

To claim “100% completed and isomorphic”, we need all three layers to share the *same* step semantics for *all* opcodes and all state components.

Known gaps today:

- The extracted runner (`build/extracted_vm_runner`) exports a unified observable snapshot (`pc`, `mu`, `err`, `regs`, `mem`, `csrs`, `graph`). Compute-state isomorphism is already gated by `tests/test_rtl_compute_isomorphism.py`.
- Partition/module semantics (`PNEW/PSPLIT/PMERGE`) still require full opcode-by-opcode alignment between RTL and the extracted/Python model (dedup, normalization, and any μ/receipt constraints).
- Boundary opcodes that involve host calls (`LASSERT`, `PYEXEC`) need an explicit equivalence boundary (what is modeled in Coq/extraction vs what is treated as an external oracle in RTL/VM) and stable receipt semantics.
- μ-core enforcement in RTL must be reflected in the executable gates (either by supplying receipts in the trace/program, or by constraining tests to the shared projection the Coq kernel actually models).

Next milestone (recommended): expand the extracted-runner gate to cover every opcode where the Coq kernel defines behavior, and make VM/RTL match that behavior on the shared state projection.
