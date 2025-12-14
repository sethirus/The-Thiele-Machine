# Agent workflow for The Thiele Machine

This repo’s north star is **3-layer isomorphism** (Coq ↔ executable extraction ↔ Python VM ↔ RTL). The goal is to keep **step semantics** and **state projection** identical across layers.

## The Inquisitor (required mindset)

Treat Coq kernel semantics (and its extracted runner) as authoritative. Don’t “fix the layer you’re in”; instead, use a minimal distinguishing trace to locate and eliminate divergences.

**Rules of engagement**:
- Do not introduce `Admitted.` or `Axiom` in the active Coq tree.
- If a proof becomes hard, first reduce/strengthen the statement, factor lemmas, or canonicalize representations; then validate with a small executable gate.
- For any opcode/state change: produce a minimal trace and add/extend a gate that runs Python ↔ extracted runner ↔ RTL.

## Execution gates

**Fast, local correctness**:
- `make -C coq core`
- `pytest -q tests/test_partition_isomorphism_minimal.py`
- `pytest -q tests/test_rtl_compute_isomorphism.py`

**Full foundry gate (when toolchain is available)**:
- `bash scripts/forge_artifact.sh`

**Extracted semantics runner**:
- `build/extracted_vm_runner <trace.txt>` prints a final JSON snapshot (pc, mu, err, regs, mem, csrs, graph).

**RTL state export**:
- `thielecpu/hardware/thiele_cpu_tb.v` prints a final JSON snapshot; tests decode the first JSON object from stdout.

## Practical “divergence reduction” loop

1. Create the smallest trace that triggers the mismatch.
2. Run it through:
   - Python VM
   - extracted runner
   - RTL sim
3. If results differ, reduce to: one opcode, one instruction word, one small state snapshot.
4. Fix the root cause once (canonicalization, operand decode, state projection), then re-run the same trace.

## Toolchain

Tested versions (in CI/dev containers):
- Coq 8.18.x (OCaml 4.14.x)
- Python 3.12.x
- iverilog 12.x
- yosys 0.33+

## Verified build state (Dec 14, 2025)

- `kernel/KernelPhysics.v` is enabled in `coq/_CoqProject` and built by `make -C coq core`.
- Canonical region normalization is enforced via `normalize_region` and the lemma `normalize_region_idempotent` in `coq/kernel/VMState.v`.
- Kernel “no-signaling” is formulated over **partition-only observation** (`ObservableRegion`), keeping μ accounting separate.

The active Coq tree is enforced admit-free: no top-level `Admitted.` (or `admit.` tactics) and no top-level `Axiom` declarations in `coq/**/*.v`.
