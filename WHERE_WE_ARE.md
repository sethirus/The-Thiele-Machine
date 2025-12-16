# Where we are (Dec 16, 2025)

This file is the single source of truth for **current progress** and **what phases remain**.

## Executive status

- **CHSH falsifiability / non-forgeability**: Implemented and enforced at the receipt level.
- **Milestone 1A (canonical receipts→CHSH)**: Done; repo has one canonical extractor.
- **Milestone 1B (adversarial local bound test)**: Done; exhaustive deterministic local strategies satisfy $|\mathrm{CHSH}| \le 2$ (tight at ±2).
- **Milestone 1C (3-layer CHSH gate: Coq/extracted ↔ Python VM ↔ RTL)**: In progress; core plumbing is being wired so `CHSH_TRIAL` exists as a real instruction surface across layers.

## All milestones (tracked)

This section lists **all actively-tracked milestones** in this workspace (not just CHSH). Status meanings:

- **Done**: implemented + has a gate or reproducible run.
- **In progress**: partially wired; not yet end-to-end gated.
- **Tooling done**: code exists, but depends on external runs/data.

### Kernel / 3-layer isomorphism

- **Coq core build is admit-free** — Done (target gate: `make -C coq core`).
- **Extracted semantics runner (`build/extracted_vm_runner`)** — Done.
- **Foundry artifact generation (Coq → Python + Verilog opcode surfaces)** — Done (pipeline exists; keep opcode sets aligned).
- **3-way compute isomorphism (Python ↔ extracted ↔ RTL) for XOR/XFER subset** — Done (gate: `tests/test_rtl_compute_isomorphism.py`).
- **CHSH as a cross-layer instruction surface** — In progress (kernel + runner + RTL decode/testbench logging are being wired).

### Receipts / falsifiability

- **Signed step receipts + stable hashing** — Done (receipt schema + signing/verify helpers exist).
- **Non-forgeability policy for CHSH trials (count only `CHSH_TRIAL` receipts)** — Done.
- **Canonical receipts→CHSH extractor used repo-wide** — Done (single source: `tools/chsh_receipts.py`).

### CHSH classical bound gates

- **Milestone 1A: Canonical receipts→CHSH** — Done.
- **Milestone 1B: Adversarial local maximizer (deterministic strategies) + pytest bound** — Done.
- **Milestone 1C: 3-layer CHSH gate (Python ↔ extracted ↔ RTL)** — In progress.

### Hardware μ/partition enforcement

- **μ-core enforcement scaffolding exists in RTL** — Done (μ exported and checked for compute gates).
- **μ-ALU bit-exactness vs Python fixed-point reference** — Tooling done (verification hooks exist; ensure the documented success criteria remain green on your toolchain).

### Experiments / proofpacks (μ-ledger pipeline)

These correspond to the “zero-trust experiment runners” described in `experiments/README.md`.

- **Phase A1: Landauer builder + auditor** — Done.
- **Phase A2: Einstein builder + auditor** — Done.
- **Phase A3: Entropy-identity builder + auditor** — Done.
- **Phase B1: CWD builder + auditor** — Done.
- **Phase C: Cross-domain builder + auditor** — Done.
- **Phase E: Public dataset discovery + mirroring workflow** — Tooling done (requires real external runs per source).

## Canonical phase pipeline (for UI + reporting)

These are the required visualization phases:

1. **INIT**
2. **DISCOVER**
3. **CLASSIFY**
4. **DECOMPOSE**
5. **EXECUTE**
6. **MERGE**
7. **VERIFY**
8. **SUCCESS**

### Phase mapping to what exists today

- **INIT**: Supported (VM/runner/RTL start state exists and is exported).
- **DISCOVER**: Supported (partition discovery machinery exists; receipts support is already in place).
- **CLASSIFY**: Partially supported (classification outputs exist in receipts/CSR fields depending on workload).
- **DECOMPOSE**: Supported for partition operations; verification gates exist for partition-only observation.
- **EXECUTE**: Supported (compute op subset has a 3-way isomorphism gate).
- **MERGE**: Supported (partition merge exists).
- **VERIFY**: Supported for multiple gates; **CHSH 3-layer verification is being finalized**.
- **SUCCESS**: Defined as “all targeted gates pass”: Coq core build + focused pytest gates + consistent cross-layer traces.

## What changed most recently (cross-layer CHSH enablement)

Kernel / Coq:
- Added **`instr_chsh_trial`** to the kernel instruction type and semantics.
  - File: [coq/kernel/VMStep.v](coq/kernel/VMStep.v)
  - Includes bit-validity predicate (`chsh_bits_ok`) and error latching on bad bits.
- Updated the functional semantics `vm_apply` to match the relational step rule.
  - File: [coq/kernel/SimulationProof.v](coq/kernel/SimulationProof.v)
- Extended the compilation placeholder matcher so compilation remains total.
  - File: [coq/kernel/VMEncoding.v](coq/kernel/VMEncoding.v)

Extraction runner:
- Extended the trace parser to accept `CHSH_TRIAL x y a b cost`.
  - File: [tools/extracted_vm_runner.ml](tools/extracted_vm_runner.ml)

RTL:
- Added `OPCODE_CHSH_TRIAL = 8'h09` to the opcode header (temporary until the next regen).
  - File: [thielecpu/hardware/generated_opcodes.vh](thielecpu/hardware/generated_opcodes.vh)
- Added RTL decode/execute behavior for `OPCODE_CHSH_TRIAL`.
  - File: [thielecpu/hardware/thiele_cpu.v](thielecpu/hardware/thiele_cpu.v)
- Testbench now prints stable stdout lines for each CHSH trial:
  - `CHSH_TRIAL x y a b`
  - File: [thielecpu/hardware/thiele_cpu_tb.v](thielecpu/hardware/thiele_cpu_tb.v)

## Remaining work (phases + gates)

### Remaining engineering milestones

**Milestone 1C: 3-layer CHSH gate** (remaining)
- Add a pytest that:
  1) runs a small program on **Python VM** producing `step_receipts.json` with `CHSH_TRIAL` steps,
  2) runs **`build/extracted_vm_runner`** on an equivalent trace,
  3) runs **RTL sim** and parses `CHSH_TRIAL ...` lines from stdout,
  4) converts all three into the same canonical trial list and computes CHSH via the canonical extractor,
  5) asserts trial stream alignment and $|\mathrm{CHSH}| \le 2$.

### Remaining visualization phases work

- **DISCOVER → CLASSIFY**: ensure receipts/trace include stable per-step events suitable for progress bars.
- **DECOMPOSE → EXECUTE**: ensure module execution reports progress deterministically (no ad-hoc prints).
- **MERGE → VERIFY**: ensure cross-layer verification summary is a single clean terminal report.

## “Compilation proof” checklist (run before committing)

These are the local “proof of build + focused correctness” steps expected for the current CHSH work:

- Coq kernel core build:
  - `make -C coq core`
- Focused isomorphism gates (fast):
  - `pytest -q tests/test_partition_isomorphism_minimal.py`
  - `pytest -q tests/test_rtl_compute_isomorphism.py`
- After the CHSH 3-layer test is added, run it explicitly:
  - `pytest -q tests/test_chsh_three_layer_gate.py`

## Canonical CHSH extractor (do not fork)

All code in the repo should compute CHSH from receipts by calling:

- [tools/chsh_receipts.py](tools/chsh_receipts.py): `chsh_from_receipts_path(...)`

This keeps parsing conventions and non-forgeability identical across tools/tests.
