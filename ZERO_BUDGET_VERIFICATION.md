# Zero-Budget Verification Checklist (Audit Log)

This document is the single source of truth for “as sure as possible” verification with $0 budget.

- Repo: sethirus/The-Thiele-Machine
- Branch: `main`
- Last updated: 2025-12-19

## 1) Mathematical Correctness Audit

### 1.1 Coq builds from clean

- [x] Command: `make -C coq clean && make -C coq -j8 all`
- [x] Result: **SUCCESS** (warnings present; no proof failures)
- Notes:
  - Deprecated notation warnings and “native_compute disabled” warnings exist but do not affect proof completion.

- [x] Command (fast gate): `make -C coq core`
- [x] Result: **SUCCESS** (`Nothing to be done for 'real-all'.`)

### 1.2 Inquisitor strict mode

- [x] Command: `/workspaces/The-Thiele-Machine/.venv/bin/python scripts/inquisitor.py --strict --build`
- [x] Result: **INQUISITOR: OK**
- [x] Report: [INQUISITOR_REPORT.md](INQUISITOR_REPORT.md)

## 2) Implementation Consistency Check (3-layer isomorphism)

Goal: run identical programs through Python VM, extracted Coq runner, and RTL; assert identical projected state.

### 2.1 Minimal cross-layer isomorphism gates

- [x] Python ↔ extracted runner ↔ RTL: [tests/test_partition_isomorphism_minimal.py](tests/test_partition_isomorphism_minimal.py)
  - [x] Includes **100-case randomized** PNEW-only program campaign (deterministic seed)
  - [x] Result: `2 passed`

- [x] RTL compute alignment: [tests/test_rtl_compute_isomorphism.py](tests/test_rtl_compute_isomorphism.py)
  - [x] Result: `1 passed`

- [x] Extracted runner integration: [tests/test_extracted_vm_runner.py](tests/test_extracted_vm_runner.py)
  - [x] Result: `2 passed`

- [x] Equivalence bundle (strict evidence mode): [tests/test_equivalence_bundle.py](tests/test_equivalence_bundle.py)
  - [x] Result: `10 passed`

- [x] RTL μ-charging static check: [tests/test_rtl_mu_charging.py](tests/test_rtl_mu_charging.py)
  - [x] Result: `1 passed`

- [x] Consolidated gate run (2025-12-19):
  - [x] Command: `/workspaces/The-Thiele-Machine/.venv/bin/python -m pytest -q tests/test_equivalence_bundle.py tests/test_partition_isomorphism_minimal.py tests/test_rtl_compute_isomorphism.py tests/test_extracted_vm_runner.py tests/test_rtl_mu_charging.py`
  - [x] Result: `15 passed in 122.61s (0:02:02)`

### 2.2 Adversarial fuzzing status

- [ ] Python ↔ Verilog Hypothesis fuzzing: [tests/adversarial_fuzzing.py](tests/adversarial_fuzzing.py)
  - Status: **KNOWN FAILING / NOT A SOURCE-OF-TRUTH ISOMORPHISM GATE**
  - Reason: uses a **simplified** Verilog harness (`fuzz_harness_simple.v`) that explicitly does *not* enforce full μ-core semantics, so μ totals are not comparable.

### 2.3 Bug fixed during verification

- [x] Fixed idempotence bug in Python `State.pnew`: duplicates must dedup even when at MAX_MODULES.
  - File: [thielecpu/state.py](thielecpu/state.py)
  - Symptom: randomized PNEW-only campaign could hit `max modules reached` even when adding an already-existing region.

- [x] Fixed Python VM final auto-MDLACC to respect empty-graph boot semantics (no implicit module 0).
  - File: [thielecpu/vm.py](thielecpu/vm.py)
  - Symptom: compute-only programs (no partition ops) could crash with `KeyError: 0`.

## 3) Tsirelson Bound Re-Derivation (step-by-step audit)

Goal: a skeptic can trace the inequality chain from stated axioms/lemmas to the final numeric bound.

- [ ] Identify exact starting axioms/definitions (partition axioms, no-free-insight, etc.)
- [ ] List theorem-by-theorem derivation chain for the Tsirelson bound (file/lemma pointers)
- [ ] Numerically sanity check: $5657/2000 \approx 2.8285$ vs $2\sqrt{2} \approx 2.8284$
- [ ] Produce a short “skeptic-readable derivation outline” section

## 4) Edge Cases & Counterexamples

Goal: actively try to break invariants and ensure failures are explicit and consistent.

- [ ] Add/run μ-conservation edge-case tests (empty partition, overlapping split, cyclic op sequences, max depth, etc.)
- [ ] Add/run partition-invariant edge-case tests (dedup, canonicalization, module-limit behavior)

## 5) Independent Code Review (free)

- [ ] Prepare a short review request + pointers (what to look at, how to reproduce)
- [ ] Post to at least 2 communities (manual)
- [ ] Track feedback and fixes

## 6) Claim Separation Audit ([PROVEN]/[IMPLEMENTED]/[CONJECTURED]/[SPECULATION])

- [ ] Pick the target doc(s): thesis + paper + README (decide scope)
- [ ] Annotate claims and rewrite for explicit separation

## 7) Falsifiability Check

- [ ] For each major physical claim: define falsification criteria + required measurement + cost + current status

## 8) Prior Art Search (free)

- [ ] Perform a structured search and record results (queries + links + notes)

## 9) Consistency with Known Results

- [ ] Turing equivalence test for blind programs (no PNEW/PSPLIT)
- [ ] Complexity sanity checks (where applicable)

## 10) Explain to a Skeptic

- [ ] Draft “Common Objections and Responses”
- [ ] Ensure each response cites either (a) Coq theorem, (b) implementation test, or (c) explicitly labeled conjecture

---

## Completion Criteria

This checklist is **complete** when every item above is checked.
