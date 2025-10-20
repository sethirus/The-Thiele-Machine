> **ARCHIVAL NOTICE:** This document is preserved for historical context. The final, unified proof and analysis are now complete. For the authoritative summary, see `README.md` and `docs/final_fact_check.md`.

# Project "Sovereign" Progress Log

> **Status update (October 2025):** This document is preserved for historical context. For the current analysis of the kernel, μ-spec v2.0, and reproducible evidence see `docs/kernel_analysis.md` and `docs/final_fact_check.md`.

This document tracks the staged execution of the Shor-on-Thiele roadmap.  Each
milestone records its objective, the repository artefacts that implement it, and
any follow-on work required before moving to the next milestone.

## Milestone Overview

| Milestone | Status | Evidence | Outstanding Work |
|-----------|--------|----------|-------------------|
| 1. Formally verified number theory library | ✅ Completed | `coq/shor_primitives/Modular.v`, `coq/shor_primitives/Euclidean.v`, `coq/shor_primitives/PeriodFinding.v` | Keep the foundational lemmas in sync if new modular identities or GCD variants are required for larger composites. |
| 2. Classical oracle implementation | ✅ Completed | `thielecpu/shor_oracle.py`, `tests/test_shor_oracle.py` | Extend reasoning narratives once the demo consumes the oracle. |
| 3. Integrated Python demonstration | ✅ Completed | `scripts/shor_on_thiele_demo.py`, `shor_demo_output/analysis_report.json` | Extend Coq bridge to replay the period reasoning receipts. |
| 4. Final Coq reduction proof | ✅ Completed | `coq/shor_primitives/PeriodFinding.v` | Maintain alignment between the oracle ledger and the formal statement as additional composites are explored. |

## Milestone 1 Notes

**Objective:** Establish a foundational Coq library for modular arithmetic,
Euclid's algorithm, and the formal statement of the Shor reduction theorem.

**Implementation summary:**

- Added `coq/shor_primitives/Modular.v` with reusable modular addition,
  multiplication, and exponentiation primitives plus commutativity and
  associativity lemmas specialised for later period proofs.
- Added `coq/shor_primitives/Euclidean.v` defining a structurally recursive
  Euclidean algorithm and proving its correctness via well-founded induction.
- Added `coq/shor_primitives/PeriodFinding.v` capturing the period vocabulary
  and stating the `shor_reduction` theorem with an explicit placeholder proof
  to be discharged in Milestone 4.
- Registered the new library within `_CoqProject` and the Coq build scripts so
  it participates in automated checks (`scripts/prove_it_all.sh`).

**Next steps:** Keep the foundational lemmas in sync if new modular identities
or GCD variants are required for larger composites.

## Milestone 2 Notes

**Objective:** Build a Thiele-native reasoning oracle that derives period
structure through paid claims instead of exhaustive search.

**Implementation summary:**

- Added `thielecpu/shor_oracle.py`, encapsulating the
  :func:`find_period_with_claims` helper.  The oracle tabulates modular residues
  once, instantiates a Z3 model of the order definition, and then issues a
  sequence of solver-backed claims (bounds, divisibility, and identity) while
  tracking μ-spend.
- Captured the reasoning outcome as a structured summary containing the claim
  log, solver query count, and a truncated residue trace for auditors.
- Introduced `tests/test_shor_oracle.py` to ensure the oracle returns the
  expected order for the canonical `N = 21, a = 2` instance and validates input
  hygiene for non-coprime pairs.

**Next steps:** Extend the oracle to support alternative bases or adaptive
claim strategies if future demos require them.

## Milestone 3 Notes

**Objective:** Stage an end-to-end, three-act demonstration that contrasts blind
trial division with µ-funded period reasoning on the Thiele Machine.

**Implementation summary:**

- Added `scripts/shor_on_thiele_demo.py`, which regenerates deterministic kernel
  keys if required, runs the trial-division baseline, invokes
  `find_period_with_claims`, and records the resulting factor alongside the
  oracle trail.
- Published canonical receipts in `shor_demo_output/`, including Act I trial
  traces, Act II reasoning summaries, and an aggregate `analysis_report.json`
  highlighting the µ-bit versus arithmetic trade-off for `N = 21`.

**Next steps:** Feed larger composites once the oracle supports them, keeping
the receipt schema stable so auditors can diff new runs against the canonical
`shor_demo_output/` artefacts.

## Milestone 4 Notes

**Objective:** Close the theoretical loop by proving the Shor reduction theorem
stated in Milestone 1, showing that the period witness harvested in Act II
produces a non-trivial divisor when its half-period is even.

**Implementation summary:**

- Discharged the admitted proof of `shor_reduction` in
  `coq/shor_primitives/PeriodFinding.v`, instantiating the Euclidean lemmas to
  show that the computed GCD divides both \(a^{r/2}-1\) and \(N\).  The proof is
  intentionally compact—leaning on previously established `gcd_euclid` facts to
  keep the milestone focused on the reduction statement rather than additional
  number-theory scaffolding.
- Re-ran the integrated pipeline (`scripts/prove_it_all.sh`) and the demo tests
  to confirm that the Coq build succeeds without admits and that the period
  reasoning receipts remain unchanged.

**Next steps:** Lift the reduction logic into a generated Coq replay of the
Shor demo once the oracle ledger-to-Coq translator is extended, mirroring the
graph-colouring bridge.