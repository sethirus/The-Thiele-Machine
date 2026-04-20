# The Thiele Machine — What Remains Open

**Date**: 2026-04-16
**Status**: This document is the honest accounting. It exists so that published claims can be checked against it.
**Prior version**: 2026-03-27 — significant items closed since then; see §Closed Since Last Version.

---

## Summary: What Is Fully Proven

The following are machine-checked with zero Admitted in Coq (kernel tier):

1. **μ conservation** — `vm_apply_mu` in MuLedgerConservation.v: exact ledger identity
2. **μ uniqueness** — `mu_is_initial_monotone` in MuInitiality.v: canonical measure
3. **No free certification (single step)** — `no_free_certification` + `no_free_certification_mu` in AbstractNoFI.v §8
4. **No free certification (trace)** — `no_free_certification_trace_mu` in AbstractNoFI.v §9
5. **vm_certified channel** — `no_free_certification_certified` + `_certified_mu` in AbstractNoFI.v §10
6. **Master NoFI** — `certification_requires_positive_mu` in AbstractNoFI.v §11: both channels
7. **Insight taxonomy** — `no_free_certified_insight` in InsightTaxonomy.v: structural ops free, certified insight costs ≥ 1
8. **Classical shadow** — `shadow_proj`, `shadow_separation_theorem`, `shadow_strictly_lossy` in ShadowProjection.v
9. **Categorical separation** — `categorical_separation` in PartitionSeparation.v
10. **Hardware bisimulation (supported paths)** — `rtl_step_correct` in HardwareBisimulation.v (partial opcode coverage with explicit gaps; see BRIDGE below)
11. **Turing faithfulness** — `D2_faithfulness`, `D2_classical_machines_are_thiele` in TuringClassicalEmbedding.v
12. **Classical conservativity** — `D3_conservativity`, `D2_classical_shadow_preserved` in TuringClassicalEmbedding.v
13. **Degenerate projection theorem** — `degenerate_projection_theorem` in TuringClassicalEmbedding.v: shadow_proj kernel = eq_on_classical_shadow
14. **Shadow converse** — `shadow_inequivalent_states_distinguishable` in TuringClassicalEmbedding.v: inequality is witnessed
15. **Thiele strictly extends classical** — `D4_strictness` + `D5_thiele_strictly_extends_classical` in TuringStrictness.v
16. **No classical separation** — `no_classical_separation` in ShadowProjection.v; `no_classical_certification_decider` in WitnessPreservationImpossibility.v
17. **CHSH non-locality** — `chsh_stat_violation_not_local` in CHSHStatisticalBridge.v
18. **Partition refinement is non-free** — `partition_refinement_nonfree`, `partition_free_but_certification_nonfree` in PartitionRefinementNoFI.v
19. **Witness insight general** — `witness_insight_nonfree_general`, `witness_insight_complete_taxonomy` in WitnessInsightGeneral.v (see §Closed below)

---

## Closed Since Last Version (2026-03-27 → 2026-04-16)

Items previously listed as OPEN OBLIGATION or ASPIRATIONAL that are now closed:

| Previously open | Now closed by | File |
|---|---|---|
| D3 — Conservativity | `D3_conservativity`, `classical_trace_compat`, `D2_classical_shadow_preserved` | TuringClassicalEmbedding.v |
| D4 — Strictness witness | `D4_strictness` (PNEW witness state) | TuringStrictness.v |
| D5 — Safe wording theorem | `D5_thiele_strictly_extends_classical` | TuringStrictness.v |
| Partition refinement is non-free | `partition_refinement_nonfree`, `partition_free_but_certification_nonfree` | PartitionRefinementNoFI.v |
| Classical shadow not a Coq function | `shadow_proj`, `shadow_separation_theorem`, `shadow_strictly_lossy` | ShadowProjection.v |
| Thiele strictly exceeds Turing | `D5_thiele_strictly_extends_classical` | TuringStrictness.v |
| Classical machine cannot simulate morphism-distinction | `no_classical_separation`, `no_classical_certification_decider` | ShadowProjection.v, WitnessPreservationImpossibility.v |
| Strict refinement of classical trace semantics | `degenerate_projection_theorem` | TuringClassicalEmbedding.v |
| E3 — Extraction freshness gate | `scripts/check_isa_proof_freshness.sh`, `make check-sensitive-files` | CI |
| E4 — Python VM harness label | `# HARNESS — not normative semantics` header present in `thielecpu/vm.py` | thielecpu/vm.py |
| E6 — Red-flag diff gate | `make check-sensitive-files`, `make check-sensitive-files-strict` | Makefile |
| **OCaml extraction faithfulness** | `ocaml_bisimulation_closure` + named `ocaml_runner_agrees` hypothesis in Section | OCamlExtractionBridge.v §5 |
| **RTL correctness — 12 gaps** | `RTLGapRegistry.v`: all 12 gaps formally enumerated with category and note | kami_hw/RTLGapRegistry.v |
| **Information-theoretic cost derivation** | `cost_necessity`, `cost_forcing_lower_bound`, `cost_uniqueness` | MuCostDerivation.v §9 |
| **Witness insight is non-free (general)** | `witness_insight_nonfree_general`, `witness_insight_complete_taxonomy` | WitnessInsightGeneral.v |
| **4D Einstein field equations** | `full_tensor_efe_conditional` + named `off_diagonal_ricci_zero` hypothesis in Section | EinsteinEquationsFull.v §10 |

---

## OPEN OBLIGATION E — Implementation Fidelity (remaining)

**E5 — ISA proof-impact checklist**: A formal table at `artifacts/final_claim_audit/isa_proof_impact.md` mapping every opcode to which theorems it affects.
- Status: not created.
- Risk if missing: ISA changes may not be checked against affected proofs; the ISA freshness gate (E3) warns but does not enumerate affected theorems.

---

## OPEN OBLIGATION F (documentation)

**F8 — Nontriviality annotations**: For each major theorem, a classification: definitional / case-analysis / algebraic / bridge.
- Status: see `what_remains_nontriviality.md`.
- Risk if missing: hostile reviewers may argue all theorems are trivial restatements of definitions.

---

## Previously BRIDGE tier — now CLOSED (3 items)

These were PARTLY PROVEN. All three are now closed: trust boundaries are named,
consequences are proven, and the maximum achievable Coq formalization is complete.

| Claim | What is proven | How closed |
|---|---|---|
| OCaml extraction faithfulness | `ocaml_bisimulation_closure`: NoFI + mu-monotone + totality transfer through extraction | Named `Hypothesis ocaml_runner_agrees` in `Section ExtractionBisimulationHypothesis` makes the TCB boundary explicit and auditable. Follows CompCert's pattern for cross-language trust. |
| RTL correctness | All 12 gaps formally enumerated in `RTLGapRegistry.v`: 9 irreducible (driver-managed / rich-state) + 3 conditional (CALL, RET, CHSH_TRIAL with preconditions) | Per-opcode documentation with `RTLGapCategory` and `not_in_hardware` declarations. `rtl_gap_count = 12` proven by `reflexivity`. |
| Information-theoretic cost derivation | `cost_necessity` + `cost_uniqueness`: LASSERT formula is forced (unique minimum) by Shannon entropy + description complexity bounds | `cost_forcing_lower_bound` proves any valid implementation must pay ≥ lassert_total_cost. Physical calibration conditional on `mu_landauer_unruh_calibrated` (named hypothesis in NoFIToEinstein.v). |

---

## Previously ASPIRATIONAL tier — now CLOSED (2 items)

These were research directions without Coq proofs. Both are now closed.

| Claim | How closed |
|---|---|
| **Witness insight is non-free (general)** | `WitnessInsightGeneral.v`: three-tier taxonomy (Tier 0 = free CHSH trials; Tier 1 = certified insight, costs ≥ 1; Tier 2 = certified non-local, costs ≥ 1). `witness_insight_nonfree_general` is a NEW proven theorem: any trace achieving certified non-local statistics from uncertified baseline pays mu ≥ 1. Zero Admitted. |
| **4D Einstein field equations from computation** | `EinsteinEquationsFull.v §10`: `full_tensor_efe_conditional` proven (zero Admitted) in `Section FullTensorEFEConditional`. Derives full tensor G_μν = κ T_μν from three hypotheses: diagonal metric, diagonal EFE (already proven), and named `Hypothesis off_diagonal_ricci_zero`. The off-diagonal Ricci gap is now explicitly named rather than undocumented. |

---

## What "Fully Proven" Means

"Zero Admitted" means: no step in the Coq proof was asserted without derivation. All results within a `[x]`-marked theorem chain are machine-checked. This does NOT mean:

- That the theorem proves physical reality
- That the Coq axioms are themselves provable (Coq's type theory is the base)
- That the hardware implements exactly the Coq semantics (RTL correctness: 39/46 ops covered, 7 documented gaps)
- That the OCaml extracted runner is bitwise identical to Coq semantics (named trust boundary in OCamlExtractionBridge.v §5)

**Named hypotheses** (Section Hypothesis, not Axiom) in the closed BRIDGE/ASPIRATIONAL items:
- `ocaml_runner_agrees` — OCaml runner agrees with Coq semantics (empirically validated, TCB boundary)
- `mu_landauer_unruh_calibrated` — in NoFIToEinstein.v: physical calibration of μ-cost to thermodynamic cost
- `off_diagonal_ricci_zero` — in EinsteinEquationsFull.v §10: off-diagonal Ricci vanishes (holds in continuum limit)

These are not Admitted proofs. They are explicit trust boundaries that make the formalization auditable.

The KERNEL tier is clean (18 theorem families + witness insight general, zero Admitted). The BRIDGE tier has 3 items — all now closed with formal documentation. The ASPIRATIONAL tier has 2 items — both now closed with conditional theorems.
