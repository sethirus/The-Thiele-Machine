# kernel/nfi

No Free Insight and its pricing. The certification-system record, the
floor for any substrate, why the toll holds on finite machines, how large the
bill is, and what a window can and cannot price. The No Free Insight rows of
the top-level README's [Formal Spine](../../../README.md#formal-spine) point
into this directory.

## The floor

| File | Purpose |
|---|---|
| `UniversalCertificationCost.v` | The `CertificationSystem` record and No Free Insight for any substrate (`universal_nfi_any_substrate`); a simulating certification system over a host certifies there too (`host_represents_simulating_cert_system`) |
| `QuantitativeNoFI.v` | From one to k: a system whose certification needs a threshold of witness pays at least that threshold (`universal_nfi_quantitative`) |
| `HonestCostTracking.v` | A cost record without A2 admits free forgery; A2 is a strict restriction (`honest_cost_tracking_strict_restriction`, `free_forgery_violates_A2`) |
| `CommitmentPredicateAdequacy.v` | The substitution test: which charge predicates keep the certification floor, and the exact-pricing characterization (`exact_commitment_pricing_characterization`) |
| `CommitmentVsErasure.v` | With trust held fixed, commitment cost does not reduce to erasure cost (`commitment_cost_not_reducible_to_erasure_cost`) |
| `StructuralUndecidability.v` | The diagonal over any substrate with a recursion theorem (`structural_shortcut_undecidable`) |
| `DecisionTreeBound.v` | A binary decision tree has at most two to the depth leaves, and the rounded logarithm bounds |

## Why the toll holds on finite machines

| File | Purpose |
|---|---|
| `PermanentCertification.v` | On a finite machine a certificate that is never revoked is switched on only by a merging step (`permanent_flip_is_not_injective`); pricing merges gives A2 (`a2_from_merging_price_and_permanence`); each premise is needed |
| `PermanentRecordPricing.v` | The bill's size (`permanent_flips_log_bound`) and which flips a finite machine must pay for (`forced_priced_iff_merges`, `flip_merges_or_revokes`, `forced_price_without_permanent_record`) |
| `PermanentCertificationEntropy.v` | The same bound in Shannon entropy, and heat under the named premise `landauer_heat` (`permanent_flip_heat_floor`, `known_state_flip_forces_no_heat`) |
| `FiniteCertMachine.v` | An eight-state machine that meets both premises as theorems (`fin_a2_from_merging_price`) |
| `PricingPhysicsTarget.v`, `PricingPhysicsAudit.v` | A ledger has no intrinsic joule value (`mu_has_no_intrinsic_joule_value`); a chosen scale is a premise (`calibrated_mu_landauer_energy`) |

## Windows and narrowing

| File | Purpose |
|---|---|
| `ShadowPricing.v` | No price computed from a window that confuses a certifying and a non-certifying step meets the floor without overcharging (`shadow_cannot_price_exactly`); a window showing the reading prices exactly |
| `KnowledgeNarrowing.v` | A machine's own spread of states shrinks only at a price (`run_narrowing_priced_log`); an observer's knowledge can shrink for free (`observer_narrowing_can_be_free`); wiping the display costs (`wipe_costs_at_least_one`) |
| `KnowledgeNarrowingIncremental.v`, `KnowledgeNarrowingMinimal.v` | The incremental reading of narrowing, and the smallest machine that narrows for free (`no_free_incremental_narrowing_below_three`) |

## Cost frameworks

| File | Purpose |
|---|---|
| `CostSemanticsComparison.v` | The ledger as a writer; A2 as the potential method (`a2_iff_nonnegative_amortized_cost`, `nfi_by_potential`) |
| `CostFrameworks.v` | Graded monads, amortized analysis, and the flip count against the cost (`a2_and_aara_iff_exact`, `flips_le_cost`) |

These files establish local correspondences, not embeddings of the cited
cost calculi.

## Imports

`foundation/` for substrates and the record-carrying machine definitions.
