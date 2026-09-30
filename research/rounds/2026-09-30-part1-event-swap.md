# Part 1 freeze: event genericity and the swap theorem

Frozen 2026-09-30, before any proof of the statements below.

Definitions and statements: `coq/kernel/foundation/EventSwapCore.v` as committed with this record. Any change to that file after this commit starts a new dated round, and this record stays unedited.

## Item 1.1: event-generic audit

Statement. Every main theorem in the monograph's claim ledger belongs to one of three classes:

- **G (generic):** its statement quantifies over an arbitrary reading or an arbitrary `CertificationSystem`, so it holds for any latchable event;
- **C (certification only):** its statement names `vm_certified` or `csr_cert_addr`;
- **N (not about a recorded event):** the ledger, the graph, CHSH/NPA, undecidability, embeddings.

Prediction. The classification below. Two classes beyond the three above: I counts an instruction class, such as CERTIFY's declared charge, not a reading's value; M is about another named event in a specific model, such as finalization or commitment.

Predicted classification (100 ledger theorems):

- **G, generic** (22): a2_from_entropy_price_and_permanence, a2_from_merging_price_and_permanence, entropy_priced_trace_floor, flip_merges_or_revokes, honest_erasure_accounting_implies_a2, injective_flip_revokes, known_state_flip_forces_no_heat, permanent_certification_trace_floor, permanent_flip_full_support_heat_positive, permanent_flip_heat_floor, permanent_flip_heat_positive, permanent_flip_is_not_injective, permanent_flip_uniform_entropy_drop, permanent_flips_collapse_at_least, permanent_flips_compression_bound, permanent_flips_log_bound, permanent_record_write_is_forced_priced, permanent_step_entropy_ceiling, shadow_cannot_price_exactly, thiele_represents_simulating_cert_system, universal_nfi_any_substrate, window_showing_reading_prices_exactly.
- **C, certification only** (24): P_full_complete_neither_mu_nor_cert_droppable, certification_is_lost, certification_requires_positive_mu, kernel_certified_implies_positive_mu, mu_ledger_minimality, mu_ledger_mutual_independence, mu_ledger_necessity, no_classical_certification_decider, no_free_certification, no_free_certification_certified, no_free_certification_mu, no_free_certification_trace_mu, partition_free_but_certification_nonfree, partition_refinement_nonfree, thiele_nfi_pc_indexed, thiele_universal_nfi_cert_addr, thiele_universal_nfi_certified, vm_bare_shadow_cannot_price_exactly, vm_certified_not_classically_determined, vm_certifying_step_is_priced_merge, vm_forget_shadow_cannot_price_exactly, vm_fragment_certification_paid, vm_prices_certifying_merge_leaves_others_free, witness_insight_nonfree_general.
- **I, counts an instruction class** (6): info_priced_cert_executions_bound, level_k_verification_floor, mu_hierarchy_no_upper_bound, mu_hierarchy_theorem, structural_trace_preserves_cert_addr, witness_insight_complete_taxonomy.
- **M, another named event in a model** (6): attestation_cannot_factor_through_bare_transcript, commit_without_erasure_system_is_not_honest, forced_price_without_permanent_record, gas_schedule_exactness, nothing_at_stake_is_free_forgery, slashing_finality_floor.
- **N, not about a recorded event** (42): D2_faithfulness, D3_conservativity, D4_strictness, D5_thiele_strictly_extends_classical, b4_information_reduction_derives_strict_predicates, blindness_non_injective, categorical_separation, chsh_stat_violation_not_local, classical_observer_cannot_separate, column_contractive_iff_npa_psd, degenerate_projection_theorem, entropy_drop_as_point_sum, entropy_drop_pos_of_support_merge, every_sound_structural_shortcut_lands_here, exists_covering_tree, feasible_strict_subset_implies_strict_predicates, fin_compression_priced, fin_merging_priced, forced_priced_iff_merges, forget_kernel_is_eq_on_classical, graph_certify_morphism_lookup, info_priced_arbitrary_feasible_reduction_bound, info_priced_reduction_no_tree_hypothesis, info_priced_weighted_feasible_reduction_bound, mu_is_initial_monotone, nat_recursion_theorem, nat_self_undecidable, nat_structural_shortcut_undecidable, nat_to_program_program_to_nat, observation_partition_reduction_implies_posterior_representative_reduction, shadow_separation_theorem, shadow_strictly_lossy, sound_shortcut_from_components, state_column_contractive_implies_tsirelson, strengthening_requires_structure_addition, structural_entitlement_representation, structural_shortcut_undecidable, vm_apply_mu, vm_mu_not_classically_determined, vm_runs_finite_trace, vm_structural_shortcut_undecidable, zero_mu_traces_satisfy_preservation_budget.

Success. A test pins every ledger theorem to one class. For each G theorem, a Coq file instantiates it at a reading other than certification, and the file compiles.

Failure. Any G theorem that cannot be instantiated at a non-certification reading. Any ledger theorem left unclassified.

## Item 1.2: generalize every certification-only theorem

The C theorems fall into three families. Each family has one generalized statement in `EventSwapCore.v`.

| Family | Generalized statement | C theorems |
|---|---|---|
| Pricing | `pricing_generalizes` | no_free_certification, no_free_certification_mu, no_free_certification_trace_mu, no_free_certification_certified, certification_requires_positive_mu, thiele_universal_nfi_cert_addr, thiele_universal_nfi_certified, thiele_nfi_pc_indexed, kernel_certified_implies_positive_mu, partition_refinement_nonfree, partition_free_but_certification_nonfree, witness_insight_nonfree_general, vm_fragment_certification_paid, vm_certifying_step_is_priced_merge, vm_prices_certifying_merge_leaves_others_free |
| Hiding | `forget_hiding_generalizes`, `bare_hiding_generalizes` | certification_is_lost, vm_certified_not_classically_determined, mu_ledger_necessity, mu_ledger_mutual_independence, mu_ledger_minimality, P_full_complete_neither_mu_nor_cert_droppable, no_classical_certification_decider |
| Inexact shadow price | `bare_inexactness_generalizes`, `forget_inexactness_generalizes` | vm_bare_shadow_cannot_price_exactly, vm_forget_shadow_cannot_price_exactly |

Certification-level theorems (mu_hierarchy_theorem, mu_hierarchy_no_upper_bound, level_k_verification_floor), info_priced_cert_executions_bound, structural_trace_preserves_cert_addr and witness_insight_complete_taxonomy count an instruction class (CERTIFY's declared charge, or certificate-address setters), not the value of a reading. The prediction is that they have no event generalization. They will be marked BLOCKED with that reason unless a generalization is found.

Predictions:

- `pricing_generalizes`: REFUTED. Counterexamples: E_word, "every register and memory cell holds a 64-bit word", switched on by LOAD_IMM with charge 0; and E_graph, "the graph has allocated a module" (`1 <= pg_next_id`), switched on by PNEW [] 0.
- `forget_hiding_generalizes`: REFUTED by E_word and by E_mu, `1 <= vm_mu`, which forget shows.
- `bare_hiding_generalizes`: REFUTED by E_word.
- `bare_inexactness_generalizes`, `forget_inexactness_generalizes`: REFUTED by E_word. A window that shows the reading prices it exactly (`window_showing_reading_prices_exactly`).

Success. Closed Coq proofs of each negation, with each counterexample shown latchable.

Failure. Any family where no latchable counterexample exists. That family would then be PROVED, needing a closed proof of the generalization.

## Item 1.3: the swap theorem

Statement: `swap_preserves_main_results`. For every latchable reading E, all five main results hold with E in place of certification.

Prediction: REFUTED, by E_word, which fails all five.

Sanity instance: `certification_main_results` is PROVED. Certification is latchable and satisfies all five. This is the vacuity check: the statement is not refuted because its premises are unsatisfiable.

Success. Closed Coq proofs of `~ swap_preserves_main_results` and of `certification_main_results`.

Failure. If every latchable reading satisfies all five, the swap theorem is PROVED instead. That needs a closed proof.

## Strategies planned (R11)

1. Direct counterexamples: E_word, E_graph, E_mu, each with a latchability proof built from `state_64bit_bounded_step`, `vm_step_next_id_monotone` and `vm_apply_mu`.
2. For the hiding families, if E_word's permanence is too costly to prove: a counterexample reading that is a function of `vm_mu` alone (E_mu), since both forget and the ledger results show `vm_mu`.
3. For the inexact-price families: instantiate `window_showing_reading_prices_exactly` at a counterexample reading that the window shows.

## Items 1.4 and 1.5

These are documentation items: a line-by-line pass under R10, and keeping Chapter 26 labeled as a conjecture. They have no Coq statement. They are reported with the audits that check them: the prose audit, the meaning gate, the citation audit, and a manual pass.
