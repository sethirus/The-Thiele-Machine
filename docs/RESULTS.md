# Results

This file states the settled results about the record axis, the events it
can carry, the guest recursion theorem, pricing and physics, and the real
systems the repository models. Each result names the Coq declarations that
carry it and has one of four statuses:

- **Proved.** A Coq theorem states the result.
- **Refuted.** A Coq theorem states its negation, and a named declaration
  supplies the counterexample.
- **Conditional.** A Coq theorem states the result under a named premise
  that no machine fact discharges. The premise is a hypothesis of the
  statement, not an axiom.
- **Not formalized here.** The question lies outside the formal development.
  The reason is given in one line.

Every theorem cited below is closed under the global context, except the ones
listed under "Standard-library axioms" at the end, which use only the Coq
standard library's real-number and classical axioms. No cited theorem uses a
project axiom. `tests/test_results_doc.py` checks that every cited declaration
exists in `coq/` and that these statuses agree with the assumption receipt in
`artifacts/print_assumptions_all_proofs.txt`.

## Uniqueness and the record axis

The questions here ask how much of a machine the record axis pins down.

- **Refuted.** Every adequate machine has a core equivalent to `ThieleCore`
  (`adequate_core_uniqueness`). Counterexample: `BilledCore`.
  Coq: `adequate_core_uniqueness_refuted`.
- **Refuted.** Every honest VM extension is equivalent to `ThieleCore` when
  certification, ledger balance, halting, and step cost are all observed
  (`honest_vm_extension_uniqueness`). Counterexample: `BilledCore`.
  Coq: `billed_core_not_observed_equiv`, `honest_vm_extension_uniqueness_refuted`.
- **Refuted.** A machine whose record is some reading tied to the Thiele core
  through the cover is equivalent to it up to the price schedule
  (`tied_record_schedule_uniqueness`). Counterexample: `MeterCore`, which
  satisfies the premise by `meter_core_honest_tied`.
  Coq: `tied_record_schedule_uniqueness_refuted`.
- **Proved.** A machine whose record is the certification reading through the
  cover is equivalent to the Thiele core up to the price schedule
  (`cert_record_schedule_uniqueness`). `BilledCore` and every surcharged core
  satisfy the premise. Coq: `cert_record_schedule_uniqueness_holds`,
  `billed_core_honest_cert`, `surcharged_core_honest_cert`.
- **Proved.** Over any deterministic base, a computation-driven, priced,
  permanent, written record factors as a latch: the next record is the old
  record or a function of the base state (`record_axis_is_latch`). Two
  permanent records factor as two latches, each reading the other
  (`record_pair_is_two_latches`). Coq: `record_axis_is_latch_holds`,
  `record_pair_is_two_latches_holds`.

## Growing records

A growing record takes values in a partial order and only moves up
(`HonestGrowingExtension`).

- **Proved.** Every honest growing record satisfies a complete family of
  permanent threshold-update equations, one per lower threshold, and keeps its
  price schedule (`growing_record_decomposes`). This is a representation
  lemma: the threshold events are built from the driving function, and the
  schedule is a premise carried through. Coq: `growing_record_decomposes_holds`.
- **Proved.** The complete family of lower thresholds determines the record
  value (`thresholds_determine_record`). Coq: `thresholds_determine_record_holds`.
- **Proved.** On a growing record, pricing every strict value change is
  equivalent to pricing every false-to-true threshold flip
  (`record_price_iff_threshold_price`).
  Coq: `record_price_iff_threshold_price_holds`.
- **Refuted.** One Boolean latch carries every honest growing record
  (`one_latch_suffices`). Counterexample: a fully priced three-value chain
  over a one-state base (`ThreeMachine`, `OneBase`, `ThreeCover`, with honesty
  proved by `three_honest`). Three values cannot be decoded from one base
  state and one bit. Coq: `one_latch_refuted`.
- **Proved.** A pairwise-distinct, pointwise-monotone chain of k-bit vectors
  has at most k + 1 members (`chain_needs_bits`). A chain through n
  distinct values in this representation needs at least n - 1 bits. The
  bound concerns monotone Boolean-vector encodings, not arbitrary encodings.
  Coq: `chain_needs_bits_holds`.

## Revocation and accountable finality

- **Proved.** A reading with an actual true-to-false transition is not
  permanent. Coq: `actual_revocation_excludes_permanence_holds`.
- **Refuted.** Pricing revocation prices writes. Counterexample: a Boolean
  toggle that charges one from true and zero from false.
  Coq: `revocation_price_does_not_price_writes_refuted`.
- **Proved.** In the Casper FFG model, two finalized blocks on conflicting
  branches imply a quorum whose votes satisfy a slashing condition. The proof
  is constructive. Coq: `accountable_safety`, `conflicting_records_are_priced`,
  `casper_conflict_is_accountable_holds`, with the key step
  `distinct_justified_same_epoch_slashes`. This is the known accountable-safety
  theorem of Casper FFG. It shows that slashable votes exist, not that a slash
  is executed or that finality is deleted.
- **Proved.** The premise of accountable safety is inhabited: a concrete
  three-validator fork finalizes two conflicting blocks and its slashed
  quorum is computed. Coq: `casper_fork_exists`, `casper_fork_slashable`.
- **Proved.** Writing a finalization record need not slash anyone: a
  one-validator setting finalizes with no slashing.
  Coq: `casper_write_without_slashing_holds`, `finalization_without_slashing`.

The literal permanent-record axis therefore excludes any record that is
actually revoked, while accountable conflict fits the axis when a
contradiction entails a stated penalty.

## Probabilistic records

In a finite positive-weight branching model:

- **Refuted.** A deterministic latch handles branching
  (`deterministic_latch_handles_branching`). Counterexample:
  `fair_branch_kernel`, whose two positive branches force one event value to
  be both false and true. Coq: `deterministic_latch_handles_branching_refuted`.
- **Refuted.** Equal branch support and equal branch charges determine the
  branch weights (`schedule_determines_probabilities`). Counterexample:
  `fair_branch_kernel` (weights 1 and 1) against `biased_branch_kernel`
  (weights 1 and 2), both honest by `fair_branch_honest` and
  `biased_branch_honest`. Coq: `schedule_determines_probabilities_refuted`.
  Uniqueness up to the schedule fails; the probability kernel has to be
  preserved as well.
- **Proved.** The relation that preserves ordered weight lists exactly is
  reflexive. This is a well-formedness check only.
  Coq: `probability_preserving_equivalence_reflexive_holds`.

## Bases and granularity

`weak_base_equiv` relates two observed bases when they agree on the chosen
observations and on halting, and a step on either side matches zero or more
steps on the other.

- **Proved.** `weak_base_equiv` is an equivalence relation.
  Coq: `weak_base_equiv_refl_holds`, `weak_base_equiv_sym_holds`,
  `weak_base_equiv_trans_holds`.
- **Proved.** Weakly equivalent bases agree on whether the record axis is a
  latch over them. The statement does not use its equivalence premise, since
  `record_axis_is_latch_holds` proves both sides for every deterministic base.
  Coq: `weak_equiv_preserves_record_latch_holds`.
- **Proved.** The record axis is a latch over four concrete bases: the toy
  Turing machine, the unbounded VM, the Cook and Reckhow unit-cost RAM over
  natural numbers (indirect load and store, conditional jumps), and the
  lambda calculus L under weak call-by-value reduction.
  Coq: `record_axis_is_latch_on_tm_holds`, `record_axis_is_latch_on_vm_holds`,
  `record_axis_is_latch_on_ram_holds`, `record_axis_is_latch_on_l_holds`.
  The RAM is a separate machine with random access through registers
  (`ram_store_then_load`, `ram_jump_pos_taken`, `ram_halted_stutters`,
  `ram_pointer_demo_runs`). The L step function is computed by structure and
  agrees with the reduction relation (`l_step_fun_correct`,
  `l_base_halted_iff_irreducible`, `l_base_run_is_star`, `star_is_l_base_run`).

## Concrete record machines

- **Proved.** A tied RAM appends the overwritten value to its record on every
  write; an untied RAM leaves its record unchanged, and equal base values do
  not determine an untied record. Coq: `ram_tied_overwrite_records_old_value`,
  `ram_untied_overwrite_has_no_record`, `ram_untied_record_not_determined_by_base`.
- **Proved.** Unbounded and modular arithmetic updates are undone by their
  syntactic inverses. These are Janus-like reversible cores, not the full Janus
  language. Coq: `janus_like_unbounded_inverse`, `janus_like_bounded_inverse`.
- **Proved.** In list memory, a write to an existing cell reads back, the
  tied step appends exactly the address and old value, the untied record never
  changes, and both machines agree on memory and program counter. Coq:
  `concrete_ram_write_reads_back`, `concrete_tied_ram_records_overwrite`,
  `concrete_untied_ram_record_unchanged`, `concrete_tied_and_untied_same_base`,
  with the executed example `concrete_ram_two_cell_witness`.
- **Proved.** Over one shared RAM base, the tied record grows, is driven by
  the computation, and passes both the honest growing test and the latch test
  for every nonempty program; the untied record is constant and fails both.
  A computed run separates the two records while their base projections agree.
  Coq: `tied_record_grows`, `tied_record_driven`, `tied_honest_growing`,
  `tied_honest_base_extension`, `untied_run_record_constant`,
  `untied_not_honest_growing`, `untied_not_honest_base_extension`,
  `ram_record_axis_classification`, `record_axis_separates_ram`.
- **Proved.** The two-counter machine of minimal/EarnedCore.v, whose
  commitments are earned, has an undecidable halting problem, satisfies the
  certification floor, is adequate as a record-carrying machine, is an honest
  extension of its base (program and core, everything but the ledger and the
  flag), and moves its record as a latch. Coq:
  `earned_core_halting_undecidable`, `earned_core_floor`,
  `earned_core_adequate`, `earned_core_honest`, `earned_core_is_latch`. Its
  provenance, checker-soundness, no-forging and price theorems are in
  minimal/EarnedCore.v itself, on the Coq standard library alone.
- **Proved.** A host built on that machine runs any of its programs as a
  guest, keeps a mirror equal to the guest's certified flag, and raises the
  mirror only in a guest step that passed CERTIFY, charged in that step, for
  every sequence of host moves, in minimal/UniversalThiele.v on the Coq
  standard library alone; coq/kernel/foundation/UniversalThieleLinks.v makes
  the host and its guests certification systems. A machine from elsewhere
  enters through the two-counter encoding; its own price list is not kept.

## Which events the theorems allow

A reading is latchable when it is permanent and some step writes it. The
certification reading is one latchable event among many.

### Event-generic theorems

The 49 theorems below quantify over an arbitrary event. Each has a closed
specialization in `EventGenericAudit.v` to an event other than certification.
The main model is a two-state door: Open switches the permanent reading
from closed to open at cost one, and Wait costs zero
(`door_one_step_opens`, `door_one_step_costs_one`). A three-state saturating
meter reaches its event after two ticks and pays for it
(`meter_two_ticks_reach_event`, `meter_event_run_pays`), and a toggle supplies
the injective, revoking case. The door also instantiates No Free Insight
(`DoorNoFreeInsight`).

For 45 of the 49, the specialization discharges every premise, including the
uniform distribution, compression and entropy pricing, and the blind-window
price the statements ask for. Four keep a physical premise that no machine
fact discharges: Landauer heat, and for `collapse_step_cost_ge_1_from_calibrated_dissipation` also its
cost calibration. Those four are conditional.

| Event-generic theorem | Specialization | Premises |
|---|---|---|
| `a2_equal_trust_substitution_payoff` | `evidence_a2_equal_trust_substitution_payoff` | discharged |
| `exact_commitment_pricing_characterization` | `evidence_exact_commitment_pricing_characterization` | discharged |
| `substitution_test_rejects_non_a2_exact_substitute` | `evidence_substitution_test_rejects_non_a2_exact_substitute` | discharged |
| `commitment_cost_not_reducible_to_erasure_cost` | `evidence_commitment_cost_not_reducible_to_erasure_cost` | discharged |
| `a2_and_aara_iff_exact` | `evidence_a2_and_aara_iff_exact` | discharged |
| `flips_le_cost` | `evidence_flips_le_cost` | discharged |
| `a2_iff_nonnegative_amortized_cost` | `evidence_a2_iff_nonnegative_amortized_cost` | discharged |
| `certification_system_is_potential_method` | `evidence_certification_system_is_potential_method` | discharged |
| `nfi_by_potential` | `evidence_nfi_by_potential` | discharged |
| `collapse_step_cost_ge_1_from_calibrated_dissipation` | `evidence_collapse_step_cost_from_calibrated_dissipation` | Landauer premise kept |
| `gas_schedule_exactness` | `evidence_gas_schedule_exactness` | discharged |
| `overcharge_breaks_exactness` | `evidence_overcharge_breaks_exactness` | discharged |
| `undercharged_opcode_admits_free_commitment` | `evidence_undercharged_opcode_admits_free_commitment` | discharged |
| `free_forgery_violates_A2` | `evidence_free_forgery_violates_A2` | discharged |
| `honest_cost_tracking_strict_restriction` | `evidence_honest_cost_tracking_strict_restriction` | discharged |
| `a2_from_merging_price_and_permanence` | `evidence_a2_from_merging_price_and_permanence` | discharged |
| `honest_erasure_accounting_implies_a2` | `evidence_honest_erasure_accounting_implies_a2` | discharged |
| `permanent_certification_trace_floor` | `evidence_permanent_certification_trace_floor` | discharged |
| `permanent_flip_is_not_injective` | `evidence_permanent_flip_is_not_injective` | discharged |
| `permanent_flips_collapse_at_least` | `evidence_permanent_flips_collapse_at_least` | discharged |
| `a2_from_entropy_price_and_permanence` | `closed_a2_from_entropy_price_and_permanence` | discharged |
| `entropy_priced_trace_floor` | `closed_entropy_priced_trace_floor` | discharged |
| `permanent_flip_full_support_entropy_drop_positive` | `closed_permanent_flip_full_support_entropy_drop_positive` | discharged |
| `permanent_flip_full_support_heat_positive` | `evidence_permanent_flip_full_support_heat_positive` | Landauer premise kept |
| `permanent_flip_heat_floor` | `evidence_permanent_flip_heat_floor` | Landauer premise kept |
| `permanent_flip_heat_positive` | `evidence_permanent_flip_heat_positive` | Landauer premise kept |
| `permanent_flip_uniform_entropy_drop` | `evidence_permanent_flip_uniform_entropy_drop` | discharged |
| `permanent_step_entropy_ceiling` | `closed_permanent_step_entropy_ceiling` | discharged |
| `permanent_step_entropy_drop` | `closed_permanent_step_entropy_drop` | discharged |
| `a2_from_compression_price_and_permanence` | `closed_a2_from_compression_price_and_permanence` | discharged |
| `compression_priced_trace_floor` | `closed_compression_priced_trace_floor` | discharged |
| `flip_merges_or_revokes` | `evidence_flip_merges_or_revokes` | discharged |
| `injective_flip_revokes` | `evidence_injective_flip_revokes` | discharged |
| `permanent_at_flip_is_not_injective` | `evidence_permanent_at_flip_is_not_injective` | discharged |
| `permanent_flips_compression_bound` | `closed_permanent_flips_compression_bound` | discharged |
| `permanent_flips_log_bound` | `closed_permanent_flips_log_bound` | discharged |
| `permanent_record_write_is_forced_priced` | `evidence_permanent_record_write_is_forced_priced` | discharged |
| `finite_reversible_cannot_write` | `evidence_finite_reversible_cannot_write` | discharged |
| `history_latch_honest` | `evidence_history_latch_honest` | discharged |
| `latch_core_honest` | `evidence_latch_core_honest` | discharged |
| `shadow_cannot_price_exactly` | `evidence_shadow_cannot_price_exactly` | discharged |
| `shadow_floor_overcharges` | `closed_shadow_floor_overcharges` | discharged |
| `step_price_is_exact` | `evidence_step_price_is_exact` | discharged |
| `window_showing_reading_has_no_collision` | `evidence_window_showing_reading_has_no_collision` | discharged |
| `window_showing_reading_prices_exactly` | `evidence_window_showing_reading_prices_exactly` | discharged |
| `record_axis_is_latch_holds` | `evidence_record_axis_is_latch_holds` | discharged |
| `record_pair_is_two_latches_holds` | `evidence_record_pair_is_two_latches_holds` | discharged |
| `universal_nfi_any_substrate` | `evidence_universal_nfi_any_substrate` | discharged |
| `no_free_insight` | `evidence_no_free_insight` | discharged |

### Mu-Chaitin bound

- **Refuted** for the VM. The Mu-Chaitin functor's pricing field requires every
  VM instruction to be priced. A morph-assert instruction with a positive
  payload and zero scheduled cost refutes it.
  Coq: `current_schedule_not_globally_cert_priced`.
- **Conditional.** The functor's bounds hold for any system satisfying the
  pricing policy `CERT_PRICING_POLICY` (`EmptyMuChaitinAudit`).
- **Proved.** The trace-local form holds for the VM: only instructions on the
  theory's traces must be priced, and the payment is derived from the kernel
  certification theorem. A VM run that creates a module, adds its identity
  morphism, and asserts it instantiates the interface.
  Coq: `supra_cert_paid_payload_trace_local`, `kernel_trace_instance_bound`.

### Certification-specific theorems

The 55 theorems below name certification. Each one's event-generic form,
stated over every latchable event, is settled by a wrapper theorem in
`EventGeneralization.v` whose statement is exactly that form or its negation:
19 hold and 36 are refuted.

Three counterexample events do the refuting:

- graph allocation, `eg_graph_reading`: `PNEW [] 0` switches it on at zero
  cost, which refutes the price and mu floors (`eg_graph_latchable`,
  `eg_graph_not_priced`);
- a state-size reading, `eg_size_reading`, visible to the projections the
  hiding theorems use (`eg_size_latchable`). Its latching witness uses a
  15-register state, outside the 16-register invariant, so these refutations
  hold on the raw state type only;
- a mu threshold, `eg_mu_reading`, written injectively by a positive-cost
  checkpoint, which refutes the writer-merge form (`eg_mu_latchable`,
  `eg_mu_checkpoint_write`).

The forms that hold are the trace-writer lemma, finite-state permanence and
merging under their premises, exact pricing by a schedule defined from the
event, projection irredundancy, the revocation boundary, billed-core adequacy
and honest extension, schedule uniqueness under an explicit event-pricing
premise, reachable-simulation descent, representation through an
event-reflecting embedding, and the direct certification specification. Some
of these repeat a premise or assume the essential structure. The
reachable-simulation existence form is stated for any global representative
satisfying a retraction law. One such representative exists:
`reachable_trace_representative` picks, for each state, the first trace in an
enumeration of all traces that reaches it, so the existence form holds outright
(`generalized_reachable_simulation_holds`). The pick is a search, not a
program that rebuilds a trace from a state: it uses the choice principle
`ClassicalDedekindReals.sig_forall_dec` of Coq's real numbers, which the corpus already assumes. The billed and surcharged schedule equivalences
fail because the unchanged Thiele base does not price every substituted event.

| Certification theorem | Event-generic form | Status | Coq |
|---|---|---|---|
| `certification_requires_positive_mu` | `generalized_step_mu` | refuted | `cert_positive_mu_not_event_generic` |
| `no_free_certification` | `generalized_step_price` | refuted | `no_free_certification_not_event_generic` |
| `no_free_certification_certified` | `generalized_step_price` | refuted | `no_free_cert_certified_not_event_generic` |
| `no_free_certification_mu` | `generalized_step_mu` | refuted | `no_free_cert_mu_not_event_generic` |
| `no_free_certification_trace_mu` | `generalized_trace_mu` | refuted | `no_free_cert_trace_mu_not_event_generic` |
| `thiele_nfi_pc_indexed` | `generalized_trace_writer` | proved | `nfi_pc_indexed_event_generic` |
| `certification_is_lost` | `generalized_forget_hidden` | refuted | `certification_is_lost_not_event_generic` |
| `fcertify_merges` | `generalized_finite_writer_merge` | proved | `fcertify_merges_event_generic` |
| `fin_a2_from_compression_price` | `generalized_finite_a2_from_compression_price` | proved | `fin_a2_from_compression_event_generic` |
| `fin_a2_from_merging_price` | `generalized_finite_a2_from_merging_price` | proved | `fin_a2_from_merging_event_generic` |
| `fin_permanent` | `generalized_finite_permanent` | proved | `fin_permanent_event_generic` |
| `vm_certify_merges` | `generalized_vm_writer_merge` | refuted | `vm_certify_merges_not_event_generic` |
| `vm_certifying_step_is_priced_merge` | `generalized_vm_priced_merge_bundle` | refuted | `vm_priced_merge_not_event_generic` |
| `vm_fragment_certification_paid` | `generalized_trace_mu` | refuted | `vm_fragment_paid_not_event_generic` |
| `vm_prices_certifying_merge_leaves_others_free` | `generalized_vm_priced_merge_bundle` | refuted | `vm_merge_others_free_not_event_generic` |
| `thiele_unit_price_lower_bounds_mu` | `generalized_event_unit_price_lower_bounds_mu` | refuted | `unit_price_bounds_mu_not_event_generic` |
| `thiele_vm_commit_pricing_is_exact` | `generalized_event_unit_pricing_exact` | proved | `commit_pricing_exact_event_generic` |
| `P_full_complete_neither_mu_nor_cert_droppable` | `generalized_projection_irredundancy` | proved | `p_full_irredundant_event_generic` |
| `cost_model_cert_necessity` | `generalized_cost_projection_necessity` | refuted | `cost_model_necessity_not_event_generic` |
| `mu_ledger_minimality` | `generalized_projection_classification` | refuted | `mu_ledger_minimality_not_event_generic` |
| `mu_ledger_mutual_independence` | `generalized_mutual_independence` | refuted | `mutual_independence_not_event_generic` |
| `thiele_state_three_component_independence` | `generalized_three_component_independence` | refuted | `three_component_indep_not_event_generic` |
| `turing_ram_cert_necessity` | `generalized_strict_projection_necessity` | refuted | `turing_ram_necessity_not_event_generic` |
| `partition_free_but_certification_nonfree` | `generalized_partition_free_but_event_nonfree` | refuted | `partition_free_cert_nonfree_not_event_generic` |
| `partition_refinement_nonfree` | `generalized_partition_refinement_nonfree` | refuted | `partition_refinement_not_event_generic` |
| `revocable_certificate_escapes` | `generalized_revocation_boundary` | proved | `revocable_escapes_event_generic` |
| `kernel_certified_implies_positive_mu` | `generalized_bounded_run_mu` | refuted | `kernel_cert_positive_mu_not_event_generic` |
| `cert_addr_not_function_of_forget` | `generalized_forget_hidden` | refuted | `cert_addr_forget_not_event_generic` |
| `cert_not_function_of_forget` | `generalized_forget_hidden` | refuted | `cert_forget_not_event_generic` |
| `no_classical_a2_cert_predicate` | `generalized_forget_hidden` | refuted | `classical_a2_predicate_not_event_generic` |
| `no_classical_cert_addr_predicate` | `generalized_forget_hidden` | refuted | `classical_addr_predicate_not_event_generic` |
| `vm_bare_shadow_cannot_price_exactly` | `generalized_bare_price_inexact` | refuted | `bare_shadow_price_not_event_generic` |
| `vm_forget_shadow_cannot_price_exactly` | `generalized_forget_price_inexact` | refuted | `forget_shadow_price_not_event_generic` |
| `billed_core_equiv_mod_schedule` | `generalized_billed_schedule_equivalence` | refuted | `billed_schedule_equiv_not_event_generic` |
| `surcharged_core_equiv_mod_schedule` | `generalized_surcharged_schedule_equivalence` | refuted | `surcharged_schedule_equiv_not_event_generic` |
| `cert_record_schedule_uniqueness_holds` | `generalized_schedule_uniqueness` | proved | `schedule_uniqueness_event_generic` |
| `billed_core_adequate` | `generalized_billed_core_adequate` | proved | `billed_core_adequate_event_generic` |
| `billed_core_honest_extension` | `generalized_billed_core_honest_extension` | proved | `billed_core_honest_event_generic` |
| `adequate_core_uniqueness_refuted` | `generalized_billed_not_core_equiv` | proved | `adequate_uniqueness_refuted_event_generic` |
| `honest_vm_extension_uniqueness_refuted` | `generalized_billed_not_observed_equiv` | proved | `vm_extension_uniqueness_refuted_event_generic` |
| `certification_agreement_does_not_imply_descent` | `generalized_agreement_does_not_imply_descent` | proved | `agreement_not_descent_event_generic` |
| `reachable_simulation_exists_iff` | `generalized_reachable_simulation_exists` | proved | `reachable_sim_exists_event_generic` |
| `reachable_simulation_unique` | `generalized_reachable_simulation_unique` | proved | `reachable_sim_unique_event_generic` |
| `thiele_represents_simulating_cert_system` | `generalized_simulating_system_representation` | proved | `simulating_system_repr_event_generic` |
| `thiele_universal_nfi_cert_addr` | `generalized_trace_cost` | refuted | `universal_nfi_cert_addr_not_event_generic` |
| `thiele_universal_nfi_certified` | `generalized_trace_cost` | refuted | `universal_nfi_certified_not_event_generic` |
| `certified_witness_insight_nonfree` | `generalized_step_price_and_mu` | refuted | `witness_insight_nonfree_not_event_generic` |
| `no_free_certification_certified_trace_mu` | `generalized_trace_mu` | refuted | `certified_trace_mu_not_event_generic` |
| `nonlocal_witness_insight_nonfree` | `generalized_nonlocal_witness_step` | refuted | `nonlocal_witness_not_event_generic` |
| `witness_insight_nonfree_general` | `generalized_nonlocal_witness_trace` | refuted | `witness_insight_general_not_event_generic` |
| `no_classical_certification_decider` | `generalized_no_classical_event_decider` | refuted | `classical_decider_not_event_generic` |
| `mu_ledger_necessity` | `generalized_joint_ledger_necessity` | proved | `mu_ledger_necessity_event_generic` |
| `mu_ledger_necessity_universal` | `generalized_certify_pnew_separation` | refuted | `ledger_necessity_universal_not_event_generic` |
| `vm_certified_not_classically_determined` | `generalized_strict_projection_necessity` | refuted | `vm_cert_nonclassical_not_event_generic` |
| `Certified_spec` | `generalized_certified_spec` | proved | `certified_spec_event_generic` |

### The swap theorem

- **Refuted.** Every latchable reading satisfies all five main results that
  certification satisfies: it is priced, hidden from the forget and bare
  projections, and priced inexactly by both shadows
  (`swap_preserves_main_results`). Counterexample: graph allocation, the
  reading `1 <=? pg_next_id (vm_graph s)`, which `PNEW [] 0` switches on at
  zero cost from `init_state`. The reading is latchable
  (`eg_graph_reading_latchable`) and the state keeps the 16-register width
  (`init_state_register_width`). Coq: `swap_preserves_main_results_refuted`.
- **Proved.** Certification satisfies all five
  (`certification_main_results`). Coq: `certification_main_results_hold`,
  `certification_reading_permanent`, `certification_reading_written`,
  `certification_hidden_from_bare`.

## Guest recursion and Rice's theorem

The guest is the four-register fragment of the VM that the self-interpreter
runs.

- **Proved.** The Kleene recursion theorem holds inside the guest
  (`vm_guest_recursion_theorem`): for every transformer F that maps
  well-formed guest programs to well-formed guest programs and is represented
  by a guest program, some well-formed guest program p behaves exactly as F p,
  with the same final registers and the same mu ledger.
  Coq: `vm_guest_recursion_theorem_closed`.
  The proof runs the evaluator inside the guest. The evaluator relation is
  extracted to the lambda calculus L, which gives it a Minsky machine
  (`RD_MMA`). That machine is compiled to guest code, whose output lands in
  guest register zero (`mma_output_to_guest_r0`). Binary specialization keeps
  the runtime input (`g_pair_smn`). The diagonal program is the guest pipeline
  specialized to its own code (`g_pair_specialize`, `guest_program_code`).
- **Proved.** Rice's theorem holds for the guest (`vm_guest_rice`): every
  extensional, nontrivial property of well-formed guest programs is
  undecidable. The proof reduces from Minsky-machine halting and does not use
  the recursion theorem. Coq: `vm_guest_rice_holds`, with
  `vm_guest_execution_is_actual` tying the guest relation to actual VM
  execution.
- **Proved.** Supporting facts: the numeric code of a guest program decodes
  back to it, a fuel-bounded evaluator agrees with actual execution, and
  prefixing a constant load is a semantic s-m-n specialization.
  Coq: `g_decode_guest_code_roundtrip`, `g_eval_is_actual_vm_execution`,
  `g_smn`, `identity_transformer_representable`.
- **Refuted.** Every map on programs of the full VM has a fixed point up to
  equal thousand-step runs from every state. Coq:
  `vm_full_recursion_premise_refuted`. The counterexample map is the flip of
  `vm_bounded_shortcut_decide`, a correct decider of the bounded shortcut
  property, and the flip of every correct decider has no such fixed point.
  Coq: `vm_correct_flip_has_no_fixed_point`. The guest theorem above is a
  different statement: its runs are the unbounded sibling's, and its
  equality is final registers and ledger.

## Pricing and physics

- **Proved.** Under every cost schedule that prices merges, no injective
  instruction is forced to have positive price; forced price is exactly
  non-injectivity (`no_price_beyond_merges`). It is a direct corollary of
  `forced_priced_iff_merges` and says nothing about schedules outside that
  class. Coq: `no_forced_price_beyond_merges`.
- **Proved** at the logical level. A permanent finite write is a many-to-one
  step, so it pays logically (`permanent_flip_logical_payment`).
  Coq: `permanent_write_has_logical_payment`. Economic, cryptographic, and
  heat payment each need a premise about that level and are not derived.
- **Refuted.** Mu has an intrinsic joule value (`no_intrinsic_joule_scale`
  states the refutation). Two distinct external scales fit the same
  natural-number ledger. Coq: `mu_has_no_intrinsic_joule_value`.
- **Conditional.** At the Landauer scale `k_B T ln 2`, one mu unit is
  `k_B T ln 2` (`mu_landauer_calibration`). Coq: `calibrated_mu_landauer_energy`.
  Fixing the scale is a premise, not a measurement.
- **Conditional.** Given the `landauer_heat` premise, flipping a permanent
  reading on a finite state space releases heat at least the logarithmic
  floor (`landauer_permanence_heat_floor`). Coq:
  `permanence_heat_floor_uses_landauer`, through `permanent_flip_heat_floor`.
  The finite-state entropy is invariant under permutation of the state
  enumeration: `semantics_entropy_permutation_invariant`. Both formulas are
  known from Landauer's principle; the checked content is the link from a
  permanent record write to a many-to-one step.
- **Proved.** A two-state calorimeter protocol: a canonical reset from
  half-excited to ground satisfies a discrete master equation exactly, and at
  fixed Hamiltonian the bath receives `Delta / 2`.
  Coq: `canonical_reset_satisfies_master_equation`, `canonical_reset_heat_exact`.
- **Proved**, with the scale built in: choosing the gap `2 k_B T ln 2` gives
  heat `k_B T ln 2`. Coq: `selected_gap_gives_landauer_heat`.
- **Refuted.** The master equation and a one-unit ledger change force the
  Landauer bound. Counterexample: the same reset with gap `k_B T ln 2` releases
  half that heat; gaps one and two have identical dynamics and different heat.
  Coq: `smaller_gap_refutes_unconditional_landauer_floor`,
  `master_equation_does_not_fix_heat_scale`. Ruling the smaller gap out needs
  a thermal premise such as local detailed balance, or device evidence.
- **Proved.** The protocol's one-unit ledger change equals the VM's minimal
  certification charge, and every certification charges at least that much.
  No state map between the protocol and the VM is claimed.
  Coq: `canonical_reset_is_one_mu`,
  `vm_minimal_certification_charges_canonical_reset_mu`,
  `vm_certification_charges_at_least_canonical_reset_mu`.

## Real-system models

Each model below is narrow. None is a full security, consensus, database, or
audit-log theorem.

- **Proved** boundary checks for RFC 9162 Certificate Transparency: the
  iterative inclusion and consistency verifiers of RFC 9162 Sections 2.1.3.2
  and 2.1.4.2 reject the boundary cases, and symbolic runs accept the
  Section 2.1.5 examples. Coq: `rfc9162_inclusion_boundary_safe`,
  `rfc9162_consistency_boundary_safe`, `rfc9162_example_inclusion_d0`,
  `rfc9162_example_consistency_4_7`. Appending to a log history keeps old
  entries and grows the size (`ct_extension_preserves_entries`,
  `ct_extension_size_monotone`). Collision resistance and signed-tree-head
  authenticity are cryptographic premises and are not proved; the symbolic
  digests rule collisions out by construction and serve only to run the RFC
  control flow.
- **Proved** for a toy proof-carrying-code fragment: the executable checker
  accepts exactly the address-bound verification condition, a typed
  certificate entails it, and an out-of-range access is rejected.
  Coq: `pcc_checker_accepts_iff_vc`, `pcc_certificate_implies_vc`,
  `pcc_unsafe_program_rejected`, `pcc_safe_instance`. This mirrors the roles
  of Necula's PCC; it is not that system.
- **Refuted.** A bare sign/verify interface implies TPM quote authenticity.
  Counterexample: a scheme that always signs false and accepts every
  signature accepts true (`degenerate_accepts_forgery`).
  Coq: `tpm_interface_authenticity_refuted`. Authenticity needs a trusted-key
  or unforgeability premise.
- **Proved**, and known from the governing sources, five narrow
  countermodels: a Certificate Transparency client's local view cannot detect
  a split log (`ct_local_view_insufficient`, RFC 9162 Section 11.3); a quote
  checker must bind the PCR selection (`tpm_selection_binding_is_necessary`,
  tpm2-tools advisory GHSA-8rjm-5f5f-h4q6); a local chain suffix does not fix
  the trusted anchor (`weak_subjective_suffix_insufficient`, Ethereum's
  weak-subjectivity guidance); an acknowledged commit needs a durable commit
  record (`wal_ack_requires_durability`, PostgreSQL WAL documentation); and a
  current local log does not establish a past event
  (`audit_local_snapshot_insufficient`, NIST SP 800-92). Each is a generic
  two-state collision or durability counterexample that does not need the
  record axis. No surveyed consequence is both new and specific to the
  record axis.

## The pointer criterion

The pointer-observable criterion is a conjecture. Choosing the observers and
the event is a modeling choice that proofs cannot make. The formal
definitions and the selected model instances are proved only inside their
observer maps.

- **Proved.** Twelve candidate events over six observer maps proliferate
  exactly as follows. Coq: `twelve_candidate_measurements_checked`.

  | Event | Observer map | Proliferates |
  |---|---|---|
  | finalized block | proof of stake | yes |
  | proposer work | proof of stake | no |
  | committed state | gas metering | yes |
  | scratch work | gas metering | no |
  | attestation issued | trusted execution | yes |
  | measurement noise | trusted execution | no |
  | certificate included | Certificate Transparency | yes |
  | prover effort | Certificate Transparency | no |
  | certificate checked | proof-carrying code | yes |
  | prover effort | proof-carrying code | no |
  | MAC authenticity | symmetric MAC | no |
  | signature authenticity | digital signature | yes |

  The MAC row is a model counterexample to universal proliferation
  (`mac_model_not_proliferating`). Reading it as a statement about forgery in
  deployed systems is a separate modeling premise.
- **Proved.** Swapping which event the fragments mirror swaps the unique
  pointer: the second event becomes the pointer and the first does not
  proliferate. Coq: `swapped_event_is_pointer_checked`,
  `first_event_not_proliferating`.
- **Refuted.** Consensus among authenticated observers that update by a
  local rule forces the observed event to be permanent. Counterexample:
  `toggle_game`, two observers that agree and update by negation, so the
  event turns false. Coq: `toggle_game_refutes_strong_pointer_necessity`.
- **Conditional.** If at least one observer exists, every view is sound and
  complete for the event, and a true view stays true (`durable_views`), the
  event is permanent. The persistence premise carries the conclusion.
  Coq: `durable_consensus_implies_permanence`.

## Not formalized here

- **Full proof-carrying code.** Necula's system (SAL execution, the LF
  encoding, the verification-condition generator, and both soundness
  translations) is another system; formalizing it is outside the Thiele
  Machine.
- **Full embeddings of four cost calculi.** Graded modal effect semantics
  (Orchard, Liepelt, and Eades), the Danner, Licata, and Ramyaa cost
  translation, automatic amortized resource analysis, and linear-logic
  resource semantics are other systems. The repository proves the fragments
  it uses: `a2_and_aara_iff_exact`, `flips_le_cost`,
  `certification_system_is_potential_method`, `nfi_by_potential`.
- **Certificate Transparency gossip and checkpoint distribution.** RFC 9162
  leaves gossip undefined, and the weak-subjectivity guidance specifies no
  distribution protocol, so there is no protocol semantics to formalize.
- **Persistent-memory durability barriers.** This needs a hardware model of
  flush completion and power failure that the platform documentation does
  not give.
- **Storage-energy and joule calibration.** These need physical measurement
  on a device; none is part of this repository.
- **Cryptographic hardness.** Collision resistance, signature
  unforgeability, and signed-tree-head authenticity appear only as premises.

## Standard-library axioms

These cited theorems depend on axioms drawn only from the Coq standard library:
the real-number axioms `ClassicalDedekindReals.sig_forall_dec` and
`ClassicalDedekindReals.sig_not_dec`,
`Classical_Prop.classic`, and
`FunctionalExtensionality.functional_extensionality_dep`.

- `a2_from_entropy_price_and_permanence`
- `calibrated_mu_landauer_energy`
- `canonical_reset_heat_exact`
- `canonical_reset_satisfies_master_equation`
- `closed_a2_from_entropy_price_and_permanence`
- `closed_entropy_priced_trace_floor`
- `closed_permanent_flip_full_support_entropy_drop_positive`
- `closed_permanent_step_entropy_ceiling`
- `closed_permanent_step_entropy_drop`
- `entropy_priced_trace_floor`
- `evidence_permanent_flip_full_support_heat_positive`
- `evidence_permanent_flip_heat_floor`
- `evidence_permanent_flip_heat_positive`
- `evidence_permanent_flip_uniform_entropy_drop`
- `generalized_reachable_simulation_holds`
- `master_equation_does_not_fix_heat_scale`
- `mu_has_no_intrinsic_joule_value`
- `permanence_heat_floor_uses_landauer`
- `permanent_flip_full_support_entropy_drop_positive`
- `permanent_flip_full_support_heat_positive`
- `permanent_flip_heat_floor`
- `permanent_flip_heat_positive`
- `permanent_flip_uniform_entropy_drop`
- `permanent_step_entropy_ceiling`
- `permanent_step_entropy_drop`
- `selected_gap_gives_landauer_heat`
- `semantics_entropy_permutation_invariant`
- `smaller_gap_refutes_unconditional_landauer_floor`
