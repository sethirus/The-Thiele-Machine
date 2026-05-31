(** * verify_zero_admits: assumption-surface report

    This file is a reporting script wrapped around [Print Assumptions].
    It enumerates the live theorems cited by the paper and the master
    summary, so the visible assumption surface stays inspectable rather
    than implicit.

    The expected output is not uniformly empty: standard-library facts
    (functional extensionality, classical reals, etc.) reach into the
    proofs from below. The contract is narrower — the script exposes
    exactly what the assumption surface is, and any newly introduced
    project-local axiom or [Admitted] would show up here immediately. *)

From Kernel Require Import NoFreeInsight KernelPhysics MuLedgerConservation.
From Kernel Require Import RevelationRequirement.
From Kernel Require Import EntropyImpossibility.
From Kernel Require Import ProperSubsumption.
From Kernel Require Import HonestNoFI HonestNoFI_TheoremsWithoutAssumptions.
From Kernel Require Import MuShannonBridge MuShannonQuantitative StateSpaceCounting.
From Kernel Require Import QuantumPartitionPSD.
From Kernel Require Import QuantumPartitionPSD_1AB.
From Kernel Require Import A2LoadBearing.
From Kernel Require Import CommitmentVsErasure.
From Kernel Require Import CommitmentPredicateAdequacy.
From Kernel Require Import CommitmentCostDecomposition.
From Kernel Require Import A2Payoff.
From Kernel Require Import MasterSummary.

(** Master-summary audit hooks. *)

(* Theorem: master summary asserts no project-local axioms or admits. *)
Print Assumptions master_summary_no_hidden_project_assumptions_verified.

(* Theorem: verification transfer surface is narrowed to explicit observables. *)
Print Assumptions master_verification_preserved_observables.

(* Theorem: non-circularity is decomposed into inspectable sub-certificates. *)
Print Assumptions master_non_circular_mu_cost_primitives.

(** Observational no-signaling checks. *)

(* Theorem: Operations on one module cannot affect observables of unrelated modules *)
Print Assumptions observational_no_signaling.

(** Gauge-symmetry checks. *)

(* The former probe [kernel_conservation_mu_gauge] was inlined; its
   transparency is captured at use sites. *)

(* Theorem: Gauge actions compose correctly *)
Print Assumptions nat_action_composition.

(** No Free Insight checks. *)

(* Main Theorem: Strengthening predicates requires structure addition *)
Print Assumptions NoFreeInsight.strengthening_requires_structure_addition.

(** Revelation-requirement checks. *)

(* Theorem: Supra-quantum certification requires revelation events *)
Print Assumptions RevelationProof.nonlocal_correlation_requires_revelation.

(** ** μ-conservation, monotonicity, and irreversibility checks *)

(* Theorem: Single-step μ-monotonicity *)
Print Assumptions mu_conservation_kernel.

(* Theorem: Multi-step μ-monotonicity *)
Print Assumptions run_vm_mu_monotonic.

(* Theorem: Irreversibility lower bound *)
Print Assumptions vm_irreversible_bits_lower_bound.

(** Honest NoFI and Shannon quantitative checks. *)

(* Theorem: honest_information_reduction_requires_structure_addition *)
Print Assumptions honest_information_reduction_requires_structure_addition.

(* Theorem: honest_nfi_trace_separation_partial *)
Print Assumptions honest_nfi_trace_separation_partial.

(* Theorem: honest_nfi_general_feasible_reduction_partial *)
Print Assumptions honest_nfi_general_feasible_reduction_partial.

(* Theorem: honest_nfi_fibered_feasible_reduction_partial *)
Print Assumptions honest_nfi_fibered_feasible_reduction_partial.

(* Theorem: honest_nfi_posterior_representative_reduction_partial *)
Print Assumptions honest_nfi_posterior_representative_reduction_partial.

(* Theorem: honest_nfi_conditional_shannon_partial *)
Print Assumptions honest_nfi_conditional_shannon_partial.

(* Theorem: honest_nfi_quantitative_state_space_partial *)
Print Assumptions honest_nfi_quantitative_state_space_partial.

(* Theorem: Separation requires cert count (Shannon quantitative lower bound) *)
Print Assumptions MuShannonQuantitative.separation_requires_cert_count.

(* Theorem: Conditional Shannon bound — cert executions bound delta-mu *)
Print Assumptions MuShannonQuantitative.conditional_shannon_bound.

(* Theorem: General feasible-set reduction bound under explicit tree-cover hypothesis *)
Print Assumptions MuShannonBridge.info_priced_arbitrary_feasible_reduction_bound.

(* Theorem: Fibered feasible-set reduction bound deriving tree cover from a structured witness *)
Print Assumptions MuShannonBridge.info_priced_fibered_feasible_reduction_bound.

(* Theorem: Posterior-representative reduction bound deriving fibers from observation-equivalent representatives *)
Print Assumptions MuShannonBridge.info_priced_posterior_representative_reduction_bound.

(* Theorem: Conservative state-space counting wrapper *)
Print Assumptions StateSpaceCounting.no_free_insight_quantitative.

(* Summary export: conservative state-space-counting wrapper in the master theorem index *)
Print Assumptions master_honest_nofi_quantitative_state_space.

(** ** Region-equivalence and quantum-bridge checks *)

(* Theorem: Region equivalence classes are infinite *)
Print Assumptions region_equiv_class_infinite.

(** The key algebraic closure theorem: PSD of the NPA moment matrix is
    equivalent to column contractivity ([zero_marginal_column_contractive]).
    This closes the bidirectional bridge between quantum realizability
    and the algebraic Tsirelson bound. *)

(* Theorem: NPA PSD → column contractive (reverse direction) *)
Print Assumptions npa_psd_implies_column_contractive.

(* Theorem: NPA PSD ↔ column contractive (biconditional) *)
Print Assumptions npa_psd_iff_column_contractive.

(* Corollary: column contractive ↔ quantum realizable *)
Print Assumptions column_contractive_iff_quantum_realizable.

(* Theorem: trace column contractive ↔ trace quantum model *)
Print Assumptions trace_column_contractive_iff_trace_quantum_model.

(* Summary export: PSD ↔ column contractive in the master theorem index *)
Print Assumptions master_psd_iff_column_contractive.

(* Summary export: coherent trace bridge forces PSD of the extracted NPA matrix *)
Print Assumptions master_trace_quantum_bridge_forces_psd.

(** Q_{1+AB} extension audit (Section 9 of QuantumPartitionPSD_1AB.v).

    These check that the new 9×9 NPA Q_{1+AB} bridge theorems —
    extending the Q_1 (5×5) characterization to the next NPA level
    via the bipartite operator set {I, A_i, B_j, A_i B_j} — close
    under the same standard-library assumption surface as the rest
    of the kernel. The final composed theorem is conditional on
    Ishizaka 2025 (arXiv:2502.10746); the conditional surfaces as
    a Coq hypothesis, not as an axiom. *)

(* Theorem: 9×9 NPA Q_{1+AB} moment matrix is symmetric by construction. *)
Print Assumptions q1ab_moment_matrix_symmetric.

(* Theorem: PSD9 ↔ column_contractive at level 1+AB (full biconditional). *)
Print Assumptions q1ab_psd_iff_column_contractive.

(* Corollary: column_contractive_q1ab ↔ quantum_realizable_q1ab. *)
Print Assumptions column_contractive_q1ab_iff_quantum_realizable.

(* Theorem: integer-arithmetic check at γ = 0 implies the real-valued predicate. *)
Print Assumptions column_contractive_check_q1ab_sound_at_g_zero.

(* Theorem: kernel bridge from CHSH_LASSERT + sum_E check to Q_{1+AB} PSD. *)
Print Assumptions chsh_lassert_no_trap_with_sum_E_check_implies_q1ab_psd.

(* Theorem: kernel bridge wraps to quantum_realizable_q1ab. *)
Print Assumptions chsh_lassert_no_trap_with_sum_E_check_implies_quantum_realizable_q1ab.

(* Diagnostic: γ = 0 check forces correlators inside the unit ball
   (strictly stronger than the classical bound |S| ≤ 2). *)
Print Assumptions q1ab_check_at_gzero_forces_unit_ball.

(* Diagnostic corollary: γ = 0 check implies the classical |S| ≤ 2 bound. *)
Print Assumptions q1ab_check_at_gzero_implies_classical_bound.

(* Re-exported bridge: γ-parameterized real-valued column-contractivity ⟹ PSD9. *)
Print Assumptions q1ab_caller_supplied_gamma_real_check_implies_psd9.

(* New ISA opcode bridge: instr_chsh_lassert_1ab no-trap ⟹ PSD9 (γ=0). *)
Print Assumptions chsh_lassert_1ab_no_trap_implies_q1ab_psd.

(* New ISA opcode bridge wrapped as quantum_realizable_q1ab. *)
Print Assumptions chsh_lassert_1ab_no_trap_implies_quantum_realizable_q1ab.

(** ** A2 load-bearing separation *)

(* Lemma: A2 forces a positive cost on the certifying single-step trace. *)
Print Assumptions trace_A_mu_ge_1_via_A2.

(* Theorem: cost ledger is not classically observable, with A2 as the
   load-bearing step in the proof. *)
Print Assumptions vm_mu_not_classically_determined_via_A2.

(* Counterfactual: without A2, the cost-ledger separation collapses. *)
Print Assumptions cf_no_cost_separation.

(* Lemma: every cert_addr-setter instruction has instruction_cost >= 1
   (the static, instruction-only form of A2 for the cert_addr channel). *)
Print Assumptions thiele_info_pricing_holds.

(* Lemma: total trace cost dominates the sum of cert-setter costs. *)
Print Assumptions cs_total_cost_ge_cert_setter_sum.

(* Theorem: for any n-way certified-distinguishability problem on the
   substrate's cert_addr channel, total substrate cost is at least n.
   Exceeds the Shannon information-theoretic minimum log_2(n) by factor
   n / log_2(n). *)
Print Assumptions nway_separation_substrate_cost_ge_n.

(* Lemma: a single-step LASSERT trace increases mu by at least
   formula-bits + 1.  (Bit-scaling from LASSERT cost rule, +1 from A2.) *)
Print Assumptions lassert_mu_increase_ge_bits_plus_one.

(* Theorem: LASSERT-based certification of a B-bit formula has substrate
   mu-cost at least B + 1, exceeding classical unit-cost RAM time (1 step
   per instruction) by factor B + 1. *)
Print Assumptions lassert_substrate_mu_exceeds_unit_cost.

(* Theorem: A2 contributes exactly +1 to the LASSERT cost bound; without
   A2 the bound drops by 1, exhibiting a strict separation at B = 0. *)
Print Assumptions a2_contributes_exact_plus_one_to_lassert_bound.

(** ** Commitment versus erasure, equal-trust separation *)

(* Theorem: trusted erasure accounting can certify at zero cost when no
   erasure occurs, while trusted A2 accounting forbids zero-cost
   certification. *)
Print Assumptions commitment_cost_not_reducible_to_erasure_cost.

(** ** A2 substitution gate *)

(* Theorem: under predicate-only pricing, a local substitute predicate
   yields a universal certification-cost floor iff it covers every
   cert-flip step. *)
Print Assumptions local_predicate_certification_floor_iff_covers_cert_flips.

(* Theorem: the quantitative trace cost lower-bounds the number of
   certification commitments iff the priced predicate contains A2. *)
Print Assumptions quantitative_floor_iff_a2_predicate_subsumed.
Print Assumptions quantitative_certification_floor_iff_covers_cert_flips.

(* Theorem: every batch of certifying runs costs at least one unit per
   run iff the priced predicate contains A2. *)
Print Assumptions batch_certification_floor_iff_a2_predicate_subsumed.

(* Theorem: if a pricing law gets the commitment lower bound and does
   not overcharge beyond commitments, then it is exactly A2 with unit
   pricing; conversely, exact unit A2 pricing has both properties. *)
Print Assumptions exact_commitment_pricing_characterization.
Print Assumptions substitution_test_rejects_non_a2_exact_substitute.
Print Assumptions substitution_test_exact_substitute_is_a2.

(* Theorem: the cert-flip predicate is the least adequate predicate;
   any substitute that gets the certification floor must contain A2. *)
Print Assumptions cert_flip_is_least_covering_predicate.
Print Assumptions universal_floor_forces_a2_predicate_subsumed.

(* Theorem: erasure accounting is not an adequate substitute when
   certification can happen without erasure. *)
Print Assumptions erasure_substitute_fails_commitment_floor.

(* Theorem: the cert-flip predicate itself has the commitment floor. *)
Print Assumptions a2_predicate_has_commitment_floor.
Print Assumptions a2_predicate_has_quantitative_floor.

(* Theorem: in a decomposed total-cost model, total cost equals
   background cost plus certification commitments iff the commitment
   component is exactly A2; the VM instruction-cost schedule has this
   decomposition for vm_certified. *)
Print Assumptions dcs_exact_total_cost_formula_iff.
Print Assumptions dcs_substitution_test_rejects_non_a2_exact_component.
Print Assumptions dcs_exact_component_substitute_is_a2.
Print Assumptions vm_instruction_cost_exactly_background_plus_cert_commitments.

(* Packaged theorem: equal-trust erasure separation, quantitative
   substitution gate, batch/n-way gate, and exact-pricing
   characterization, plus the decomposed-cost VM instantiation. *)
Print Assumptions a2_equal_trust_substitution_payoff.


(** ** Subsumption theorems *)

(* Theorem: Thiele simulates Turing exactly *)
Print Assumptions ProperSubsumption.thiele_simulates_turing.

(* Theorem: Cost certificates are valid *)
Print Assumptions ProperSubsumption.cost_certificate_valid.

(* Main Theorem: Thiele strictly extends Turing *)
Print Assumptions ProperSubsumption.thiele_strictly_extends_turing.

(** ** Structural connectivity anchor

    A trivial lemma whose [let _ := ...] preamble forces every cited
    theorem to type-check. Its job is to give this audit script at
    least one proof symbol with dependencies on the production kernel,
    so the dependency graph carries it. The conclusion [1 <> 0] is a
    placeholder; what matters is that all the names in scope refer to
    real, [Qed]-closed theorems. *)
Lemma zero_admit_connectivity_check :
  let _ := mu_conservation_kernel in
  let _ := run_vm_mu_monotonic in
  let _ := observational_no_signaling in
  let _ := vm_irreversible_bits_lower_bound in
  let _ := NoFreeInsight.strengthening_requires_structure_addition in
  let _ := RevelationProof.nonlocal_correlation_requires_revelation in
  1 <> 0.
Proof.
  discriminate.
Qed.

(** ** Verification summary

    If every [Print Assumptions] above reports either
    [Closed under the global context] or only standard-library
    assumptions (e.g. functional extensionality, classical reals,
    [propositional_extensionality]), then:

      - No [Admitted] proofs are reachable from the cited theorems.
      - No project-local axioms have been introduced.
      - The standard-library reach is explicit rather than implicit.
      - Every paper theorem is fully machine-checked. *)
