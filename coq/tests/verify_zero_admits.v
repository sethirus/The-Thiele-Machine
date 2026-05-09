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

(* Theorem: Partition structure is invariant under μ-gauge shifts *)
Print Assumptions kernel_conservation_mu_gauge.

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

