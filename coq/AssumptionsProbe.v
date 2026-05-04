(** Assumptions audit probe — runs Print Assumptions against the consequential
    top-level claims in [Kernel.MasterSummary]. Output is captured by coqc and
    pinned to artifacts/print_assumptions_master_summary.txt.

    This file is a probe, not a proof obligation. It produces no theorems and
    is excluded from the canonical _CoqProject build. *)

From Kernel Require Import MasterSummary.

(* ============================================================
   Assumption-surface meta-claims
   ============================================================ *)
Print Assumptions master_summary_project_local_axioms_count_zero.
Print Assumptions master_summary_project_local_admits_count_zero.
Print Assumptions master_summary_no_hidden_project_assumptions_verified.
Print Assumptions master_assumption_artifact_path_pinned.
Print Assumptions master_assumption_artifact_sha256_pinned.
Print Assumptions master_assumption_artifact_is_pinned.
Print Assumptions master_assumption_boundary_explicit.

(* ============================================================
   Mu-cost / classical / quantum
   ============================================================ *)
Print Assumptions master_mu_zero_witness_sound.
Print Assumptions master_mu_zero_algebraic_bound.
Print Assumptions master_classical_bound.
Print Assumptions master_quantum_violation_proves_nonclassicality.
Print Assumptions master_algebraic_tsirelson.
Print Assumptions master_algebraic_tsirelson_tight.
Print Assumptions master_quantum_foundations.
Print Assumptions master_tsirelson_conditional.

(* ============================================================
   Non-circularity sub-certificates
   ============================================================ *)
Print Assumptions master_non_circularity.
Print Assumptions master_non_circular_mu_cost_primitives.
Print Assumptions master_non_circular_chsh_formula.
Print Assumptions master_non_circular_classical_witness.
Print Assumptions master_non_circular_mu_zero_locc.

(* ============================================================
   PSD / column-contractive / trace / quantum-model bridge
   ============================================================ *)
Print Assumptions master_psd_iff_column_contractive.
Print Assumptions master_trace_column_contractive_iff_quantum_model.
Print Assumptions master_trace_quantum_model_unfolds.
Print Assumptions master_trace_quantum_bridge_forces_psd.

(* ============================================================
   Honest NoFI surface
   ============================================================ *)
Print Assumptions master_honest_nofi_structure_requirement.
Print Assumptions master_honest_nofi_trace_separation.
Print Assumptions master_honest_nofi_conditional_shannon.
Print Assumptions master_honest_nofi_quantitative_state_space.
Print Assumptions master_honest_nofi_posterior_representative_reduction.

(* ============================================================
   NoFI -> discrete Einstein
   ============================================================ *)
Print Assumptions master_nofi_to_discrete_einstein.
Print Assumptions master_nofi_to_discrete_einstein_from_bekenstein_calibration.

(* ============================================================
   Verification chain (Coq <-> Python <-> hardware)
   ============================================================ *)
Print Assumptions master_verification_chain.
Print Assumptions master_verification_preserved_observables.

(* ============================================================
   Exposed audit-facing surfaces
   ============================================================ *)
Print Assumptions exposed_zero_marginal_psd_contractivity.
Print Assumptions exposed_trace_bridge_content.
Print Assumptions exposed_non_circularity_content.
Print Assumptions exposed_verification_surface_content.
Print Assumptions exposed_honest_nofi_structure_content.

(* ============================================================
   Top-level "machine is complete" bundle
   ============================================================ *)
Print Assumptions thiele_machine_core_summary_verified.
Print Assumptions thiele_machine_is_complete.
