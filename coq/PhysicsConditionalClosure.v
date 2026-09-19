(** Conditional physical interpretation of the CHSH elliptope.

    The accounting results follow from VM execution. The quantum bound
    follows from existence of a PSD completion with free within-party cross
    moments. [A_QM] supplies the connection between a chosen experimental
    predicate and that completion model. The VM cost law does not supply
    this physical premise. *)

From Coq Require Import List Arith.PeanoNat Lia Reals Psatz.
Import ListNotations.
From Kernel Require Import VMState VMStep SimulationProof AbstractNoFI
  QuantitativeNoFI MinorConstraints NPAMomentMatrix TsirelsonGeneral
  MuLedgerQuantumBridge MuInitiality ElliptopeCompletion.
Local Open Scope R_scope.

Definition U1_classical_chsh_bound := fine_theorem.
Definition U2_no_free_certification := certification_requires_positive_mu.
Definition U3_trial_authenticity := chsh_trial_count_lower_bound.
Definition U4_cost_intrinsic := mu_accumulates_trace_cost.

Lemma semantics_run_vm_cost_invariant :
  forall (trace : list vm_instruction) (s : VMState),
    (exec_trace_from s trace).(vm_mu) = (s.(vm_mu) + trace_total_cost trace)%nat.
Proof.
  intros trace s. exact (mu_accumulates_trace_cost s trace).
Qed.

Theorem elliptope_tsirelson_bound_abs :
  forall E00 E01 E10 E11 : RealNumber,
    elliptope_realizable E00 E01 E10 E11 ->
    Rabs (CHSH E00 E01 E10 E11) <= sqrt8.
Proof.
  intros E00 E01 E10 E11 Hreal.
  pose proof (elliptope_tsirelson E00 E01 E10 E11 Hreal) as Hsq.
  rewrite <- (Rabs_right sqrt8); [| pose proof sqrt8_positive; lra].
  apply Rsqr_le_abs_0.
  unfold Rsqr at 2. rewrite sqrt8_squared.
  unfold CHSH, Rsqr. unfold ElliptopeCompletion.chsh_S in Hsq.
  exact Hsq.
Qed.

Definition U5_tsirelson_from_psd_completion := elliptope_tsirelson_bound_abs.

Section PhysicsBridge.
(* INQUISITOR NOTE: abstract interface section, an experimental interpretation and its PSD-completion premise. *)
Context (honest_quantum_chsh_correlations :
  RealNumber -> RealNumber -> RealNumber -> RealNumber -> Prop).
Context (A_QM :
  forall E00 E01 E10 E11 : RealNumber,
    honest_quantum_chsh_correlations E00 E01 E10 E11 ->
    elliptope_realizable E00 E01 E10 E11).

Theorem master_tsirelson_conditional :
  forall E00 E01 E10 E11 : RealNumber,
    honest_quantum_chsh_correlations E00 E01 E10 E11 ->
    Rabs (CHSH E00 E01 E10 E11) <= sqrt8.
Proof.
  intros E00 E01 E10 E11 Hhonest.
  apply elliptope_tsirelson_bound_abs.
  apply A_QM. exact Hhonest.
Qed.

Corollary master_supra_quantum_impossible :
  forall E00 E01 E10 E11 : RealNumber,
    honest_quantum_chsh_correlations E00 E01 E10 E11 ->
    ~ (Rabs (CHSH E00 E01 E10 E11) > sqrt8).
Proof.
  intros E00 E01 E10 E11 Hhonest Hcontra.
  pose proof (master_tsirelson_conditional E00 E01 E10 E11 Hhonest).
  lra.
Qed.
End PhysicsBridge.

(** The completion interpretation includes deterministic classical play. *)
Example completion_bridge_admits_classical_all_ones :
  Rabs (CHSH 1 1 1 1) <= sqrt8.
Proof.
  apply (master_tsirelson_conditional
    elliptope_realizable (fun _ _ _ _ H => H)).
  pose proof (deterministic_strategy_elliptope 1 1 1 1) as H.
  assert (Hone : 1 * 1 = 1) by ring.
  specialize (H Hone Hone Hone Hone). rewrite Hone in H. exact H.
Qed.
