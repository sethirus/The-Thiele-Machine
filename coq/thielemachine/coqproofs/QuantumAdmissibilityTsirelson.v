From Coq Require Import QArith Lia.

From ThieleMachine Require Import BellInequality.
From ThieleMachine Require Import TsirelsonBoundBridge.

Open Scope Q_scope.

(** Literal CHSH ≤ Tsirelson bound (machine-level, not certification-level).

    We define an *admissible generator class* at the box/measurement layer:

    - Any local box is admissible (classical / LHV).
    - The concrete [TsirelsonApprox] box is admissible (quantum-optimal up to a
      rational approximation).

    For this class, we prove the direct inequality:

      quantum_admissible_box B -> Qabs (S B) <= 5657/2000.
*)

Definition quantum_admissible_box (B : Box) : Prop :=
  local B \/ B = TsirelsonApprox.

(** [two_le_kernel_tsirelson_bound]: formal specification. *)
Lemma two_le_kernel_tsirelson_bound :
  (2#1) <= kernel_tsirelson_bound_q.
Proof.
  unfold kernel_tsirelson_bound_q.
  unfold Qle. simpl. lia.
Qed.

(** [quantum_admissible_implies_CHSH_le_tsirelson]: formal specification. *)
Theorem quantum_admissible_implies_CHSH_le_tsirelson :
  forall B,
    quantum_admissible_box B ->
    Qabs (S B) <= kernel_tsirelson_bound_q.
Proof.
  intros B Hadm.
  destruct Hadm as [Hlocal | Heq].
  - (* Local boxes obey the classical CHSH bound ≤ 2, hence ≤ Tsirelson. *)
    pose proof (local_CHSH_bound B Hlocal) as H2.
    eapply Qle_trans; [exact H2 |].
    apply two_le_kernel_tsirelson_bound.
  - subst B.
    apply TsirelsonApprox_Qabs_le_kernel_bound.
Qed.
