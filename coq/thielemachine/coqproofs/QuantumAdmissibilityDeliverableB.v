From Coq Require Import QArith Lia.
From Coq Require Import Qring.
From Coq Require Import Lra.

From ThieleMachine Require Import BellInequality.
From ThieleMachine Require Import TsirelsonBoundBridge.
From ThieleMachine Require Import QuantumAdmissibilityTsirelson.

Open Scope Q_scope.

(** Deliverable B (Coq): “Tsirelson as a theorem of admissibility”.

    This file does three small, *checklist-aligned* things:

    B1. Names the admissible generator class at the measurement/box layer.
        (In this repo, the fully general trace->distribution bridge remains a
        separate milestone; this file is the exact, proof-carrying box layer.)

    B2. Re-exports the literal rational inequality already proven in
        [QuantumAdmissibilityTsirelson].

    B3. Provides a tightness witness (explicit rational gap to the kernel
        bound) and a simple contrapositive “supra-bound => non-admissible”.
*)

(** B1: admissible generator class (box/measurement layer). *)
Definition admissible_generator_box (B : Box) : Prop := quantum_admissible_box B.

(** B2: admissible => literal CHSH <= kernel Tsirelson bound. *)
Theorem admissible_generator_implies_CHSH_le_kernel_bound :
  forall B,
    admissible_generator_box B ->
    Qabs (S B) <= kernel_tsirelson_bound_q.
Proof.
  intros B Hadm.
  unfold admissible_generator_box in Hadm.
  apply quantum_admissible_implies_CHSH_le_tsirelson.
  exact Hadm.
Qed.

(** B3 (part 1): tightness/near-optimality witness.

    The concrete [TsirelsonApprox] box has
      Qabs(S) = 7071/2500
    while the kernel threshold is
      5657/2000.

    These differ by exactly 1/10000.
*)
Lemma TsirelsonApprox_gap_to_kernel_bound :
  kernel_tsirelson_bound_q - Qabs (S TsirelsonApprox) == (1#10000).
Proof.
  unfold kernel_tsirelson_bound_q.
  setoid_replace (Qabs (S TsirelsonApprox)) with ((4#1) * tsirelson_gamma)
    by exact TsirelsonApprox_Qabs.
  unfold tsirelson_gamma.
  ring.
Qed.

Corollary TsirelsonApprox_within_1_over_10000_of_kernel_bound :
  Qabs (S TsirelsonApprox) <= kernel_tsirelson_bound_q /\
  kernel_tsirelson_bound_q - (1#10000) <= Qabs (S TsirelsonApprox).
Proof.
  split.
  - apply TsirelsonApprox_Qabs_le_kernel_bound.
  - (* Rearrange the exact gap equation into a lower bound. *)
    pose proof TsirelsonApprox_gap_to_kernel_bound as Hgap.
    (* kernel_bound - Qabs(S) == 1/10000  ==> kernel_bound - 1/10000 == Qabs(S) *)
    assert (kernel_tsirelson_bound_q - (1#10000) == Qabs (S TsirelsonApprox)) as Heq.
    {
      (* Replace [1/10000] using the exact gap, then simplify by ring. *)
      setoid_replace (1#10000) with (kernel_tsirelson_bound_q - Qabs (S TsirelsonApprox))
        by (symmetry; exact Hgap).
      ring.
    }
    (* turn equality into <= *)
    setoid_replace (kernel_tsirelson_bound_q - (1#10000))
      with (Qabs (S TsirelsonApprox)) by exact Heq.
    apply Qle_refl.
Qed.

(** B3 (part 2): supra-bound => non-admissible (contrapositive of B2). *)
Corollary supra_kernel_bound_implies_not_admissible_generator :
  forall B,
    kernel_tsirelson_bound_q < Qabs (S B) ->
    ~ admissible_generator_box B.
Proof.
  intros B Hgt Hadm.
  pose proof (admissible_generator_implies_CHSH_le_kernel_bound B Hadm) as Hle.
  eapply Qlt_not_le; eauto.
Qed.
