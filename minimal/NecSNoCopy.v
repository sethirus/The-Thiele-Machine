(** NecSNoCopy.v: "No host fact on an exact copy of the guest's counter"
    (UniversalNoCopy.v) pushed to its limit.

    - The finite list Q is necessary. A host whose property language is the
      guest's own (PZero, PEven, PGe n for every n), with the identity as
      translation, meets every other hypothesis; no two different guest
      properties PGe n, PGe m share a host property, no finite list holds
      every translated property, and the host pair
      CHECK (PGe n) R; COMMIT (PGe m) R traps from every clean host start,
      exactly as the guest pair does. So with an infinite Q the obstacle
      disappears.
    - The soundness of the translation (the host check passes whenever the
      guest check passes) is necessary for the "host passes" half: a host
      whose checker never passes fails the host CHECK.
    - The guest check of PGe n on A passes exactly when A is at least n,
      so "a register holding a number at least n" is exact for the guest
      half.                                                              *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedCore.
Require Minimal.EarnedMulti.
Require Import Minimal.UniversalNoCopy.
Module C := Minimal.EarnedCore.
Module M := Minimal.EarnedMulti.

Lemma nec_s_prop_eqb_eq : forall p q, C.prop_eqb p q = true <-> p = q.
Proof.
  intros [| | n] [| | m]; simpl; split; intro H; try discriminate; try reflexivity.
  - apply Nat.eqb_eq in H. subst. reflexivity.
  - injection H as ->. apply Nat.eqb_refl.
Qed.

(* ================================================================= *)
(* 1. With an infinite property list the collision disappears.        *)
(* ================================================================= *)

(* The translation id meets the soundness hypothesis. *)
Lemma nec_s_id_sound : forall p v, C.eval p v = true -> C.eval (id p) v = true.
Proof. auto. Qed.

(* No collision. *)
Lemma nec_s_id_no_collision : forall n m, n <> m -> id (C.PGe n) <> id (C.PGe m).
Proof. intros n m H E. injection E. exact H. Qed.

(* No finite list holds every translated property. *)
Lemma nec_s_id_not_finite : forall Q : list C.prop, ~ (forall p, In (id p) Q).
Proof.
  intros Q HQ.
  apply (pigeonhole_not_injective C.prop Q (fun n => C.PGe n)).
  - intro n. apply HQ.
  - intros n m E. injection E. auto.
Qed.

(* The host pair traps from every clean host start, like the guest pair. *)
Lemma nec_s_id_host_pair_traps : forall n m (R : nat) (vs : nat -> nat),
  n <> m ->
  M.err (M.core_of (M.run C.prop_eqb C.eval
                     [M.CHECK (C.PGe n) R; M.COMMIT (C.PGe m) R] (M.start vs))) = true.
Proof.
  intros n m R vs Hnm.
  assert (Hmn : Nat.eqb m n = false) by (apply Nat.eqb_neq; auto).
  cbn. unfold M.check_ok. cbn.
  destruct (Nat.leb n (vs R)); cbn.
  - unfold M.commit_ok, M.fact_eqb. cbn. rewrite Hmn. reflexivity.
  - reflexivity.
Qed.

Theorem nec_s_nocopy_needs_finite_Q :
  (forall p v, C.eval p v = true -> C.eval (id p) v = true) /\
  (forall Q : list C.prop, ~ (forall p, In (id p) Q)) /\
  ~ (exists n m, n <> m /\ id (C.PGe n) = id (C.PGe m)) /\
  (forall n m (R : nat) (vs : nat -> nat), n <> m ->
     M.err (M.core_of (M.run C.prop_eqb C.eval
                        [M.CHECK (C.PGe n) R; M.COMMIT (C.PGe m) R] (M.start vs))) = true /\
     (forall a b, C.err (C.core_of (C.run_prog 2 (guest n m) (C.start a b))) = true)).
Proof.
  split; [exact nec_s_id_sound |]. split; [exact nec_s_id_not_finite |]. split.
  - intros [n [m [Hnm E]]]. exact (nec_s_id_no_collision n m Hnm E).
  - intros n m R vs Hnm. split; [apply nec_s_id_host_pair_traps; exact Hnm |].
    intros a b. apply guest_traps. exact Hnm.
Qed.

(* ================================================================= *)
(* 2. The soundness of the translation is needed.                     *)
(* ================================================================= *)

Definition nec_s_never (p : unit) (v : nat) : bool := false.

Theorem nec_s_nocopy_needs_sound_translation :
  forall (R : nat) (vs : nat -> nat),
  M.err (M.core_of (M.run (fun _ _ : unit => true) nec_s_never
                     [M.CHECK tt R; M.COMMIT tt R] (M.start vs))) = true /\
  ~ (forall p v, C.eval p v = true -> nec_s_never ((fun _ => tt) p) v = true).
Proof.
  intros R vs. split; [reflexivity |].
  intro H. specialize (H (C.PGe 0) 0 eq_refl). discriminate.
Qed.

(* ================================================================= *)
(* 3. "At least n" is exact for the guest's check.                    *)
(* ================================================================= *)

Theorem nec_s_guest_check_passes_iff : forall n m a b,
  C.err (C.core_of (C.run_prog 1 (guest n m) (C.start a b))) = false <-> n <= a.
Proof.
  intros n m a b. split; [| apply guest_check_passes].
  cbn. unfold C.check_ok. cbn.
  destruct (Nat.leb n a) eqn:H; cbn; intro E; [apply Nat.leb_le; exact H | discriminate].
Qed.

Print Assumptions nec_s_prop_eqb_eq.
Print Assumptions nec_s_nocopy_needs_finite_Q.
Print Assumptions nec_s_nocopy_needs_sound_translation.
Print Assumptions nec_s_guest_check_passes_iff.
