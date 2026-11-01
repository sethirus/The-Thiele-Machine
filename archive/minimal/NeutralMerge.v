(** NeutralMerge.v: thm:record-merge-toll (2)-(4) for every
    neutral lift, with the base part = the box's state. *)
From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Import Minimal.FragmentSmall.
Require Import Minimal.RecordMerge.
Require Import Minimal.NeutralComplete.

Section M.
Variable M0 : machine.
Variable K : Type.
Variable E : K -> m_state M0 -> bool.

Definition nbase_part (s : nstate M0) : m_state M0 := fst (fst s).
Local Notation st := (nstep M0 K E).
Local Notation rec := (fun s : nstate M0 => snd (fst s)).

(* (1') a raising mark merges the state with its copy whose record is up. *)
Theorem nlift_raise_is_record_merge : forall s k,
  rec s = false -> rec (st s (NMark k)) = true -> record_merge st nbase_part (NMark k).
Proof.
  intros [[x r] l] k H0 H1. simpl in H0, H1. subst r. simpl in H1.
  exists (x, false, l), (x, true, l). split; [intro H; inversion H |].
  split; [reflexivity |]. simpl. rewrite H1. reflexivity.
Qed.

(* (3') no base move is a record-layer merge. *)
Theorem nlift_base_no_record_merge : forall b, ~ record_merge st nbase_part (NBase b).
Proof.
  intros b [[[x r] l] [[[x' r'] l'] [Hne [Hb Hs]]]]. unfold nbase_part in Hb. simpl in Hb, Hs. subst x'.
  injection Hs as Hr Hl. subst. apply Hne. reflexivity.
Qed.

(* So the lift's own prices meet record-layer merge pricing ... *)
Theorem nlift_record_priced : record_merges_priced st (ncost M0 K) nbase_part.
Proof.
  intros [b | k] Hm; simpl; [exfalso; exact (nlift_base_no_record_merge b Hm) | lia].
Qed.

(* (4') ... and every price list that meets it obeys the toll. *)
Theorem nlift_toll_from_record_price : forall cost' : nmove M0 K -> nat,
  record_merges_priced st cost' nbase_part ->
  forall s m, rec s = false -> rec (st s m) = true -> cost' m >= 1.
Proof.
  intros cost' H s [b | k] H0 H1.
  - destruct s as [[x r] l]. simpl in *. congruence.
  - apply H, (nlift_raise_is_record_merge s k H0 H1).
Qed.
End M.

Print Assumptions nlift_raise_is_record_merge.
Print Assumptions nlift_base_no_record_merge.
Print Assumptions nlift_record_priced.
Print Assumptions nlift_toll_from_record_price.
