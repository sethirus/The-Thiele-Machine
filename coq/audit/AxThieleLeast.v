(** AxThieleLeast: the least price list for the history lift.

    The history lift of AxThiele prices every move 1, the clock price, and
    that is enough for membership.  Over a finite base the least price
    list that obeys the toll is the one LeastToll builds: 1 on every move
    that can land on the lifted state x, 0 on every other move.  This file
    states the lift with any price list, shows the toll holds for it
    exactly when the list is at least that least list, and shows the lift
    with the least list is itself a member.

    Results (all closed):

      ax_a2_two_point_iff      the axis toll over the two-point order is
                               the no-to-yes toll of the cost comparison.
      lift_can_raise_iff       a move can raise the lift's bit exactly when
                               it can land on x from some state.
      lift_toll_iff_least      the toll holds for the lift priced by c
                               exactly when c is at least the least list.
      least_lift_is_thiele     the lift with the least list is a member
                               whenever some run from a start other than x
                               ends at x. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import AxCore AxThiele CostSemanticsComparison.
From Audit Require Import LeastToll.

(** The axis toll over the two-point order, read as the no-to-yes toll. *)
Lemma ax_a2_two_point_iff : forall (Y : AxSys bool two_pre),
  ax_a2 (X := Y) <->
  a2 (ax_state bool two_pre Y) (ax_instr bool two_pre Y) (ax_step bool two_pre Y)
     (ax_cost bool two_pre Y) (ax_rec bool two_pre Y).
Proof.
  intro Y. split.
  - intros Ha s i H0 H1. apply (Ha s i). unfold ax_exits, bp_le. rewrite H0, H1.
    simpl. discriminate.
  - intros Ha s i Hex. destruct (two_not_le _ _ Hex) as [H1 H0]. exact (Ha s i H0 H1).
Qed.

Section LeastLift.

Variable A : Type.
Variable P : BPre A.
Variable M : AxSys A P.
Variable eqb : ax_state A P M -> ax_state A P M -> bool.
Hypothesis eqb_eq : forall a b, eqb a b = true <-> a = b.
Variable x : ax_state A P M.
Variable all : list (ax_state A P M).
Hypothesis all_covers : forall s, In s all.

Local Notation L := (history_lift A P M eqb x).

(** The lifted states, listed. *)
Definition lift_states : list (ax_state A P M * bool) := list_prod all [false; true].

Lemma lift_states_cover : forall p : ax_state A P M * bool, In p lift_states.
Proof.
  intros [s b]. apply in_prod; [apply all_covers | destruct b; simpl; auto].
Qed.

(** The history lift with any price list on its moves. *)
Definition history_lift_priced (c : ax_instr A P M -> nat) : AxSys bool two_pre :=
  mk_axsys bool two_pre (ax_state A P M * bool) (ax_instr A P M)
    (ax_step bool two_pre L) c (ax_rec bool two_pre L).

(** One on every move that can land on x, zero elsewhere. *)
Definition lift_least_price : ax_instr A P M -> nat :=
  least_price (ax_step bool two_pre L) (ax_rec bool two_pre L) lift_states.

Theorem lift_can_raise_iff : forall i,
  can_raise (ax_step bool two_pre L) (ax_rec bool two_pre L) lift_states i = true <->
  exists s, ax_step A P M s i = x.
Proof.
  intro i.
  rewrite (can_raise_exact (ax_step bool two_pre L) (ax_rec bool two_pre L)
             lift_states lift_states_cover i).
  split.
  - intros [[s b] [H0 H1]]. simpl in H0, H1. subst b. simpl in H1.
    exists s. apply eqb_eq. exact H1.
  - intros [s Hs]. exists (s, false). simpl. split; [reflexivity |].
    apply eqb_eq. exact Hs.
Qed.

(** The toll holds for the priced lift exactly when the price list is at
    least the least list. *)
Theorem lift_toll_iff_least : forall c,
  ax_a2 (X := history_lift_priced c) <-> forall i, lift_least_price i <= c i.
Proof.
  intro c.
  pose proof (toll_exactly_dominates_least_price (ax_step bool two_pre L)
                (ax_rec bool two_pre L) lift_states lift_states_cover c) as T.
  pose proof (ax_a2_two_point_iff (history_lift_priced c)) as B. simpl in B.
  split.
  - intro H. apply T. apply B. exact H.
  - intro H. apply B. apply T. exact H.
Qed.

(** The lift with the least price list is a member. *)
Theorem least_lift_is_thiele : forall s0 tr,
  ax_run (X := M) tr s0 = x -> s0 <> x ->
  ax_thiele (history_lift_priced lift_least_price) (fun p => p = (s0, false)).
Proof.
  intros s0 tr Hrun Hne.
  destruct (history_lift_is_thiele A P M eqb eqb_eq x s0 tr Hrun Hne) as [_ [Hg Hd]].
  unfold ax_thiele. repeat split.
  - apply lift_toll_iff_least. intro i. apply le_n.
  - exact Hg.
  - destruct Hd as [s [tr' [Hs Hn]]]. exists s, tr'. split; [exact Hs |].
    exact Hn.
Qed.

End LeastLift.

Print Assumptions ax_a2_two_point_iff.
Print Assumptions lift_can_raise_iff.
Print Assumptions lift_toll_iff_least.
Print Assumptions least_lift_is_thiele.
