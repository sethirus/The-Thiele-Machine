(** AxThieleComplete: every Thiele-complete machine, certified or not, is a
    Thiele machine.

    A certified Thiele-complete machine (minimal/ThieleComplete.v) is a
    two-place machine read through an interface with four clauses.  Clause
    (a) keeps the record up once it is up, clause (b) puts it down at every
    clean start, clause (c) prices every record move one, and clause (d)
    gives a claim that holds at some loaded start and a check, commit and
    certify that raise the record there.  Those are the toll, permanence
    and a distinction, so the machine meets the member predicate of
    AxThiele with its loaded starts as the designated starts.  The
    uncertified notion (minimal/NeutralComplete.v) has the same three in its
    base, start, price and distinction clauses, so it meets the predicate
    too.

    Results (all closed):

      machine_axsys_a2          a machine that obeys the toll is an axis
                                system over the two-point order that obeys
                                the axis toll.
      thiele_complete_is_member every certified Thiele-complete machine,
                                with its loaded starts designated, is a
                                Thiele machine.
      neutral_complete_is_member every Thiele-complete machine, with its
                                loaded starts designated, is a Thiele
                                machine.
      small_machine_is_member   the small machine, with its starts
                                designated, is a Thiele machine. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import AxCore AxThiele.
Require Minimal.ThieleComplete Minimal.NeutralComplete.
Module T := Minimal.ThieleComplete.
Module N := Minimal.NeutralComplete.

(** A two-place machine as an axis system over the two-point order. *)
Definition machine_axsys (M : T.machine) : AxSys bool two_pre :=
  mk_axsys bool two_pre (T.m_state M) (T.m_move M) (T.m_step M) (T.m_cost M) (T.m_record M).

Lemma machine_axsys_run : forall M tr s,
  ax_run (X := machine_axsys M) tr s = T.run M tr s.
Proof. intros M tr. induction tr; intros; simpl; auto. Qed.

(** The toll on a machine is the axis toll at the two-point order. *)
Theorem machine_axsys_a2 : forall M, T.obeys_toll M -> ax_a2 (X := machine_axsys M).
Proof.
  intros M H s i Hex. destruct (two_not_le _ _ Hex) as [H1 H0]. exact (H s i H0 H1).
Qed.

(** Every certified Thiele-complete machine is a Thiele machine, started at
    its loaded states. *)
Theorem thiele_complete_is_member : forall (M : T.machine) (I : T.thiele_interface M),
  T.thiele_complete_with I ->
  ax_thiele (machine_axsys M) (fun s => exists a b, s = T.load I a b).
Proof.
  intros M I HI.
  assert (Hw : T.weakly_thiele_complete M) by (apply T.thiele_complete_is_weak; exists I; exact HI).
  destruct HI as [[_ [Hclean [_ Hperm]]] [[Hdown _] [_ [c [chk [cmt [crt [_ [_ [_ [Hiff [[a [b Hm]] _]]]]]]]]]]]].
  unfold ax_thiele. repeat split.
  - exact (machine_axsys_a2 M (proj1 Hw)).
  - intros s i. apply (proj2 (two_le _ _)). simpl. apply Hperm.
  - exists (T.load I a b), [chk; cmt; crt]. split; [exists a, b; reflexivity |].
    intro H. pose proof (proj1 (two_le _ _) H) as H'.
    change (T.m_record M (T.run M [chk; cmt; crt] (T.load I a b)) = true ->
            T.m_record M (T.load I a b) = true) in H'.
    rewrite (Hdown _ (Hclean a b)) in H'.
    discriminate (H' (proj2 (Hiff a b) Hm)).
Qed.

(** Every Thiele-complete machine is a Thiele machine, started at its
    loaded states. *)
Theorem neutral_complete_is_member : forall (M : T.machine) (J : N.neutral_interface M),
  N.neutral_complete_with J ->
  ax_thiele (machine_axsys M) (fun s => exists a b, s = N.nload J a b).
Proof.
  intros M J HJ.
  assert (Hw : T.weakly_thiele_complete M) by (apply N.nc_is_weak; exists J; exact HJ).
  destruct HJ as [[_ [_ Hperm]] [Hstart [_ [tr [a [b [a' [b' [Hup _]]]]]]]]].
  unfold ax_thiele. repeat split.
  - exact (machine_axsys_a2 M (proj1 Hw)).
  - intros s i. apply (proj2 (two_le _ _)). simpl. apply Hperm.
  - exists (N.nload J a b), tr. split; [exists a, b; reflexivity |].
    intro H. pose proof (proj1 (two_le _ _) H) as H'.
    rewrite <- (machine_axsys_run M tr (N.nload J a b)) in Hup.
    simpl in H'. rewrite (Hstart a b) in H'. discriminate (H' Hup).
Qed.

(** The small machine is a Thiele machine. *)
Theorem small_machine_is_member :
  exists starts, ax_thiele (machine_axsys T.earned_machine) starts.
Proof.
  destruct T.earned_core_thiele_complete as [I HI].
  eexists. exact (thiele_complete_is_member T.earned_machine I HI).
Qed.

Print Assumptions machine_axsys_a2.
Print Assumptions thiele_complete_is_member.
Print Assumptions neutral_complete_is_member.
Print Assumptions small_machine_is_member.
