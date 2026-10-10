(** CzFollow: nesting pays for every rise, on every host run that follows
    the guest.

    CzCat.v proves two things about a simulation f of a guest X in a host Y
    whose record map reflects the order, when Y pays the toll:

      cmpz_sim_exit_cost       for EVERY host list of moves that carries the
                               image of a guest state to the image of its
                               successor, a guest move that leaves the
                               down-set of its record costs the host at least
                               1;
      cmpz_sim_cost_ge_exits   over a guest run, SOME host list of moves
                               reaching the image of the end state costs at
                               least the guest's number of exits.

    This file closes the gap between the two.

      cmpz_follows             a host run follows a guest run when it splits
                               into one segment per guest move, each carrying
                               the image of the state before that move to the
                               image of the state after it.
      cmpz_follow_exists       every guest run has a host run that follows it
                               (from the simulation clause of the morphism).
      cmpz_follow_reaches      a host run that follows a guest run ends on the
                               image of the guest's end state.
      cmpz_follow_cost_ge_exits
                               EVERY host run that follows a guest run costs
                               at least the guest's number of exits.
      cmpz_end_only_not_enough
                               the universal statement fails for host runs
                               that only reach the image of the end state: a
                               guest that rises and comes back has one exit,
                               and the empty host run reaches its end image
                               for nothing. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import AxCore AxComplete CzProd CzCat.

Section Follow.

Context {X Y : cmpz_obj}.
Variable f : cmpz_hom X Y.

(** A host run, given as one segment per guest move, follows a guest run. *)
Fixpoint cmpz_follows (tr : list (am_move (ob_M X))) (s : am_state (ob_M X))
    (segs : list (list (am_move (ob_M Y)))) : Prop :=
  match tr, segs with
  | [], [] => True
  | m :: tr', seg :: segs' =>
      h_state f (am_step (ob_M X) s m) = am_run (ob_M Y) seg (h_state f s) /\
      cmpz_follows tr' (am_step (ob_M X) s m) segs'
  | _, _ => False
  end.

Theorem cmpz_follow_exists : forall tr s, exists segs, cmpz_follows tr s segs.
Proof.
  induction tr as [| m tr IH]; intro s.
  - exists []. exact I.
  - destruct (h_sim f s m) as [seg Hseg].
    destruct (IH (am_step (ob_M X) s m)) as [segs Hsegs].
    exists (seg :: segs). split; assumption.
Qed.

Theorem cmpz_follow_reaches : forall tr s segs, cmpz_follows tr s segs ->
  h_state f (am_run (ob_M X) tr s) = am_run (ob_M Y) (concat segs) (h_state f s).
Proof.
  induction tr as [| m tr IH]; intros s [| seg segs] H; simpl in H; try contradiction.
  - reflexivity.
  - destruct H as [Hseg Hrest]. rewrite am_run_cons. simpl.
    rewrite am_run_app, <- Hseg. apply IH. exact Hrest.
Qed.

Theorem cmpz_follow_cost_ge_exits :
  (forall a b, bp_le (ob_P Y) (h_rec f a) (h_rec f b) -> bp_le (ob_P X) a b) ->
  ax_a2 (X := am_axsys (ob_M Y)) ->
  forall tr s segs, cmpz_follows tr s segs ->
    cmpz_cost (ob_M Y) (concat segs) >= cmpz_exit_count (ob_M X) tr s.
Proof.
  intros Hemb Ha. induction tr as [| m tr IH]; intros s [| seg segs] H;
    simpl in H; try contradiction.
  - unfold cmpz_exit_count. simpl. lia.
  - destruct H as [Hseg Hrest]. simpl. rewrite cmpz_cost_app.
    specialize (IH _ _ Hrest). unfold cmpz_exit_count in *. simpl.
    destruct (bp_leb (ob_A X) (ob_P X) (am_rec (ob_M X) (am_step (ob_M X) s m))
                (am_rec (ob_M X) s)) eqn:E.
    + lia.
    + assert (Hex : ax_exits (X := am_axsys (ob_M X)) s m)
        by (unfold ax_exits, bp_le; simpl; rewrite E; discriminate).
      pose proof (cmpz_sim_exit_cost f Hemb Ha s m seg Hseg Hex). lia.
Qed.

End Follow.

(** * Reaching the end image is not enough *)

(** A machine on one bit, ordered false below true, whose move b sets the
    bit to b; setting it to true costs 1, setting it to false costs 0. *)
Definition cmpz_bit_machine : amachine bool two_pre :=
  mk_am bool two_pre bool bool (fun _ b => b) (fun b => if b then 1 else 0) (fun s => s).

Definition cmpz_bit : cmpz_obj := mk_obj bool two_pre cmpz_bit_machine.

Lemma cmpz_bit_a2 : ax_a2 (X := am_axsys (ob_M cmpz_bit)).
Proof.
  intros s b Hex. unfold ax_exits, bp_le in Hex. simpl in Hex.
  destruct s, b; simpl in *; try lia; exfalso; apply Hex; reflexivity.
Qed.

Theorem cmpz_end_only_not_enough :
  exists (X Y : cmpz_obj) (f : cmpz_hom X Y),
    (forall a b, bp_le (ob_P Y) (h_rec f a) (h_rec f b) -> bp_le (ob_P X) a b) /\
    ax_a2 (X := am_axsys (ob_M Y)) /\
    exists (tr : list (am_move (ob_M X))) s (tr' : list (am_move (ob_M Y))),
      h_state f (am_run (ob_M X) tr s) = am_run (ob_M Y) tr' (h_state f s) /\
      cmpz_cost (ob_M Y) tr' < cmpz_exit_count (ob_M X) tr s.
Proof.
  exists cmpz_bit, cmpz_bit, (cmpz_hom_id cmpz_bit).
  split; [intros a b H; exact H |].
  split; [exact cmpz_bit_a2 |].
  exists [true; false], false, []. split.
  - reflexivity.
  - unfold cmpz_exit_count, cmpz_cost. simpl. lia.
Qed.

Print Assumptions cmpz_follow_exists.
Print Assumptions cmpz_follow_reaches.
Print Assumptions cmpz_follow_cost_ge_exits.
Print Assumptions cmpz_end_only_not_enough.
