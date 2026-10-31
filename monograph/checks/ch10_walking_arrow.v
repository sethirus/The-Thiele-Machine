(* SCOPE NOTE: standalone proof scope. A short check written beside the book: it states its own
   machine, prices and conditions as hypotheses and uses only the Coq standard library, so it
   does not import the foundation chain. *)
(* Chapter ten: laying a machine's moves onto the walking arrow (NO and YES, a loop on each, one arrow
   from NO to YES and nothing back) is exactly a split that no move crosses from YES to NO. Laying them
   onto two dots with no arrow is exactly a split no move crosses at all. *)
From Coq Require Import Bool.

Section WalkingArrow.
  Variable S : Type.
  Variable step : S -> S -> Prop.          (* the machine's moves, any relation *)
  Variable side : S -> bool.               (* false = NO, true = YES *)

  (* the walking arrow's allowed arrows: NO->NO, NO->YES, YES->YES *)
  Definition arrow (a b : bool) : Prop := a = false \/ b = true.
  (* two dots, loops only *)
  Definition plain (a b : bool) : Prop := a = b.

  Definition lays_on (R : bool -> bool -> Prop) := forall x y, step x y -> R (side x) (side y).

  Theorem walking_arrow_is_one_way_split :
    lays_on arrow <-> (forall x y, step x y -> side x = true -> side y = true).
  Proof.
    unfold lays_on, arrow. split.
    - intros H x y Hs Hx. destruct (H x y Hs) as [E | E]; [congruence | exact E].
    - intros H x y Hs. destruct (side x) eqn:Ex.
      + right. apply (H x y Hs Ex).
      + left. reflexivity.
  Qed.

  Theorem plain_dots_is_closed_split :
    lays_on plain <-> (forall x y, step x y -> side x = side y).
  Proof. unfold lays_on, plain. tauto. Qed.
End WalkingArrow.

Print Assumptions walking_arrow_is_one_way_split.
Print Assumptions plain_dots_is_closed_split.

(* Chapter ten: an order is a sorting with one-way doors. For any preorder ("at or below", reflexive and
   transitive), "each at or below the other" is a sameness that sorts the pile, it respects the order,
   and between different buckets "at or below" goes only one way. *)
Section Doors.
  Variable A : Type.
  Variable le : A -> A -> Prop.
  Hypothesis le_refl : forall x, le x x.
  Hypothesis le_trans : forall x y z, le x y -> le y z -> le x z.
  Definition same x y := le x y /\ le y x.

  Theorem same_is_a_sameness :
    (forall x, same x x) /\ (forall x y, same x y -> same y x) /\
    (forall x y z, same x y -> same y z -> same x z).
  Proof. unfold same. repeat split; intros; firstorder eauto. Qed.

  Theorem order_respects_buckets : forall x x' y y', same x x' -> same y y' -> le x y -> le x' y'.
  Proof. unfold same. intros x x' y y' [_ H1] [H2 _] H. eauto. Qed.

  Theorem doors_go_one_way : forall x y, le x y -> ~ same x y -> ~ le y x.
  Proof. unfold same. intros x y H N H'. apply N. split; assumption. Qed.
End Doors.

Print Assumptions same_is_a_sameness.
Print Assumptions doors_go_one_way.
