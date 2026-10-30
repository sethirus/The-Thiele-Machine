(* Chapter twenty-one: receipts cover the merges a run shows. Charge each state the run leaves from;
   whenever two different states the run leaves from land together, one of them pays. Then the landings
   two different states of the run lead to, counted once each, are no more than the run's bill. *)
From Coq Require Import List Arith Lia.
Import ListNotations.

Section Receipts.
  Variable X : Type.
  Hypothesis eq_dec : forall a b : X, {a = b} + {a <> b}.
  Variable F : X -> X.
  Variable charge : X -> nat.
  Variable u : X.
  Variable L : nat.

  Fixpoint iter (t : nat) : X := match t with 0 => u | S k => F (iter k) end.
  Definition sources := map iter (seq 0 L).               (* the states the run leaves from *)
  Fixpoint sumc (l : list X) : nat := match l with [] => 0 | x :: r => charge x + sumc r end.
  Definition bill := sumc sources.                        (* every step taken is charged *)

  Hypothesis one_of_each_pair_pays : forall x y, In x sources -> In y sources -> x <> y ->
      F x = F y -> 1 <= charge x \/ 1 <= charge y.

  Definition D := nodup eq_dec sources.
  Definition lands_twice (y : X) : bool :=
    Nat.leb 2 (length (filter (fun x => if eq_dec (F x) y then true else false) D)).
  Definition marked := filter lands_twice (nodup eq_dec (map F D)).
  Definition paid := filter (fun x => Nat.leb 1 (charge x)) D.

  Lemma two_in_filter : forall (f : X -> bool) (l : list X), NoDup l -> 2 <= length (filter f l) ->
      exists x y, In x l /\ In y l /\ x <> y /\ f x = true /\ f y = true.
  Proof.
    intros f l Hl H. remember (filter f l) as k eqn:Ek.
    destruct k as [|x [|y k']]; simpl in H; try lia.
    assert (Hx : In x (filter f l)) by (rewrite <- Ek; left; reflexivity).
    assert (Hy : In y (filter f l)) by (rewrite <- Ek; right; left; reflexivity).
    assert (Nd : NoDup (filter f l)) by (apply NoDup_filter; exact Hl).
    rewrite <- Ek in Nd. inversion Nd; subst.
    apply filter_In in Hx as [Hx fx]. apply filter_In in Hy as [Hy fy].
    exists x, y. repeat split; auto. intro E; subst. apply H2. left. reflexivity.
  Qed.

  Lemma marked_in_paid_landings : incl marked (map F paid).
  Proof.
    intros y Hy. unfold marked in Hy. apply filter_In in Hy as [Hy Ht].
    unfold lands_twice in Ht. apply Nat.leb_le in Ht.
    destruct (two_in_filter _ D (NoDup_nodup eq_dec sources) Ht) as [x1 [x2 [H1 [H2 [Ne [F1 F2]]]]]].
    destruct (eq_dec (F x1) y) as [E1|]; [|discriminate]. destruct (eq_dec (F x2) y) as [E2|]; [|discriminate].
    apply nodup_In in H1. apply nodup_In in H2.
    destruct (one_of_each_pair_pays x1 x2 H1 H2 Ne (eq_trans E1 (eq_sym E2))) as [P | P].
    - apply in_map_iff. exists x1. split; [exact E1|]. apply filter_In. split; [apply nodup_In; exact H1 | apply Nat.leb_le; exact P].
    - apply in_map_iff. exists x2. split; [exact E2|]. apply filter_In. split; [apply nodup_In; exact H2 | apply Nat.leb_le; exact P].
  Qed.

  Lemma paid_le_sum : forall l : list X, length (filter (fun x => Nat.leb 1 (charge x)) l) <= sumc l.
  Proof.
    induction l as [|x r IH]; [simpl; lia|].
    cbn [filter]. destruct (Nat.leb 1 (charge x)) eqn:E.
    - cbn [length sumc]. apply Nat.leb_le in E. lia.
    - cbn [sumc]. lia.
  Qed.

  Lemma sumc_app : forall l1 l2 : list X, sumc (l1 ++ l2) = sumc l1 + sumc l2.
  Proof. induction l1 as [|b l1 IH]; intro l2; simpl; [reflexivity | rewrite IH; lia]. Qed.

  Lemma sum_sub : forall d s : list X, NoDup d -> incl d s -> sumc d <= sumc s.
  Proof.
    induction d as [|a d IH]; intros s Hd Hi; simpl; [lia|].
    inversion Hd; subst.
    assert (Ha : In a s) by (apply Hi; left; reflexivity).
    apply in_split in Ha as [l1 [l2 ->]].
    assert (Hs : sumc (l1 ++ a :: l2) = sumc l1 + charge a + sumc l2) by (rewrite sumc_app; simpl; lia).
    assert (Hs' : sumc (l1 ++ l2) = sumc l1 + sumc l2) by apply sumc_app.
    assert (Inc : incl d (l1 ++ l2)).
    { intros x Hx. assert (In x (l1 ++ a :: l2)) by (apply Hi; right; exact Hx).
      apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H | subst; contradiction | right; exact H]. }
    specialize (IH (l1 ++ l2) H2 Inc). lia.
  Qed.

  Theorem receipts_cover_merges : length marked <= bill.
  Proof.
    assert (Nm : NoDup marked) by (apply NoDup_filter, NoDup_nodup).
    pose proof (NoDup_incl_length Nm marked_in_paid_landings) as A.
    rewrite map_length in A. unfold paid in A.
    pose proof (paid_le_sum D) as B.
    pose proof (sum_sub D sources (NoDup_nodup eq_dec sources) (fun x H => proj1 (nodup_In eq_dec sources x) H)) as C.
    unfold bill. lia.
  Qed.
End Receipts.

Print Assumptions receipts_cover_merges.
