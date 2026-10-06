(** CzProd: the interleaved product of two axis machines.

    Two machines run side by side.  A move of the product is a move of the
    left machine or a move of the right machine, and it acts on its own
    component only.  The record of the product is the pair of the two
    records, in the product order: a pair is below another when both
    coordinates are.

    Why the product order and no other.  The toll watches the record leave
    the down-set of where it stood.  In the product order the down-set of a
    pair is the product of the two down-sets, so a step leaves it exactly
    when it leaves the down-set of the coordinate it moved
    ([cmpz_exits_inl_iff], [cmpz_exits_inr_iff]).  Every certification of
    either part is therefore a certification of the whole, none is merged
    with the other, and every threshold of either part is a threshold of the
    whole.

    Results (all closed):

      cmpz_run_prod          a run of the product is the pair of the runs of
                             the two projections of its trace;
      cmpz_cost_prod         the cost of a trace is the cost of its left
                             part plus the cost of its right part;
      cmpz_exit_count_prod   so is the number of steps that leave the
                             down-set;
      cmpz_prod_a2_iff       the product pays the toll exactly when both
                             parts do;
      cmpz_prod_floor        the cost floor holds for the product;
      cmpz_prod_exit_cost    the cost of a run is at least the number of
                             its exits, over both parts together.

    Everything in this file is about the move structure and the order; it
    uses no property of the machines beyond their shape. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import AxCore.
From Kernel Require Import AxLatch.
From Kernel Require Import AxComplete.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

(** * The product order *)

Definition cmpz_pair_pre {A B} (P : BPre A) (Q : BPre B) : BPre (A * B).
Proof.
  refine {| bp_leb := fun x y => andb (bp_leb A P (fst x) (fst y)) (bp_leb B Q (snd x) (snd y)) |}.
  - intros [a b]. simpl. rewrite !bp_refl. reflexivity.
  - intros [a b] [c d] [e f]. simpl. rewrite !andb_true_iff. intros [H1 H2] [H3 H4].
    split; eapply bp_trans; eauto.
Defined.

Lemma cmpz_pair_le : forall {A B} (P : BPre A) (Q : BPre B) (x y : A * B),
  bp_le (cmpz_pair_pre P Q) x y <-> bp_le P (fst x) (fst y) /\ bp_le Q (snd x) (snd y).
Proof.
  intros A B P Q x y. unfold bp_le. simpl. rewrite andb_true_iff. tauto.
Qed.

(** Antisymmetry passes to the product. *)
Lemma cmpz_pair_antisym : forall {A B} (P : BPre A) (Q : BPre B),
  bp_antisym P -> bp_antisym Q -> bp_antisym (cmpz_pair_pre P Q).
Proof.
  intros A B P Q HP HQ [a b] [c d] H1 H2.
  apply cmpz_pair_le in H1. apply cmpz_pair_le in H2. simpl in *.
  f_equal; [apply HP | apply HQ]; tauto.
Qed.

(** * The two projections of an interleaved trace *)

Fixpoint cmpz_lefts {X Y : Type} (l : list (X + Y)) : list X :=
  match l with
  | [] => []
  | inl x :: r => x :: cmpz_lefts r
  | inr _ :: r => cmpz_lefts r
  end.

Fixpoint cmpz_rights {X Y : Type} (l : list (X + Y)) : list Y :=
  match l with
  | [] => []
  | inl _ :: r => cmpz_rights r
  | inr y :: r => y :: cmpz_rights r
  end.

Lemma cmpz_lefts_app : forall {X Y} (l1 l2 : list (X + Y)),
  cmpz_lefts (l1 ++ l2) = cmpz_lefts l1 ++ cmpz_lefts l2.
Proof. induction l1 as [| [x | y] l1 IH]; intro l2; simpl; auto; rewrite IH; reflexivity. Qed.

Lemma cmpz_rights_app : forall {X Y} (l1 l2 : list (X + Y)),
  cmpz_rights (l1 ++ l2) = cmpz_rights l1 ++ cmpz_rights l2.
Proof. induction l1 as [| [x | y] l1 IH]; intro l2; simpl; auto; rewrite IH; reflexivity. Qed.

(** A decomposition of the left projection lifts to the whole trace. *)
Lemma cmpz_lefts_split : forall {X Y} (l : list (X + Y)) (l1 : list X) x l2,
  cmpz_lefts l = l1 ++ x :: l2 ->
  exists t1 t2, l = t1 ++ inl x :: t2 /\ cmpz_lefts t1 = l1 /\ cmpz_lefts t2 = l2.
Proof.
  intros X Y l. induction l as [| [a | b] r IH]; intros l1 x l2 H.
  - simpl in H. destruct l1; discriminate.
  - simpl in H. destruct l1 as [| c l1'].
    + simpl in H. injection H as <- <-. exists [], r. simpl. auto.
    + simpl in H. injection H as <- H.
      destruct (IH l1' x l2 H) as [t1 [t2 [E [E1 E2]]]].
      exists (inl a :: t1), t2. simpl. rewrite E, E1. auto.
  - simpl in H. destruct (IH l1 x l2 H) as [t1 [t2 [E [E1 E2]]]].
    exists (inr b :: t1), t2. simpl. rewrite E, E2, E1. auto.
Qed.

Lemma cmpz_rights_split : forall {X Y} (l : list (X + Y)) (l1 : list Y) y l2,
  cmpz_rights l = l1 ++ y :: l2 ->
  exists t1 t2, l = t1 ++ inr y :: t2 /\ cmpz_rights t1 = l1 /\ cmpz_rights t2 = l2.
Proof.
  intros X Y l. induction l as [| [a | b] r IH]; intros l1 y l2 H.
  - simpl in H. destruct l1; discriminate.
  - simpl in H. destruct (IH l1 y l2 H) as [t1 [t2 [E [E1 E2]]]].
    exists (inl a :: t1), t2. simpl. rewrite E, E1, E2. auto.
  - simpl in H. destruct l1 as [| c l1'].
    + simpl in H. injection H as <- <-. exists [], r. simpl. auto.
    + simpl in H. injection H as <- H.
      destruct (IH l1' y l2 H) as [t1 [t2 [E [E1 E2]]]].
      exists (inr b :: t1), t2. simpl. rewrite E, E1. auto.
Qed.

(** * The product machine *)

Section Prod.

Context {A B : Type} {P : BPre A} {Q : BPre B}.
Variable M : amachine A P.
Variable N : amachine B Q.

Definition cmpz_prod : amachine (A * B) (cmpz_pair_pre P Q) :=
  mk_am (A * B) (cmpz_pair_pre P Q)
    (am_state M * am_state N) (am_move M + am_move N)
    (fun s m => match m with
                | inl x => (am_step M (fst s) x, snd s)
                | inr y => (fst s, am_step N (snd s) y)
                end)
    (fun m => match m with inl x => am_cost M x | inr y => am_cost N y end)
    (fun s => (am_rec M (fst s), am_rec N (snd s))).

Lemma cmpz_run_prod : forall tr s,
  am_run cmpz_prod tr s
    = (am_run M (cmpz_lefts tr) (fst s), am_run N (cmpz_rights tr) (snd s)).
Proof.
  induction tr as [| [x | y] tr IH]; intro s.
  - destruct s. reflexivity.
  - rewrite am_run_cons. simpl am_step. rewrite IH. simpl cmpz_lefts. simpl cmpz_rights.
    rewrite am_run_cons. reflexivity.
  - rewrite am_run_cons. simpl am_step. rewrite IH. simpl cmpz_lefts. simpl cmpz_rights.
    rewrite am_run_cons. reflexivity.
Qed.

Lemma cmpz_run_prod_fst : forall tr s,
  fst (am_run cmpz_prod tr s) = am_run M (cmpz_lefts tr) (fst s).
Proof. intros. rewrite cmpz_run_prod. reflexivity. Qed.

Lemma cmpz_run_prod_snd : forall tr s,
  snd (am_run cmpz_prod tr s) = am_run N (cmpz_rights tr) (snd s).
Proof. intros. rewrite cmpz_run_prod. reflexivity. Qed.

Lemma cmpz_rec_prod : forall s, am_rec cmpz_prod s = (am_rec M (fst s), am_rec N (snd s)).
Proof. reflexivity. Qed.

(** ** Cost *)

Definition cmpz_cost {A' : Type} {P' : BPre A'} (X : amachine A' P') (tr : list (am_move X)) : nat :=
  fold_right (fun m n => am_cost X m + n) 0 tr.

Lemma cmpz_cost_app : forall {A' P'} (X : amachine A' P') l1 l2,
  cmpz_cost X (l1 ++ l2) = cmpz_cost X l1 + cmpz_cost X l2.
Proof. intros A' P' X. induction l1; intro l2; simpl; [auto | rewrite IHl1; lia]. Qed.

(** The cost of an interleaved trace is the cost of its two projections. *)
Theorem cmpz_cost_prod : forall tr,
  cmpz_cost cmpz_prod tr = cmpz_cost M (cmpz_lefts tr) + cmpz_cost N (cmpz_rights tr).
Proof.
  induction tr as [| [x | y] tr IH]; [reflexivity | |].
  - change (am_cost M x + cmpz_cost cmpz_prod tr
            = am_cost M x + cmpz_cost M (cmpz_lefts tr) + cmpz_cost N (cmpz_rights tr)).
    rewrite IH. lia.
  - change (am_cost N y + cmpz_cost cmpz_prod tr
            = cmpz_cost M (cmpz_lefts tr) + (am_cost N y + cmpz_cost N (cmpz_rights tr))).
    rewrite IH. lia.
Qed.

(** ** Exits *)

Definition cmpz_exit_count {A' : Type} {P' : BPre A'} (X : amachine A' P')
    (tr : list (am_move X)) (s : am_state X) : nat :=
  ax_exit_count (X := am_axsys X) tr s.

Lemma cmpz_exits_inl_iff : forall s x,
  ax_exits (X := am_axsys cmpz_prod) s (inl x) <-> ax_exits (X := am_axsys M) (fst s) x.
Proof.
  intros s x. unfold ax_exits. simpl. rewrite cmpz_pair_le. simpl.
  split; intros H H'.
  - apply H. split; [exact H' | apply bp_le_refl].
  - apply H. exact (proj1 H').
Qed.

Lemma cmpz_exits_inr_iff : forall s y,
  ax_exits (X := am_axsys cmpz_prod) s (inr y) <-> ax_exits (X := am_axsys N) (snd s) y.
Proof.
  intros s y. unfold ax_exits. simpl. rewrite cmpz_pair_le. simpl.
  split; intros H H'.
  - apply H. split; [apply bp_le_refl | exact H'].
  - apply H. exact (proj2 H').
Qed.

Theorem cmpz_exit_count_prod : forall tr s,
  cmpz_exit_count cmpz_prod tr s
    = cmpz_exit_count M (cmpz_lefts tr) (fst s) + cmpz_exit_count N (cmpz_rights tr) (snd s).
Proof.
  induction tr as [| [x | y] tr IH]; intro s.
  - reflexivity.
  - unfold cmpz_exit_count in *. simpl. rewrite IH. simpl.
    assert (Hb : bp_leb (A * B) (cmpz_pair_pre P Q)
                  (am_rec cmpz_prod (am_step cmpz_prod s (inl x))) (am_rec cmpz_prod s)
                = bp_leb A P (am_rec M (am_step M (fst s) x)) (am_rec M (fst s))).
    { simpl. rewrite bp_refl, andb_true_r. reflexivity. }
    simpl in Hb. rewrite Hb. destruct (bp_leb A P _ _); simpl; lia.
  - unfold cmpz_exit_count in *. simpl. rewrite IH. simpl.
    assert (Hb : bp_leb (A * B) (cmpz_pair_pre P Q)
                  (am_rec cmpz_prod (am_step cmpz_prod s (inr y))) (am_rec cmpz_prod s)
                = bp_leb B Q (am_rec N (am_step N (snd s) y)) (am_rec N (snd s))).
    { simpl. rewrite bp_refl, andb_true_l. reflexivity. }
    simpl in Hb. rewrite Hb. destruct (bp_leb B Q _ _); simpl; lia.
Qed.

(** ** The toll *)

Theorem cmpz_prod_a2_if : ax_a2 (X := am_axsys M) -> ax_a2 (X := am_axsys N) ->
  ax_a2 (X := am_axsys cmpz_prod).
Proof.
  intros HM HN s [x | y] Hex.
  - apply cmpz_exits_inl_iff in Hex. exact (HM _ _ Hex).
  - apply cmpz_exits_inr_iff in Hex. exact (HN _ _ Hex).
Qed.

(** Conversely, each part pays its toll when the product does: the other
    component is any state at all. *)
Theorem cmpz_prod_a2_only_if : ax_a2 (X := am_axsys cmpz_prod) ->
  forall (t : am_state N) (s : am_state M), ax_a2 (X := am_axsys M).
Proof.
  intros H t s s' x Hex. apply (H (s', t) (inl x)).
  apply cmpz_exits_inl_iff. exact Hex.
Qed.

Theorem cmpz_prod_a2_only_if_right : ax_a2 (X := am_axsys cmpz_prod) ->
  forall (s : am_state M), ax_a2 (X := am_axsys N).
Proof.
  intros H s t y Hex. apply (H (s, t) (inr y)).
  apply cmpz_exits_inr_iff. exact Hex.
Qed.

Theorem cmpz_prod_a2_iff : forall (s : am_state M) (t : am_state N),
  ax_a2 (X := am_axsys cmpz_prod) <->
  ax_a2 (X := am_axsys M) /\ ax_a2 (X := am_axsys N).
Proof.
  intros s t. split.
  - intro H. split; [exact (cmpz_prod_a2_only_if H t s) | exact (cmpz_prod_a2_only_if_right H s)].
  - intros [HM HN]. apply cmpz_prod_a2_if; assumption.
Qed.

(** ** The cost of a run is at least its exits, over both parts together. *)
Theorem cmpz_prod_exit_cost :
  ax_a2 (X := am_axsys M) -> ax_a2 (X := am_axsys N) ->
  forall tr s, cmpz_cost cmpz_prod tr >= cmpz_exit_count cmpz_prod tr s.
Proof.
  intros HM HN tr s. rewrite cmpz_cost_prod, cmpz_exit_count_prod.
  assert (Hc : forall {A' P'} (X : amachine A' P'), ax_a2 (X := am_axsys X) ->
            forall tr s, cmpz_cost X tr >= cmpz_exit_count X tr s).
  { intros A' P' X HX tr0. induction tr0 as [| m tr0 IH]; intro s0; simpl.
    - lia.
    - unfold cmpz_exit_count in *. simpl.
      specialize (IH (am_step X s0 m)).
      destruct (bp_leb A' P' (am_rec X (am_step X s0 m)) (am_rec X s0)) eqn:E; [lia |].
      assert (Hex : ax_exits (X := am_axsys X) s0 m)
        by (unfold ax_exits, bp_le; simpl; rewrite E; discriminate).
      specialize (HX s0 m Hex). simpl in HX. unfold cmpz_cost in *. lia. }
  pose proof (Hc _ _ M HM (cmpz_lefts tr) (fst s)).
  pose proof (Hc _ _ N HN (cmpz_rights tr) (snd s)). lia.
Qed.

(** The cost floor, for the product. *)
Theorem cmpz_prod_floor : ax_a2 (X := am_axsys M) -> ax_a2 (X := am_axsys N) ->
  ax_floor (X := am_axsys cmpz_prod).
Proof.
  intros HM HN. apply (proj2 (ax_floor_iff_a2 (am_axsys cmpz_prod))).
  apply cmpz_prod_a2_if; assumption.
Qed.

End Prod.

Arguments cmpz_prod {A B P Q} M N.
Arguments cmpz_cost {A' P'} X tr.
Arguments cmpz_exit_count {A' P'} X tr s.

Print Assumptions cmpz_run_prod.
Print Assumptions cmpz_cost_prod.
Print Assumptions cmpz_exit_count_prod.
Print Assumptions cmpz_prod_a2_iff.
Print Assumptions cmpz_prod_exit_cost.
Print Assumptions cmpz_prod_floor.
Print Assumptions cmpz_lefts_split.
