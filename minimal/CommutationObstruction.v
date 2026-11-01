(* SCOPE NOTE: standalone proof scope.
   Proves finite retention obstructions for two commuting maps on an arbitrary carrier.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List Arith Lia.
Import ListNotations.

Section Obstruction.
Context {X:Type}.
Variable eq_dec : forall a b:X, {a=b}+{a<>b}.
Variables F G : X->X.
Variable v : X->nat.
Variables z a b : X.
Hypothesis vz : v z=0.
Hypothesis va : v a=1.
Hypothesis vb : v b=2.
Definition initials := [z;a;b].
Definition early s := In s initials \/ exists q, In q initials /\ (s=F q \/ s=G q).
Hypothesis Fi : forall s t, early s -> early t -> F s=F t -> s=t.
Hypothesis Gi : forall s t, early s -> early t -> G s=G t -> s=t.
Hypothesis commute : forall s, F (G s)=G (F s).
Hypothesis projectF : forall s, v (F s)=if Nat.eqb (v s) 2 then 2 else 0.
Hypothesis projectG : forall s, v (G s)=if Nat.eqb (v s) 1 then 1 else 0.

Lemma initial_early : forall s, In s initials -> early s.
Proof. intros; left; assumption. Qed.
Lemma F_early : forall s, In s initials -> early (F s).
Proof. intros; right; exists s; auto. Qed.
Lemma G_early : forall s, In s initials -> early (G s).
Proof. intros; right; exists s; auto. Qed.
Ltac early_tac := first
  [ solve [apply initial_early; unfold initials; simpl; auto]
  | solve [apply F_early; unfold initials; simpl; auto]
  | solve [apply G_early; unfold initials; simpl; auto] ].

Lemma three_zero_states : exists l, length l=3 /\ NoDup l /\
  (forall s, In s l -> v s=0).
Proof.
  assert (H0:v (F z)=0) by (rewrite projectF,vz; reflexivity).
  assert (H1:v (F a)=0) by (rewrite projectF,va; reflexivity).
  assert (Eza:z<>a) by (intro E; rewrite E,va in vz; discriminate).
  assert (E01:F z<>F a) by (intro E; apply Eza; apply Fi; auto; early_tac).
  assert (E0a:F z<>a) by (intro E; rewrite E,va in H0; discriminate).
  assert (E1a:F a<>a) by (intro E; rewrite E,va in H1; discriminate).
  assert (D01:F (F z)<>F (F a)) by (intro E; apply E01; apply Fi; auto; early_tac).
  assert (D0a:F (F z)<>F a) by (intro E; apply E0a; apply Fi; auto; early_tac).
  assert (D1a:F (F a)<>F a) by (intro E; apply E1a; apply Fi; auto; early_tac).
  assert (V0:v (F (F z))=0) by (rewrite projectF,H0; reflexivity).
  assert (V1:v (F (F a))=0) by (rewrite projectF,H1; reflexivity).
  exists [F (F z);F (F a);F a]; split; [reflexivity|]; split.
  - repeat constructor; simpl; intuition congruence.
  - intros s [E|[E|[E|E]]]; try contradiction; subst s; auto.
Qed.

Lemma four_zero_if_singletons :
  (forall s, v s=1 -> s=a) -> (forall s, v s=2 -> s=b) ->
  exists l, length l=4 /\ NoDup l /\ (forall s, In s l -> v s=0).
Proof.
  intros one two.
  assert (G_a:G a=a) by (apply one; rewrite projectG,va; reflexivity).
  assert (F_b:F b=b) by (apply two; rewrite projectF,vb; reflexivity).
  set (A:=F a); set (B:=G b); set (C:=F A); set (D:=G B).
  assert (vA:v A=0) by (unfold A; rewrite projectF,va; reflexivity).
  assert (vB:v B=0) by (unfold B; rewrite projectG,vb; reflexivity).
  assert (vC:v C=0) by (unfold C; rewrite projectF,vA; reflexivity).
  assert (vD:v D=0) by (unfold D; rewrite projectG,vB; reflexivity).
  assert (eA:early A) by (unfold A; early_tac).
  assert (eB:early B) by (unfold B; early_tac).
  assert (ea:early a) by early_tac.
  assert (eb:early b) by early_tac.
  assert (ez:early z) by early_tac.
  assert (aA:a<>A) by (intro E; rewrite E,vA in va; discriminate).
  assert (aB:a<>B) by (intro E; rewrite E,vB in va; discriminate).
  assert (bA:b<>A) by (intro E; rewrite E,vA in vb; discriminate).
  assert (bB:b<>B) by (intro E; rewrite E,vB in vb; discriminate).
  assert (GA:G A=A) by (unfold A; rewrite <-commute,G_a; reflexivity).
  assert (FB:F B=B) by (unfold B; rewrite commute,F_b; reflexivity).
  assert (GC:G C=C) by (unfold C; rewrite <-commute,GA; reflexivity).
  assert (FD:F D=D) by (unfold D; rewrite commute,FB; reflexivity).
  assert (AB:A<>B).
  { intro E; apply aB; apply Fi; auto; change (A=F B); rewrite FB; exact E. }
  assert (CA:C<>A).
  { intro E; apply aA; symmetry; apply Fi; auto; exact E. }
  assert (CB:C<>B).
  { intro E; apply AB; apply Fi; auto; rewrite FB; exact E. }
  assert (DA:D<>A).
  { intro E; apply AB; symmetry; apply Gi; auto; rewrite GA; exact E. }
  assert (DB:D<>B).
  { intro E; apply bB; symmetry; apply Gi; auto; exact E. }
  destruct (eq_dec C D) as [CD|CD].
  - assert (FC:F C=C) by (rewrite CD; exact FD).
    assert (zC:z<>C).
    { intro E; assert (early C) by (rewrite <-E; exact ez).
      apply CA; symmetry; apply Fi; auto; rewrite FC; reflexivity. }
    assert (zA:z<>A).
    { intro E; assert (early C) by (unfold C; rewrite <-E; early_tac).
      apply CB; symmetry; apply Gi; auto; rewrite GC; unfold D in CD; symmetry; exact CD. }
    assert (zB:z<>B).
    { intro E; assert (early D) by (unfold D; rewrite <-E; early_tac).
      assert (early C) by (rewrite CD; assumption).
      apply CA; symmetry; apply Fi; auto; rewrite FC; reflexivity. }
    exists [A;B;C;z]; split; [reflexivity|]; split.
    + repeat constructor; simpl; intuition congruence.
    + intros s [E|[E|[E|[E|E]]]]; try contradiction; subst s; auto.
  - exists [A;B;C;D]; split; [reflexivity|]; split.
    + repeat constructor; simpl; intuition congruence.
    + intros s [E|[E|[E|[E|E]]]]; try contradiction; subst s; auto.
Qed.

Variable carrier : list X.
Hypothesis covers : forall s, In s carrier.

Lemma add_sides : forall l, NoDup l -> (forall s, In s l -> v s=0) ->
  NoDup (a::b::l).
Proof.
  intros l H H0.
  assert (ab:a<>b) by (intro E; rewrite E,vb in va; discriminate).
  assert (~In a l) by (intro E; specialize (H0 a E); rewrite va in H0; discriminate).
  assert (~In b l) by (intro E; specialize (H0 b E); rewrite vb in H0; discriminate).
  repeat constructor; auto; simpl; intuition congruence.
Qed.
Lemma capacity_of_distinct : forall l:list X, NoDup l -> length l<=length carrier.
Proof. intros l H; apply NoDup_incl_length; auto; intros s _; apply covers. Qed.

Theorem unrestricted_exclusive_resets_need_five : 5<=length carrier.
Proof.
  destruct three_zero_states as [l [len [nd zeros]]].
  pose proof (capacity_of_distinct (a::b::l) (add_sides l nd zeros)).
  simpl in H; lia.
Qed.

Theorem commuting_exclusive_resets_need_six : 6<=length carrier.
Proof.
  destruct (three_zero_states) as [l [len [nd zeros]]].
  destruct (le_dec 6 (length carrier)); auto.
  assert (small:length carrier<6) by lia.
  assert (one:forall s, v s=1 -> s=a).
  { intros s vs; destruct (eq_dec s a); auto.
    assert (s<>b) by (intro E; rewrite E,vb in vs; discriminate).
    assert (~In s l) by (intro E; specialize (zeros s E); rewrite vs in zeros; discriminate).
    assert (NoDup (s::a::b::l)).
    { constructor; [simpl; intuition congruence|apply add_sides; auto]. }
    pose proof (capacity_of_distinct _ H1); simpl in H2; lia. }
  assert (two:forall s, v s=2 -> s=b).
  { intros s vs; destruct (eq_dec s b); auto.
    assert (s<>a) by (intro E; rewrite E,va in vs; discriminate).
    assert (~In s l) by (intro E; specialize (zeros s E); rewrite vs in zeros; discriminate).
    assert (NoDup (s::a::b::l)).
    { constructor; [simpl; intuition congruence|apply add_sides; auto]. }
    pose proof (capacity_of_distinct _ H1); simpl in H2; lia. }
  destruct (four_zero_if_singletons one two) as [q [q_len [q_nd q_zero]]].
  pose proof (capacity_of_distinct (a::b::q) (add_sides q q_nd q_zero)).
  simpl in H; lia.
Qed.
End Obstruction.
