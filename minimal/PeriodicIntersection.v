(* SCOPE NOTE: standalone proof scope.
   Proves commutation and cancellation facts for periodic seeds and their retained rays.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import Arith Lia.
From Minimal Require Import CompleteHost.

Section Commuting.
Context {X:Type} (F G:X->X).
Hypothesis commute : forall s, F (G s)=G (F s).

Lemma F_G_power : forall n s, F (iter G n s)=iter G n (F s).
Proof.
  induction n; intro s; simpl; [reflexivity|].
  rewrite commute,IHn; reflexivity.
Qed.
Theorem powers_commute : forall n m s,
  iter F n (iter G m s)=iter G m (iter F n s).
Proof.
  induction n; intros m s; simpl; [reflexivity|].
  rewrite IHn,F_G_power; reflexivity.
Qed.

Variables a b:X.
Variables L M p q:nat.
Hypothesis p_positive : 0<p.
Hypothesis q_positive : 0<q.
Hypothesis a_periodic : iter G p a=a.
Hypothesis b_periodic : iter F q b=b.
Hypothesis F_distinct : forall i j, i<=L -> j<=L -> iter F i a=iter F j a -> i=j.
Hypothesis G_distinct : forall i j, i<=M -> j<=M -> iter G i b=iter G j b -> i=j.

Theorem crossing_periodicity : forall i j,
  iter F i a=iter G j b ->
  iter F (q+i) a=iter F i a /\ iter G (p+j) b=iter G j b.
Proof.
  intros i j E; split.
  - rewrite iter_add,E,powers_commute,b_periodic; reflexivity.
  - rewrite iter_add,<-E,<-powers_commute,a_periodic; reflexivity.
Qed.
Theorem crossing_only_in_tails : forall i j,
  i<=L -> j<=M -> iter F i a=iter G j b -> L<i+q /\ M<j+p.
Proof.
  intros i j Hi Hj E; destruct (crossing_periodicity i j E) as [EF EG].
  split.
  - destruct (le_dec (q+i) L).
    + pose proof (F_distinct (q+i) i l Hi EF); lia.
    + lia.
  - destruct (le_dec (p+j) M).
    + pose proof (G_distinct (p+j) j l Hj EG); lia.
    + lia.
Qed.

Theorem unit_period_crossing_is_joint_end : forall i j,
  p=1 -> q=1 -> i<=L -> j<=M -> iter F i a=iter G j b ->
  i=L /\ j=M /\ F (iter F i a)=iter F i a /\ G (iter G j b)=iter G j b.
Proof.
  intros i j Hp Hq Hi Hj E.
  destruct (crossing_only_in_tails i j Hi Hj E) as [I J].
  destruct (crossing_periodicity i j E) as [EF EG].
  subst p q; simpl in EF,EG; repeat split; auto; lia.
Qed.
End Commuting.

Lemma iterate_injective {X:Type} (F:X->X) :
  (forall a b, F a=F b -> a=b) ->
  forall n a b, iter F n a=iter F n b -> a=b.
Proof.
  intros H n; induction n; intros a b E; simpl in E.
  - exact E.
  - apply IHn; apply H; exact E.
Qed.

Theorem global_crossing_forces_periodic_seed {X:Type} (F G:X->X) :
  (forall s, F (G s)=G (F s)) ->
  (forall a b, F a=F b -> a=b) ->
  forall a b i j q, iter F q b=b -> iter F i a=iter G j b -> iter F q a=a.
Proof.
  intros C I a b i j q P E.
  apply (iterate_injective F I i).
  rewrite <-iter_add, (Nat.add_comm i q), iter_add, E.
  rewrite (powers_commute F G C q j b),P; reflexivity.
Qed.

Theorem population_arithmetic : forall T r s p q a b overlap,
  r<T -> s<T -> 0<p -> 0<q -> a=T-r -> b=T-s ->
  overlap<=p -> overlap<=q ->
  2*T+Nat.max p q <= (r+p)+(s+q)+(a+b-overlap).
Proof.
  intros; destruct (le_dec p q);
    [rewrite Nat.max_r by lia|rewrite Nat.max_l by lia]; lia.
Qed.
