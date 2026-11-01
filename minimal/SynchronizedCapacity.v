(* SCOPE NOTE: standalone proof scope.
   Counts distinct configurations under synchronized first completion and layerwise injectivity.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List Arith Lia.
From Minimal Require Import CompleteHost.
Import ListNotations.

Lemma nodup_append_disjoint {A : Type} : forall xs ys : list A,
  NoDup xs -> NoDup ys -> (forall a, In a xs -> ~In a ys) -> NoDup (xs++ys).
Proof.
  intros xs; induction xs as [|x xs IH]; intros ys Hx Hy Hd; simpl; [exact Hy|].
  inversion Hx; subst; constructor.
  - rewrite in_app_iff; intro H; destruct H; [contradiction|].
    apply (Hd x); simpl; auto.
  - apply IH; auto. intros a Ha; apply Hd; simpl; auto.
Qed.
Lemma nodup_product {A B : Type} : forall xs:list A, forall ys:list B,
  NoDup xs -> NoDup ys -> NoDup (list_prod xs ys).
Proof.
  intros xs; induction xs as [|x xs IH]; intros ys Hx Hy; simpl; [constructor|].
  inversion Hx; subst; apply nodup_append_disjoint.
  - apply nodup_map_on; [exact Hy|]. intros a b Ha Hb H; injection H; auto.
  - apply IH; assumption.
  - intros [a b] Hin Hrest; apply in_map_iff in Hin as [c [He Hc]].
    injection He as He1 He2; subst a b.
    apply in_prod_iff in Hrest; tauto.
Qed.

Section Synchronized.
  Context {X : Type}.
  Variable F : X -> X.
  Variable starts : list X.
  Variable T : nat.
  Variable H : X -> Prop.
  Hypothesis distinct_starts : NoDup starts.
  Hypothesis not_early : forall a, In a starts -> forall n, n<T -> ~H(iter F n a).
  Hypothesis all_finish : forall a, In a starts -> H(iter F T a).
  (* Layerwise injectivity suffices here; unrestricted reversible dynamics
     without synchronized first completion does not give this conclusion. *)
  Hypothesis running_injective : forall n, n<T -> forall a b,
    In a starts -> In b starts ->
    F(iter F n a)=F(iter F n b) -> iter F n a=iter F n b.

  Lemma same_time_separated : forall n, n<=T -> forall a b,
    In a starts -> In b starts -> iter F n a=iter F n b -> a=b.
  Proof.
    induction n; intros Hn a b Ha Hb He; [exact He|].
    apply IHn; try lia; try assumption.
    apply running_injective; try lia; assumption.
  Qed.
  Lemma different_times_separated : forall i j a b,
    i<j -> j<=T -> In a starts -> In b starts ->
    iter F i a<>iter F j b.
  Proof.
    intros i j a b Hij Hj Ha Hb He.
    pose proof (f_equal (iter F (T-j)) He) as Hadvance.
    rewrite <- !iter_add in Hadvance.
    replace (T-j+j) with T in Hadvance by lia.
    apply (not_early a Ha (T-j+i)); [lia|].
    rewrite Hadvance; apply all_finish; exact Hb.
  Qed.
  Theorem spacetime_embedding_injective : forall i j a b,
    i<=T -> j<=T -> In a starts -> In b starts ->
    iter F i a=iter F j b -> i=j /\ a=b.
  Proof.
    intros i j a b Hi Hj Ha Hb He.
    assert (Hij:i=j).
    { destruct (Nat.lt_trichotomy i j) as [Hlt|[Heq|Hgt]]; [|exact Heq|].
      - exfalso; exact (different_times_separated i j a b Hlt Hj Ha Hb He).
      - exfalso; apply (different_times_separated j i b a Hgt Hi Hb Ha); symmetry; exact He. }
    subst j; split; [reflexivity|]. eapply same_time_separated; eauto.
  Qed.
  Definition run_population :=
    map (fun ta=>iter F (fst ta) (snd ta)) (list_prod (seq 0 (S T)) starts).
  Theorem synchronized_population_distinct : NoDup run_population.
  Proof.
    unfold run_population; apply nodup_map_on.
    - apply nodup_product; [apply seq_NoDup|exact distinct_starts].
    - intros [i a] [j b] Ha Hb He; simpl in He.
      apply in_prod_iff in Ha as [Hi Ha]; apply in_prod_iff in Hb as [Hj Hb].
      apply in_seq in Hi; apply in_seq in Hj.
      destruct (spacetime_embedding_injective i j a b) as [-> ->]; try lia; auto.
  Qed.
  Theorem synchronized_population_count : length run_population=length starts*(T+1).
  Proof.
    unfold run_population; rewrite map_length,prod_length,seq_length; lia.
  Qed.
  Theorem synchronized_capacity_bound : forall all,
    (forall a, In a starts -> forall n, n<=T -> In (iter F n a) all) ->
    length starts*(T+1)<=length all.
  Proof.
    intros all Hcover; rewrite <-synchronized_population_count.
    apply NoDup_incl_length; [apply synchronized_population_distinct|].
    intros s Hs; unfold run_population in Hs.
    apply in_map_iff in Hs as [[n a] [<- Hin]]; simpl.
    apply in_prod_iff in Hin as [Hn Ha]; apply in_seq in Hn.
    apply Hcover; auto; lia.
  Qed.
End Synchronized.
