(* SCOPE NOTE: standalone proof scope.
   Counts distinct alternatives in layers of arbitrary total-map executions.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List ListDec Arith Lia.
From Minimal Require Import CompleteHost Multiplicity.
Import ListNotations.

Section Ensemble.
  Context {X : Type}.
  Variable eq_dec : forall a b : X, {a=b}+{a<>b}.
  Variable F : X -> X.
  Variable starts : list X.
  Hypothesis starts_distinct : NoDup starts.

  Fixpoint layer n : list X :=
    match n with 0=>starts | S k=>nodup eq_dec (map F (layer k)) end.
  Definition size n := length (layer n).
  Definition loss n := size n-size (S n).
  Fixpoint total_loss n := match n with 0=>0 | S k=>total_loss k+loss k end.

  Lemma layer_distinct : forall n, NoDup (layer n).
  Proof. destruct n; simpl; [exact starts_distinct|apply NoDup_nodup]. Qed.
  Lemma layer_image : forall n s, In s (layer n) <->
    exists a, In a starts /\ s=iter F n a.
  Proof.
    induction n; intro s; simpl.
    - split; [intro H; exists s; auto|intros [a [Ha ->]]; exact Ha].
    - rewrite nodup_In,in_map_iff; split.
      + intros [b [Hb Hbin]]; apply IHn in Hbin as [a [Ha ->]].
        exists a; split; [exact Ha|symmetry; exact Hb].
      + intros [a [Ha ->]]; exists (iter F n a); split; [reflexivity|].
        apply IHn; exists a; auto.
  Qed.
  Lemma size_nonincreasing : forall n, size (S n)<=size n.
  Proof.
    intro n; unfold size; simpl.
    pose proof (NoDup_incl_length (NoDup_nodup eq_dec (map F (layer n)))
      (fun s Hs => proj1 (nodup_In eq_dec (map F (layer n)) s) Hs)) as H.
    rewrite map_length in H; exact H.
  Qed.
  Theorem exact_loss_telescopes : forall T,
    total_loss T+size T=length starts.
  Proof.
    induction T; [reflexivity|].
    change (total_loss T+loss T+size (S T)=length starts).
    unfold loss; pose proof (size_nonincreasing T); lia.
  Qed.
  Lemma final_capacity : forall T held,
    (forall a, In a starts -> In (iter F T a) held) -> size T<=length held.
  Proof.
    intros T held H; unfold size; apply NoDup_incl_length; [apply layer_distinct|].
    intros s Hs; apply layer_image in Hs as [a [Ha ->]]; apply H; exact Ha.
  Qed.
  Theorem ensemble_loss_bound : forall T held,
    (forall a, In a starts -> In (iter F T a) held) ->
    length starts<=total_loss T+length held.
  Proof.
    intros T held H; pose proof (exact_loss_telescopes T).
    pose proof (final_capacity T held H); lia.
  Qed.

  Lemma drop_witness : forall xs,
    NoDup xs -> length (nodup eq_dec (map F xs))<length xs ->
    exists a b, In a xs /\ In b xs /\ a<>b /\ F a=F b.
  Proof.
    intros xs Hnd Hdrop.
    set (bad:=fun ab:X*X => fst ab<>snd ab /\ F(fst ab)=F(snd ab)).
    assert (Hd:forall ab,{bad ab}+{~bad ab}).
    { intros [a b]; unfold bad; simpl; destruct (eq_dec a b);
        destruct (eq_dec (F a) (F b)); intuition. }
    destruct (Exists_dec bad (list_prod xs xs) Hd) as [Hex|Hnone].
    - apply Exists_exists in Hex as [[a b] [Hin Hb]].
      apply in_prod_iff in Hin; exists a,b; unfold bad in Hb; simpl in Hb; tauto.
    - assert (Hinj:forall a b, In a xs -> In b xs -> F a=F b -> a=b).
      { intros a b Ha Hb He; destruct (eq_dec a b); [assumption|].
        exfalso; apply Hnone; apply Exists_exists; exists (a,b); split.
        - apply in_prod_iff; auto.
        - unfold bad; simpl; auto. }
      assert (Hmap:NoDup (map F xs)) by (apply nodup_map_on; assumption).
      rewrite nodup_fixed_point, map_length in Hdrop by exact Hmap; lia.
  Qed.
  Lemma decrease_time : forall T, size T<length starts ->
    exists t, t<T /\ size (S t)<size t.
  Proof.
    induction T; intro H; [unfold size in H; simpl in H; lia|].
    destruct (lt_dec (size (S T)) (size T)) as [Hd|Hd].
    - exists T; split; auto.
    - destruct IHT as [t [Ht He]]; [lia|exists t; split; auto; lia].
  Qed.
  Theorem execution_collision_before_deadline : forall T held,
    (forall a, In a starts -> In (iter F T a) held) ->
    length held<length starts ->
    exists t a b, t<T /\ In a (layer t) /\ In b (layer t) /\ a<>b /\ F a=F b.
  Proof.
    intros T held Hends Hsmall.
    pose proof (final_capacity T held Hends) as Hcap.
    destruct (decrease_time T) as [t [Ht Hd]]; [lia|].
    unfold size in Hd; simpl in Hd.
    destruct (drop_witness (layer t) (layer_distinct t) Hd) as [a [b Hab]].
    exists t,a,b; tauto.
  Qed.
  Theorem canonical_output_loss : forall T h,
    starts<>[] -> (forall a, In a starts -> iter F T a=h) ->
    total_loss T=length starts-1.
  Proof.
    intros T h Hnonempty Hends.
    assert (Hcap:size T<=1).
    { change (size T<=length [h]); apply final_capacity.
      intros a Ha; rewrite Hends by exact Ha; left; reflexivity. }
    assert (Hpositive:0<size T).
    { destruct starts as [|a rest] eqn:E; [contradiction|].
      assert (Hin:In (iter F T a) (layer T)).
      { apply layer_image; exists a; split; [rewrite E; left; reflexivity|reflexivity]. }
      unfold size; destruct (layer T); simpl in *; [contradiction|lia]. }
    pose proof (exact_loss_telescopes T); lia.
  Qed.

  Variable price : nat -> nat.
  Fixpoint total_price n := match n with 0=>0 | S k=>total_price k+price k end.
  Definition halving_at t := forall y, In y (layer (S t)) ->
    count_occ eq_dec (map F (layer t)) y<=2^(price t).
  Lemma halving_edge : forall t, halving_at t -> size t<=2^(price t)*size (S t).
  Proof.
    intros t H; unfold size.
    rewrite <- (map_length F (layer t)) at 1.
    apply (bounded_multiplicity_capacity eq_dec); [apply layer_distinct| |exact H].
    intros s Hs; simpl; apply nodup_In; exact Hs.
  Qed.
  Theorem execution_halving_bound : forall T,
    (forall t, t<T -> halving_at t) ->
    length starts<=2^(total_price T)*size T.
  Proof.
    induction T; intro H; [simpl; unfold size; simpl; lia|].
    assert (Hprev:length starts<=2^(total_price T)*size T).
    { apply IHT; intros; apply H; lia. }
    pose proof (halving_edge T (H T (Nat.lt_succ_diag_r T))) as Hedge.
    change (length starts<=2^(total_price T+price T)*size (S T)).
    rewrite Nat.pow_add_r; nia.
  Qed.
End Ensemble.
