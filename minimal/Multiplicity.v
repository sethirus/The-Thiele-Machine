(* SCOPE NOTE: standalone proof scope.
   Supplies finite-list multiplicity bounds used in ensemble retention counting.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List ListDec Arith Lia.
Import ListNotations.

Section Piles.
  Context {Y : Type}.
  Variable eq_dec : forall a b : Y, {a=b}+{a<>b}.
  Fixpoint mass (targets values : list Y) : nat :=
    match targets with []=>0 | y::rest=>count_occ eq_dec values y+mass rest values end.
  Lemma mass_empty : forall targets, mass targets []=0.
  Proof. induction targets; simpl; lia. Qed.
  Lemma mass_cons : forall targets x xs,
    mass targets (x::xs)=mass targets xs+count_occ eq_dec targets x.
  Proof.
    induction targets as [|y ys IH]; intros x xs; simpl; [lia|].
    rewrite IH; destruct (eq_dec x y); destruct (eq_dec y x); try congruence; lia.
  Qed.
  Theorem count_partition : forall values targets,
    NoDup targets -> incl values targets -> mass targets values=length values.
  Proof.
    induction values as [|x xs IH]; intros targets Hnd Hinc.
    - apply mass_empty.
    - rewrite mass_cons; simpl.
      assert (Hx:In x targets) by (apply Hinc; left; reflexivity).
      assert (Hxs:incl xs targets) by (intros y Hy; apply Hinc; right; exact Hy).
      rewrite IH by assumption.
      rewrite (proj1 (NoDup_count_occ' eq_dec targets) Hnd x Hx); lia.
  Qed.
  Lemma mass_bound : forall targets values k,
    (forall y, In y targets -> count_occ eq_dec values y<=k) ->
    mass targets values<=k*length targets.
  Proof.
    induction targets as [|y ys IH]; intros values k H; simpl; [lia|].
    assert (Hy:count_occ eq_dec values y<=k) by (apply H; left; reflexivity).
    assert (Hys:mass ys values<=k*length ys).
    { apply IH; intros z Hz; apply H; right; exact Hz. }
    nia.
  Qed.
  Theorem bounded_multiplicity_capacity : forall values targets k,
    NoDup targets -> incl values targets ->
    (forall y, In y targets -> count_occ eq_dec values y<=k) ->
    length values<=k*length targets.
  Proof.
    intros values targets k Hnd Hinc Hbound.
    rewrite <- (count_partition values targets Hnd Hinc); apply mass_bound; assumption.
  Qed.
  Theorem overcapacity_forces_large_pile : forall values targets k,
    NoDup targets -> incl values targets -> k*length targets<length values ->
    exists y, In y targets /\ k<count_occ eq_dec values y.
  Proof.
    intros values targets k Hnd Hinc Hbig.
    destruct (Exists_dec (fun y=>k<count_occ eq_dec values y) targets
      (fun y=>lt_dec k (count_occ eq_dec values y))) as [Hex|Hno].
    - apply Exists_exists in Hex; exact Hex.
    - assert (Hbound:forall y, In y targets -> count_occ eq_dec values y<=k).
      { intros y Hy; destruct (le_dec (count_occ eq_dec values y) k); [assumption|].
        exfalso; apply Hno; apply Exists_exists; exists y; split; auto; lia. }
      pose proof (bounded_multiplicity_capacity values targets k Hnd Hinc Hbound); lia.
  Qed.
End Piles.

(* Mapping a duplicate-free input list makes occurrences in the value list
   count DISTINCT input states, rather than repeated samples of one input. *)
Theorem preparation_overcapacity {X Y : Type}
    (eq_dec : forall a b : Y, {a=b}+{a<>b}) (f : X->Y) :
  forall inputs targets k,
  NoDup inputs -> NoDup targets ->
  (forall x, In x inputs -> In (f x) targets) ->
  k*length targets<length inputs ->
  exists y, In y targets /\ k<count_occ eq_dec (map f inputs) y.
Proof.
  intros inputs targets k Hinputs Htargets Himage Hbig.
  apply overcapacity_forces_large_pile; [exact Htargets| |rewrite map_length; exact Hbig].
  intros y Hy; apply in_map_iff in Hy as [x [<- Hx]]; apply Himage; exact Hx.
Qed.
