From Coq Require Import List Lia Arith.PeanoNat.

From KernelTOE Require Import Definitions.
From Kernel Require Import VMStep.
From Kernel Require Import VMState.
From Kernel Require Import EntropyImpossibility.

Import ListNotations.

(** * KernelTOE: minimal no-go theorems

    This is the “impossible without extra structure” part.
*)

(** ** A one-parameter family of weights preserving all explicit laws *)

Definition w_scale (k : nat) : Weight :=
  fun t => k * length t.

(** HELPER: Base case property *)
(** HELPER: Base case property *)
Lemma w_scale_empty : forall k, weight_empty (w_scale k).
Proof.
  intro k. unfold weight_empty, w_scale. simpl. lia.
Qed.

Lemma w_scale_sequential : forall k, weight_sequential (w_scale k).
Proof.
  intro k. unfold weight_sequential, w_scale.
  intros t1 t2. rewrite app_length. lia.
Qed.

Lemma w_scale_disjoint_commutes : forall k, weight_disjoint_commutes (w_scale k).
Proof.
  intro k. unfold weight_disjoint_commutes, w_scale.
  intros t1 t2 _.
  rewrite !app_length. lia.
Qed.

Lemma w_scale_laws : forall k, weight_laws (w_scale k).
Proof.
  intro k.
  unfold weight_laws.
  split.
  - apply w_scale_empty.
  - split.
    + apply w_scale_sequential.
    + apply w_scale_disjoint_commutes.
Qed.

(* DEFINITIONAL — witness w_scale, verify weight_laws + distinctness *)
Theorem CompositionalWeightFamily_Infinite :
  exists w : nat -> Weight,
    (forall k, weight_laws (w k)) /\
    (forall k1 k2, k1 <> k2 -> exists t, w k1 t <> w k2 t).
Proof.
  exists w_scale.
  split.
  - intro k. apply w_scale_laws.
  - intros k1 k2 Hneq.
    exists [instr_halt 0].
    unfold w_scale. simpl.
    (* k1*1 <> k2*1 *)
    intro Heq. apply Hneq.
    lia.
Qed.

(** ** Stronger no-go statement: no unique weight is forced *)

Definition KernelNoGo_UniqueWeight_FailsP : Prop :=
  exists w1 w2,
    weight_laws w1 /\
    weight_laws w2 /\
    (exists t, w1 t <> w2 t).

Theorem KernelNoGo_UniqueWeight_Fails : KernelNoGo_UniqueWeight_FailsP.
Proof.
  (* Pick two distinct points from the infinite family. *)
  exists (w_scale 1), (w_scale 2).
  split.
  - apply w_scale_laws.
  - split.
    + apply w_scale_laws.
    + exists [instr_halt 0].
      unfold w_scale. simpl. discriminate.
Qed.

(** ** Explicit “extra structure” sufficient to restore uniqueness

    If we add:
      - singleton uniformity (all single-instruction traces have equal weight)
      - unit normalization (pin that singleton to 1)
    then any law-abiding weight is forced to be length.
*)

Theorem Weight_Unique_Under_UniformSingletons :
  forall w,
    weight_laws w ->
    singleton_uniform w ->
    unit_normalization w ->
    forall t, w t = length t.
Proof.
  intros w [Hempty [Hseq _]] Hunif Hunit.
  induction t as [|i rest IH].
  - rewrite Hempty. reflexivity.
  - (* w (i::rest) = w([i]++rest) = w[i] + w rest = 1 + w rest *)
    replace (i :: rest) with ([i] ++ rest) by reflexivity.
    rewrite Hseq.
    specialize (Hunif i (instr_halt 0)).
    simpl in Hunif.
    rewrite Hunif.
    rewrite Hunit.
    rewrite IH.
    simpl. lia.
Qed.

(** ** Entropy obstruction: Dedekind-infinite observational classes *)

Lemma region_equiv_class_dedekind_infinite : forall s,
  exists f : nat -> VMState,
    (forall n, region_equiv s (f n)) /\
    (forall n1 n2, f n1 = f n2 -> n1 = n2).
Proof.
  intro s.
  (* Reuse the existing kernel witness (tweak_regs). *)
  destruct (region_equiv_class_infinite s) as [f [Hre Heq]].
  exists f. split; assumption.
Qed.

Lemma NoDup_map_inj :
  forall (A B : Type) (f : A -> B) (l : list A),
    NoDup l ->
    (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
    NoDup (map f l).
Proof.
  intros A B f l Hnodup.
  induction Hnodup as [|x xs Hnotin Hnodup_xs IH]; intros Hinj.
  - simpl. constructor.
  - simpl.
    constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [y [Hfy Hyin]].
      pose proof (Hinj x y (or_introl eq_refl) (or_intror Hyin) (eq_sym Hfy)) as Heq.
      subst y.
      exact (Hnotin Hyin).
    + apply IH.
      intros a b Ha Hb Hab.
      apply (Hinj a b (or_intror Ha) (or_intror Hb) Hab).
Qed.

Theorem region_equiv_class_not_finite :
  forall s,
    ~ finite_region_equiv_class s.
Proof.
  intro s.
  unfold finite_region_equiv_class.
  destruct (region_equiv_class_dedekind_infinite s) as [f [Hre Hinj]].
  intro Hfin.
  destruct Hfin as [l [Hnodup Hall]].
  (* Build an arbitrary-large NoDup list inside l, contradicting finiteness. *)
  set (n := S (length l)).
  pose (l1 := map f (seq 0 n)).
  assert (Hnodup_l1 : NoDup l1).
  {
    unfold l1.
    apply (NoDup_map_inj nat VMState f (seq 0 n)).
    - apply seq_NoDup.
    - intros a b _ _ Hab.
      apply Hinj in Hab.
      exact Hab.
  }
  assert (Hincl : incl l1 l).
  {
    unfold incl, l1.
    intros x Hin.
    apply in_map_iff in Hin.
    destruct Hin as [k [Hx Hk]].
    subst x.
    (* f k is region-equivalent to s, hence must be in l *)
    apply Hall.
    apply Hre.
  }
  pose proof (NoDup_incl_length Hnodup_l1 Hincl) as Hlen.
  unfold l1 in Hlen.
  rewrite map_length, seq_length in Hlen.
  (* n <= length l contradicts n = S (length l) *)
  unfold n in Hlen.
  lia.
Qed.

(** ** Flagship no-go theorem (kernel + explicit gaps) *)

Definition KernelNoGoForTOE_P : Prop :=
  KernelNoGo_UniqueWeight_FailsP
  /\
  (forall s, ~ finite_region_equiv_class s).

Theorem KernelNoGoForTOE : KernelNoGoForTOE_P.
Proof.
  split.
  - exact KernelNoGo_UniqueWeight_Fails.
  - intro s.
    apply region_equiv_class_not_finite.
Qed.
