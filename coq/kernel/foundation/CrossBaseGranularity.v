(** Closed generic and available-adapter outcomes for cross-base granularity. *)

From Coq Require Import Arith.PeanoNat.
From Kernel Require Import StructuralCoreAnyBase StructuralRecordAxis CrossBaseGranularityCore.
From Kernel Require Import CrossBaseGranularityTransCore.

Theorem weak_base_equiv_refl_holds : weak_base_equiv_refl.
Proof.
  intros B O obs. exists (fun x y => x = y).
  split; [intros x Hx; exists x; auto |].
  split; [intros y Hy; exists y; auto |].
  intros x y ->. split; [reflexivity |].
  split; [reflexivity |]. split.
  - exists 1. reflexivity.
  - exists 1. reflexivity.
Qed.

Theorem weak_base_equiv_sym_holds : weak_base_equiv_sym.
Proof.
  intros B1 B2 O obs1 obs2 [R [Hinit1 [Hinit2 Hstep]]].
  exists (fun y x => R x y). split; [exact Hinit2 |].
  split; [exact Hinit1 |].
  intros y x Hxy.
  destruct (Hstep x y Hxy) as [Hobs [Hhalt [H12 H21]]].
  split; [symmetry; exact Hobs |].
  split; [symmetry; exact Hhalt |].
  split; [exact H21 | exact H12].
Qed.

Lemma weak_match_left_runs :
  forall (B1 B2 : BaseMachine) (R : b_state B1 -> b_state B2 -> Prop),
    (forall x y, R x y ->
      (exists n, R (b_next B1 x) (base_run B2 n y))) ->
    forall k x y, R x y ->
      exists n, R (base_run B1 k x) (base_run B2 n y).
Proof.
  intros B1 B2 R Hone k. induction k as [|k IH]; intros x y Hxy.
  - exists 0. exact Hxy.
  - destruct (Hone x y Hxy) as [n Hn].
    destruct (IH (b_next B1 x) (base_run B2 n y) Hn) as [m Hm].
    exists (m + n). unfold base_run in *. rewrite Nat.iter_succ_r.
    rewrite Nat.iter_add. exact Hm.
Qed.

Lemma weak_match_right_runs :
  forall (B1 B2 : BaseMachine) (R : b_state B1 -> b_state B2 -> Prop),
    (forall x y, R x y ->
      (exists n, R (base_run B1 n x) (b_next B2 y))) ->
    forall k x y, R x y ->
      exists n, R (base_run B1 n x) (base_run B2 k y).
Proof.
  intros B1 B2 R Hone k. induction k as [|k IH]; intros x y Hxy.
  - exists 0. exact Hxy.
  - destruct (Hone x y Hxy) as [n Hn].
    destruct (IH (base_run B1 n x) (b_next B2 y) Hn) as [m Hm].
    exists (m + n). unfold base_run in *. rewrite Nat.iter_succ_r.
    rewrite Nat.iter_add. exact Hm.
Qed.

Theorem weak_base_equiv_trans_holds : weak_base_equiv_trans.
Proof.
  intros B1 B2 B3 O obs1 obs2 obs3
    [R12 [Hi12 [Hi21 H12]]] [R23 [Hi23 [Hi32 H23]]].
  exists (fun x z => exists y, R12 x y /\ R23 y z).
  split.
  - intros x Hx. destruct (Hi12 x Hx) as [y [Hy Hxy]].
    destruct (Hi23 y Hy) as [z [Hz Hyz]].
    exists z. split; [exact Hz |]. exists y. auto.
  - split.
    + intros z Hz. destruct (Hi32 z Hz) as [y [Hy Hyz]].
      destruct (Hi21 y Hy) as [x [Hx Hxy]].
      exists x. split; [exact Hx |]. exists y. auto.
    + intros x z [y [Hxy Hyz]].
      destruct (H12 x y Hxy) as [Ho12 [Hh12 [Hs12 Hs21]]].
      destruct (H23 y z Hyz) as [Ho23 [Hh23 [Hs23 Hs32]]].
      split; [now rewrite Ho12 |].
      split; [tauto |]. split.
      * destruct Hs12 as [n Hnext].
        assert (Hone23 : forall a b, R23 a b ->
          exists q, R23 (b_next B2 a) (base_run B3 q b)).
        { intros a b Hab. destruct (H23 a b Hab) as [_ [_ [H _]]]. exact H. }
        destruct (weak_match_left_runs B2 B3 R23 Hone23 n y z Hyz)
          as [q Hrun].
        exists q, (base_run B2 n y). auto.
      * destruct Hs32 as [n Hnext].
        assert (Hone12 : forall a b, R12 a b ->
          exists q, R12 (base_run B1 q a) (b_next B2 b)).
        { intros a b Hab. destruct (H12 a b Hab) as [_ [_ [_ H]]]. exact H. }
        destruct (weak_match_right_runs B1 B2 R12 Hone12 n x y Hxy)
          as [q Hrun].
        exists q, (base_run B2 n y). auto.
Qed.

(** Both sides of the equivalence hold for every base:
    [record_axis_is_latch_holds] proves the record axis is a latch over any
    deterministic base. So weakly equivalent bases agree on it, and so do any
    two bases. The weak-equivalence premise is not used; the theorem says no
    more than that. *)
Theorem weak_equiv_preserves_record_latch_holds : weak_equiv_preserves_record_latch.
Proof.
  intros B1 B2 O obs1 obs2 _. split; intros _ M C Hhonest;
    exact (record_axis_is_latch_holds M _ C Hhonest).
Qed.

Theorem record_axis_is_latch_on_tm_holds : record_axis_is_latch_on_tm.
Proof.
  intros p M C Hhonest.
  exact (record_axis_is_latch_holds M _ C Hhonest).
Qed.

Print Assumptions weak_base_equiv_refl_holds.
Print Assumptions weak_base_equiv_sym_holds.
Print Assumptions weak_base_equiv_trans_holds.
Print Assumptions weak_equiv_preserves_record_latch_holds.
Print Assumptions record_axis_is_latch_on_tm_holds.
