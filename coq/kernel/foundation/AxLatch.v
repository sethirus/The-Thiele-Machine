(** AxLatch: a record on the axis is a family of latches, one per point.

    A machine is extended by a record whose next value depends only on the
    classical state and on itself ("driven by the computation") and which
    only grows.  Then, for every point a of the order, the bit "a <= record"
    evolves as a latch: it turns on at some event and never turns off.  The
    event may read the record.  Conversely a family of such latches is a
    growing, driven record.  This is the axis form of the book's statement
    that the record of a machine is a latch.

    Results (all closed):

      ax_decompose           driven and growing give a threshold factorization,
                             over any preorder; no price, no antisymmetry, no
                             reachable write.
      ax_factor_grows        a threshold factorization forces growth.
      ax_factor_determined   with antisymmetry it forces the record to be
                             determined by the classical state and itself.
      ax_a2_iff_views        the axis toll holds exactly when every threshold
                             pays its own one-bit toll.
      ax_a2_threshold_form   the same, as "a step that crosses a threshold".

    Each hypothesis is needed:

      toggle_no_factorization   a driven record that revokes has no
                                factorization (growth is needed).
      clock_no_factorization    a hidden-clock record has no factorization
                                (being driven is needed).
      indiscrete_loses_record   over a preorder that is not antisymmetric the
                                thresholds do not determine the record.

    What the single event becomes:

      two_point_is_join_latch   over the two-point order one event of the
                                classical state suffices (the book's latch).
      chain3_not_join_latch     over the three-point chain no event of the
                                classical state suffices: the events must read
                                the record.
    The book's one-bit latch theorem is the two-point instance
    ([two_point_record_axis_is_latch]).  The bit count and the pair of
    records are in AxLatch2. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import StructuralCore StructuralCoreCover StructuralCoreAnyBase
  StructuralRecordAxis GrowingRecordCore GrowingRecord.
From Kernel Require Import AxCore.

Section Latch.

Variable M : RCM.
Variable B : BaseMachine.
Variable C : BaseCover M B.
Variable A : Type.
Variable P : BPre A.
Variable rec : rc_state M -> A.

Definition ax_rgrows : Prop :=
  forall m, bp_le P (rec m) (rec (rc_next M m)).

Definition ax_rdriven : Prop :=
  exists f : b_state B -> A -> A,
    forall m, rec (rc_next M m) = f (base_state M B C m) (rec m).

(** The next record depends only on the classical state and the record,
    stated without a function. *)
Definition ax_rdetermined : Prop :=
  forall m m', base_state M B C m = base_state M B C m' -> rec m = rec m' ->
    rec (rc_next M m) = rec (rc_next M m').

Definition ax_thr_fact (h : A -> b_state B -> A -> bool) : Prop :=
  forall m a,
    bp_leb A P a (rec (rc_next M m)) =
    orb (bp_leb A P a (rec m)) (h a (base_state M B C m) (rec m)).

Theorem ax_driven_determined : ax_rdriven -> ax_rdetermined.
Proof.
  intros [f Hf] m m' Hb Hr. rewrite !Hf, Hb, Hr. reflexivity.
Qed.

(** Driven and growing: every threshold is a latch.  Any preorder. *)
Theorem ax_decompose : ax_rgrows -> ax_rdriven ->
  exists h, ax_thr_fact h.
Proof.
  intros Hg [f Hf].
  exists (fun a b x => andb (negb (bp_leb A P a x)) (bp_leb A P a (f b x))).
  intros m a. rewrite Hf. specialize (Hg m). rewrite Hf in Hg.
  destruct (bp_leb A P a (rec m)) eqn:Hbefore;
    destruct (bp_leb A P a (f (base_state M B C m) (rec m))) eqn:Hafter;
    simpl; try reflexivity.
  exfalso.
  pose proof (bp_trans A P a (rec m) (f (base_state M B C m) (rec m)) Hbefore Hg).
  congruence.
Qed.

(** A factorization forces growth. *)
Theorem ax_factor_grows : forall h, ax_thr_fact h -> ax_rgrows.
Proof.
  intros h Hh m. unfold bp_le. rewrite (Hh m (rec m)), bp_refl. reflexivity.
Qed.

(** With antisymmetry a factorization forces the record to be driven in the
    function-free sense. *)
Theorem ax_factor_determined : bp_antisym P ->
  forall h, ax_thr_fact h -> ax_rdetermined.
Proof.
  intros Hanti h Hh m m' Hb Hr.
  apply (bp_thresholds_determine A P Hanti). intro a.
  rewrite (Hh m a), (Hh m' a), Hb, Hr. reflexivity.
Qed.

(** Without antisymmetry the factorization still fixes the record up to
    equivalence. *)
Theorem ax_factor_determined_up_to_equiv :
  forall h, ax_thr_fact h ->
  forall m m', base_state M B C m = base_state M B C m' -> rec m = rec m' ->
    bp_le P (rec (rc_next M m)) (rec (rc_next M m')) /\
    bp_le P (rec (rc_next M m')) (rec (rc_next M m)).
Proof.
  intros h Hh m m' Hb Hr.
  assert (Hthr : forall a, bp_leb A P a (rec (rc_next M m)) =
                           bp_leb A P a (rec (rc_next M m'))).
  { intro a. rewrite (Hh m a), (Hh m' a), Hb, Hr. reflexivity. }
  split; unfold bp_le.
  - rewrite <- (Hthr (rec (rc_next M m))). apply bp_refl.
  - rewrite (Hthr (rec (rc_next M m'))). apply bp_refl.
Qed.

End Latch.

Arguments ax_rgrows {M A} P rec.
Arguments ax_rdriven {M B} C {A} rec.
Arguments ax_rdetermined {M B} C {A} rec.
Arguments ax_thr_fact {M B} C {A} P rec h.

(** * The toll is the conjunction of the one-bit tolls *)

Section Price.

Variable A : Type.
Variable P : BPre A.
Variable X : AxSys A P.

Theorem ax_a2_iff_views :
  ax_a2 (X := X) <-> forall a, ax_a2 (X := ax_view X a).
Proof.
  split.
  - intro H. exact (ax_view_a2 X H).
  - intros H s i Hex. specialize (H (ax_rec A P X (ax_step A P X s i)) s i).
    apply H. unfold ax_exits. simpl. intro Hle. apply Hex.
    unfold bp_le in *. simpl in Hle. destruct (bp_leb A P (ax_rec A P X (ax_step A P X s i)) (ax_rec A P X s)) eqn:E.
    + reflexivity.
    + exfalso. rewrite bp_refl in Hle. simpl in Hle. discriminate.
Qed.

Theorem ax_a2_threshold_form :
  ax_a2 (X := X) <->
  forall s i a, ~ bp_le P a (ax_rec A P X s) ->
                bp_le P a (ax_rec A P X (ax_step A P X s i)) ->
                ax_cost A P X i >= 1.
Proof.
  split.
  - intros H s i a Hn Hy. apply (H s i). intro Hle. apply Hn.
    eapply bp_le_trans; [exact Hy | exact Hle].
  - intros H s i Hex. apply (H s i (ax_rec A P X (ax_step A P X s i))); [exact Hex |].
    apply bp_le_refl.
Qed.

End Price.

(** * Each hypothesis is needed *)

(** A revoking record has no factorization. *)
Definition toggle_rcm : RCM := {|
  rc_state := nat * bool;
  rc_next := fun x => (S (fst x), negb (snd x));
  rc_init := fun _ => True;
  rc_cert := snd;
  rc_mu := fst;
  rc_halted := fun _ => False
|}.

Theorem toggle_no_factorization :
  ax_rdriven toggle_cover (A := bool) snd /\
  ~ exists h, ax_thr_fact toggle_cover two_pre snd h.
Proof.
  split.
  - exists (fun _ r => negb r). intro m. reflexivity.
  - intros [h Hh]. pose proof (ax_factor_grows _ _ _ _ _ _ h Hh (0, true)) as Hg.
    unfold bp_le in Hg. simpl in Hg. discriminate.
Qed.

(** A record switched on by a hidden clock has no factorization. *)
Theorem clock_no_factorization :
  ax_rgrows two_pre (M := ClockCore) (fun x => let '(_, _, r) := x in r) /\
  ~ exists h, ax_thr_fact clock_cover two_pre
      (fun x : rc_state ClockCore => let '(_, _, r) := x in r) h.
Proof.
  split.
  - intros [[b k] r]. unfold bp_le. simpl. destruct r; simpl; reflexivity.
  - intros [h Hh].
    pose proof (ax_factor_determined _ _ _ _ _ _ two_antisym h Hh) as Hd.
    specialize (Hd (0, 5, false) (0, 0, false) eq_refl eq_refl).
    simpl in Hd. discriminate.
Qed.

(** Over an indiscrete preorder every record "grows" and the thresholds
    carry nothing: the factorization holds with a trivial event and says
    nothing about the record. *)
Definition flip_rcm : RCM := {|
  rc_state := bool;
  rc_next := negb;
  rc_init := fun _ => True;
  rc_cert := fun _ => false;
  rc_mu := fun _ => 0;
  rc_halted := fun _ => False
|}.

Definition flip_base : BaseMachine := {|
  b_state := unit;
  b_next := fun _ => tt;
  b_init := fun _ => True;
  b_halted := fun _ => False
|}.

Definition flip_cover : BaseCover flip_rcm flip_base.
Proof.
  refine (Build_BaseCover flip_rcm flip_base (fun _ => tt) _ _ _ _).
  - intros; exact I.
  - intros [] _. exists true. split; [exact I | reflexivity].
  - intros []; reflexivity.
  - intros []; split; contradiction.
Defined.

Theorem indiscrete_loses_record :
  ax_rgrows indiscrete_pre (M := flip_rcm) (fun x => x) /\
  ax_rdriven flip_cover (A := bool) (fun x => x) /\
  ax_thr_fact flip_cover indiscrete_pre (fun x => x) (fun _ _ _ => false) /\
  (forall a, bp_leb bool indiscrete_pre a true = bp_leb bool indiscrete_pre a false) /\
  rc_next flip_rcm true <> true.
Proof.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - intros m. unfold bp_le. reflexivity.
  - exists (fun _ r => negb r). intro m. reflexivity.
  - intros m a. reflexivity.
  - intro a. reflexivity.
  - intro H. discriminate H.
Qed.

(** * What the single event becomes *)

(** Over the two-point order one event of the classical state suffices. *)
Theorem two_point_is_join_latch :
  forall (M : RCM) (B : BaseMachine) (C : BaseCover M B) (rec : rc_state M -> bool),
    ax_rgrows two_pre rec -> ax_rdriven C rec ->
    exists g : b_state B -> bool,
      forall m, rec (rc_next M m) = orb (rec m) (g (base_state M B C m)).
Proof.
  intros M B C rec Hg [f Hf].
  exists (fun b => f b false). intro m. rewrite Hf.
  destruct (rec m) eqn:E.
  - specialize (Hg m). rewrite Hf, E in Hg. unfold bp_le in Hg. simpl in Hg.
    simpl. exact Hg.
  - reflexivity.
Qed.

(** The book's latch theorem as a corollary: it is the two-point case. *)
Corollary two_point_record_axis_is_latch : record_axis_is_latch.
Proof.
  intros M B C [Hdr [_ [_ [Hperm _]]]].
  assert (Hg : ax_rgrows two_pre (rc_cert M)).
  { intro m. unfold bp_le. simpl. destruct (rc_cert M m) eqn:E;
      [rewrite (Hperm m E); reflexivity | reflexivity]. }
  destruct (two_point_is_join_latch M B C (rc_cert M) Hg Hdr) as [g Hg'].
  exists g. intro m. unfold latch_next. simpl. rewrite (base_step M B C m).
  rewrite (Hg' m). reflexivity.
Qed.

(** A three-point chain a < b < c, as a type. *)
Inductive ax_T3 : Type := ax_t0 | ax_t1 | ax_t2.

Definition t3_leb (x y : ax_T3) : bool :=
  match x, y with
  | ax_t0, _ => true
  | ax_t1, ax_t0 => false
  | ax_t1, _ => true
  | ax_t2, ax_t2 => true
  | ax_t2, _ => false
  end.

Definition t3_pre : BPre ax_T3.
Proof.
  refine {| bp_leb := t3_leb |}.
  - intros []; reflexivity.
  - intros [] [] []; simpl; intros; try discriminate; reflexivity.
Defined.

Definition t3_next (x : ax_T3) : ax_T3 := match x with ax_t0 => ax_t2 | ax_t1 => ax_t1 | ax_t2 => ax_t2 end.

Definition t3_rcm : RCM := {|
  rc_state := ax_T3;
  rc_next := t3_next;
  rc_init := fun _ => True;
  rc_cert := fun _ => false;
  rc_mu := fun _ => 0;
  rc_halted := fun _ => False
|}.

Definition t3_base : BaseMachine := {|
  b_state := unit;
  b_next := fun _ => tt;
  b_init := fun _ => True;
  b_halted := fun _ => False
|}.

Definition t3_cover : BaseCover t3_rcm t3_base.
Proof.
  refine (Build_BaseCover t3_rcm t3_base (fun _ => tt) _ _ _ _).
  - intros; exact I.
  - intros [] _. exists ax_t0. split; [exact I | reflexivity].
  - intros []; reflexivity.
  - intros []; split; contradiction.
Defined.

Definition ax_is_lub {A} (P : BPre A) (x y z : A) : Prop :=
  bp_le P x z /\ bp_le P y z /\ forall w, bp_le P x w -> bp_le P y w -> bp_le P z w.

(** The record is driven and growing, yet its next value is never the join
    of itself with an event of the classical state. *)
Theorem chain3_not_join_latch :
  ax_rgrows t3_pre (M := t3_rcm) (fun x => x) /\
  ax_rdriven t3_cover (A := ax_T3) (fun x => x) /\
  ~ exists g : unit -> ax_T3, forall m : ax_T3,
      ax_is_lub t3_pre m (g tt) (t3_next m).
Proof.
  split; [| split].
  - intros []; reflexivity.
  - exists (fun _ x => t3_next x). intros []; reflexivity.
  - intros [g Hg].
    pose proof (Hg ax_t0) as H0. pose proof (Hg ax_t1) as H1.
    destruct (g tt) eqn:Eg.
    + destruct H0 as [_ [_ Hw]]. specialize (Hw ax_t0 eq_refl eq_refl).
      unfold bp_le in Hw. discriminate Hw.
    + destruct H0 as [_ [_ Hw]]. specialize (Hw ax_t1 eq_refl eq_refl).
      unfold bp_le in Hw. discriminate Hw.
    + destruct H1 as [_ [Hy _]]. unfold bp_le in Hy. discriminate Hy.
Qed.

Print Assumptions ax_driven_determined.
Print Assumptions ax_decompose.
Print Assumptions ax_factor_grows.
Print Assumptions ax_factor_determined.
Print Assumptions ax_factor_determined_up_to_equiv.
Print Assumptions ax_a2_iff_views.
Print Assumptions ax_a2_threshold_form.
Print Assumptions toggle_no_factorization.
Print Assumptions clock_no_factorization.
Print Assumptions indiscrete_loses_record.
Print Assumptions two_point_is_join_latch.
Print Assumptions two_point_record_axis_is_latch.
Print Assumptions chain3_not_join_latch.
