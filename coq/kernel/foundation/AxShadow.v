(** AxShadow: the shadow, its fibres, and what the toll prices.

    The Turing machine is the shadow of the axis machine: the map that drops
    the record and the ledger.  The fibre over a classical state is the set of
    full states that project onto it.  The axis coordinates locate a point in
    the fibre, and certification is the instrument that tells two points of
    one fibre apart.

    The four parts of the shadow theorem for a Thiele-complete machine are
    proved in AxComplete2:

      independence   [ax_tc_independence], [ax_tc_collision]: two reachable
                     states in one fibre with different records, and no
                     function of the shadow gives the record;
      invisibility   [ax_tc_ledger_independence], [ax_tc_no_verifier]: no
                     function of the shadow gives the ledger, and no bare
                     verifier decides any point;
      conservativity [ax_tc_conservative]: the compiled moves are exactly the
                     classical machine and leave the record and the ledger
                     alone;
      priced movement [ax_tc_every_point_priced]: every point not below the
                     floor costs at least 3.

    Here (all closed):

      ax_fibre_collapse_exit    on a finite machine whose shadow step is
                                injective (the classical machine forgets
                                nothing), a move that takes the record out of
                                the down-set merges two distinct states of
                                one fibre: the toll prices the destruction of
                                axis information inside a fibre.
      shadow_merge_escape       without that premise the merge can be between
                                two fibres only and no fibre point is lost.
      ax_step_fibre_in_fibre    with an injective shadow step every landing
                                spot of a move receives states of one fibre.
      ax_compression_iff_fibres the halving price is exactly the bound "no
                                landing spot receives more than 2^cost
                                states"; with an injective shadow those
                                states are all points of one fibre.
      ax_thresholds_separate    two states whose records are inequivalent are
                                told apart by a one-bit threshold: the tap. *)

From Coq Require Import List Bool Arith.PeanoNat Lia ListDec.
Import ListNotations.
From Kernel Require Import AxCore AxMerge.
Require Minimal.EntitlementSmall.

Lemma ax_nodup_map_collision : forall {S : Type} (eq_dec : forall a b : S, {a = b} + {a <> b})
    (f : S -> S) (l : list S),
  NoDup l -> ~ NoDup (map f l) ->
  exists x y, In x l /\ In y l /\ x <> y /\ f x = f y.
Proof.
  intros S eq_dec f l. induction l as [| a l IH]; intros Hnd Hnn.
  - exfalso. apply Hnn. constructor.
  - inversion Hnd as [| ? ? Hnotin Hl]; subst. simpl in Hnn.
    destruct (in_dec eq_dec (f a) (map f l)) as [Hin | Hnin].
    + apply in_map_iff in Hin as [y [Hy Hyl]].
      exists a, y. split; [left; reflexivity |]. split; [right; exact Hyl |].
      split; [intro H; subst y; exact (Hnotin Hyl) | symmetry; exact Hy].
    + assert (Hnn' : ~ NoDup (map f l)).
      { intro H. apply Hnn. constructor; [exact Hnin | exact H]. }
      destruct (IH Hl Hnn') as [x [y [Hx [Hy [Hne Hf]]]]].
      exists x, y. split; [right; exact Hx |]. split; [right; exact Hy |]. auto.
Qed.

Section Shadow.

Variable A : Type.
Variable P : BPre A.
Variable X : AxSys A P.

Local Notation S := (ax_state A P X).
Local Notation I := (ax_instr A P X).
Local Notation step := (ax_step A P X).
Local Notation rc := (ax_rec A P X).
Local Notation cost := (ax_cost A P X).

Variable eq_dec : forall a b : S, {a = b} + {a <> b}.

(** A move that takes the record out of the down-set, on a finite machine,
    collides two distinct states. *)
Theorem ax_exit_collision :
  forall all s i, ax_finite X all -> ax_grows (X := X) -> ax_exits (X := X) s i ->
    exists x y, x <> y /\ step x i = step y i.
Proof.
  intros all s i Hfin Hg Hex.
  set (a := rc (step s i)).
  set (T := ax_up X all a).
  assert (Hs : ~ In s T).
  { intro H. apply (ax_up_spec A P X all a Hfin) in H. exact (Hex H). }
  assert (HndL : NoDup (s :: T)).
  { constructor; [exact Hs | apply (ax_up_nodup A P X all a Hfin)]. }
  assert (Hincl : incl (map (fun t => step t i) (s :: T)) T).
  { intros y Hy. apply in_map_iff in Hy as [x [<- Hx]]. destruct Hx as [<- | Hx].
    - apply (ax_up_spec A P X all a Hfin). apply bp_le_refl.
    - apply (ax_up_spec A P X all a Hfin). apply (ax_up_spec A P X all a Hfin) in Hx.
      eapply bp_le_trans; [exact Hx | apply Hg]. }
  destruct (NoDup_dec eq_dec (map (fun t => step t i) (s :: T)))
    as [Hnd | Hnn].
  - exfalso. pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
    rewrite map_length in Hlen. simpl in Hlen. lia.
  - destruct (ax_nodup_map_collision eq_dec (fun t => step t i) (s :: T) HndL Hnn)
      as [x [y [_ [_ [Hne Hf]]]]]. exists x, y. auto.
Qed.

(** A cover: a projection to classical states commuting with a classical step. *)
Variable C : Type.
Variable proj : S -> C.
Variable cstep : C -> I -> C.
Hypothesis proj_step : forall s i, proj (step s i) = cstep (proj s) i.

(** The classical step forgets nothing for this move. *)
Definition shadow_injective (i : I) : Prop :=
  forall a b, cstep a i = cstep b i -> a = b.

(** A move merges two distinct states of one fibre. *)
Definition fibre_collapse (i : I) : Prop :=
  exists x y, x <> y /\ proj x = proj y /\ step x i = step y i.

(** With an injective shadow, every merge is a merge inside one fibre. *)
Lemma merge_in_fibre : forall i,
  shadow_injective i ->
  forall x y, step x i = step y i -> proj x = proj y.
Proof.
  intros i Hinj x y H. apply Hinj. rewrite <- !proj_step. rewrite H. reflexivity.
Qed.

(** The toll prices the destruction of axis information inside a fibre. *)
Theorem ax_fibre_collapse_exit :
  forall all s i, ax_finite X all -> ax_grows (X := X) -> ax_exits (X := X) s i ->
    shadow_injective i -> fibre_collapse i.
Proof.
  intros all s i Hfin Hg Hex Hsh.
  destruct (ax_exit_collision all s i Hfin Hg Hex) as [x [y [Hne Hxy]]].
  exists x, y. split; [exact Hne |]. split; [apply (merge_in_fibre i Hsh); exact Hxy | exact Hxy].
Qed.

(** With an injective shadow, a landing spot receives states of one fibre. *)
Theorem ax_step_fibre_in_fibre : forall i,
  shadow_injective i ->
  forall y x1 x2, step x1 i = y -> step x2 i = y -> proj x1 = proj x2.
Proof.
  intros i Hsh y x1 x2 H1 H2. apply (merge_in_fibre i Hsh). rewrite H1, H2. reflexivity.
Qed.

(** ** The halving price is a bound on landing spots *)

Definition ax_step_fibre (all : list S) (i : I) (y : S) : list S :=
  filter (fun x => if eq_dec (step x i) y then true else false) all.

Definition ax_eqb (a b : S) : bool := if eq_dec a b then true else false.

Lemma ax_eqb_spec : forall a b, ax_eqb a b = true <-> a = b.
Proof. intros a b. unfold ax_eqb. destruct (eq_dec a b); split; intro H; auto; discriminate. Qed.

Lemma ax_filter_nodup_le : forall {B : Type} (p : B -> bool) (D all : list B),
  NoDup D -> incl D all -> length (filter p D) <= length (filter p all).
Proof.
  intros B p D all Hnd Hin.
  apply NoDup_incl_length; [apply NoDup_filter, Hnd |].
  intros x Hx. apply filter_In in Hx as [Hx1 Hx2]. apply filter_In. split; auto.
Qed.

Theorem ax_compression_iff_fibres : forall all,
  ax_finite X all ->
  (ax_compression_priced A P X eq_dec <->
   forall i y, length (ax_step_fibre all i y) <= 2 ^ cost i).
Proof.
  intros all [Hnd Hall]. split.
  - intros Hprice i y.
    pose proof (Hprice i (ax_step_fibre all i y) (NoDup_filter _ Hnd)) as H.
    assert (Himg : ax_image_size A P X eq_dec i (ax_step_fibre all i y) <= 1).
    { unfold ax_image_size.
      change 1 with (length [y]).
      apply NoDup_incl_length; [apply NoDup_nodup |].
      intros z Hz. apply nodup_In in Hz. apply in_map_iff in Hz as [x [<- Hx]].
      unfold ax_step_fibre in Hx. apply filter_In in Hx as [_ Hx].
      destruct (eq_dec (step x i) y) as [E | _]; [| discriminate].
      rewrite E. left. reflexivity. }
    assert (Hm : 2 ^ cost i * ax_image_size A P X eq_dec i (ax_step_fibre all i y) <= 2 ^ cost i * 1)
      by (apply Nat.mul_le_mono_l; exact Himg).
    lia.
  - intros Hfib i D HD. unfold ax_image_size.
    set (imgs := nodup eq_dec (map (fun t => step t i) D)).
    apply (Minimal.EntitlementSmall.ent_fibres_count ax_eqb ax_eqb_spec
             (fun x => step x i) (2 ^ cost i) imgs D).
    + intros x Hx. unfold imgs. apply nodup_In. apply (in_map (fun t => step t i)). exact Hx.
    + intros x Hx.
      eapply Nat.le_trans.
      * apply (ax_filter_nodup_le (fun y => ax_eqb (step y i) (step x i)) D all HD).
        intros z _. apply Hall.
      * change (length (ax_step_fibre all i (step x i)) <= 2 ^ cost i). apply Hfib.
Qed.

End Shadow.

(** ** Without a reversible shadow the merge can be between fibres only *)

(** Two states, each alone in its fibre; the classical step sends both to the
    same classical state.  The record rises by a merge that destroys no point
    of any fibre. *)
Theorem shadow_merge_escape :
  ax_finite stamp_sys [false; true] /\
  ax_grows (X := stamp_sys) /\
  ax_exits (X := stamp_sys) false tt /\
  ~ ax_step_injective stamp_sys tt /\
  (forall x y : bool, x <> y -> (fun b : bool => b) x <> (fun b : bool => b) y) /\
  ~ (forall a b : bool, (fun (_ : bool) (_ : unit) => true) a tt =
                        (fun (_ : bool) (_ : unit) => true) b tt -> a = b).
Proof.
  destruct free_merge_escape as [Hfin [Hg [Hn _]]].
  assert (Hn' : ~ ax_step_injective stamp_sys tt).
  { intro Hinj. specialize (Hinj false true eq_refl). discriminate. }
  refine (conj Hfin (conj Hg (conj _ (conj Hn' (conj _ _))))).
  - unfold ax_exits, bp_le. simpl. discriminate.
  - intros x y H. exact H.
  - intro H. specialize (H false true eq_refl). discriminate.
Qed.

(** ** The tap: a threshold tells inequivalent records apart *)

Theorem ax_thresholds_separate : forall {A : Type} (P : BPre A) (x y : A),
  ~ (bp_le P x y /\ bp_le P y x) ->
  exists a, bp_leb A P a x <> bp_leb A P a y.
Proof.
  intros A P x y H.
  destruct (bp_leb A P x y) eqn:Hxy.
  - destruct (bp_leb A P y x) eqn:Hyx.
    + exfalso. apply H. split; [exact Hxy | exact Hyx].
    + exists y. rewrite bp_refl, Hyx. discriminate.
  - exists x. rewrite bp_refl, Hxy. discriminate.
Qed.

Theorem ax_threshold_view_separates : forall {A : Type} (P : BPre A) (X : AxSys A P)
    (x y : ax_state A P X),
  ~ (bp_le P (ax_rec A P X x) (ax_rec A P X y) /\ bp_le P (ax_rec A P X y) (ax_rec A P X x)) ->
  exists a, ax_rec bool two_pre (ax_view X a) x <> ax_rec bool two_pre (ax_view X a) y.
Proof.
  intros A P X x y H. destruct (ax_thresholds_separate P _ _ H) as [a Ha].
  exists a. exact Ha.
Qed.

Print Assumptions ax_exit_collision.
Print Assumptions ax_fibre_collapse_exit.
Print Assumptions ax_step_fibre_in_fibre.
Print Assumptions ax_compression_iff_fibres.
Print Assumptions shadow_merge_escape.
Print Assumptions ax_thresholds_separate.
Print Assumptions ax_threshold_view_separates.
