(** AxMerge: on a finite machine, moving along the axis forgets.

    The book's statement for one bit: on a finite machine a certificate that
    is never revoked is switched on only by a step that merges states, and
    charging every merge gives the toll.  Here it is for a record in any
    preorder.

    Results (all closed):

      ax_exit_merges_or_revokes   finite state space, a step that leaves the
                                  down-set of the record: the move merges two
                                  states, or it takes some other state out of
                                  the up-set of the same threshold.  No
                                  growth, no antisymmetry is assumed.
      ax_growth_exit_merges       with growth, the move merges.
      ax_a2_from_merge_price      finite, growing, every merging move costs 1:
                                  the axis toll is a theorem.
      ax_a2_iff_flipping_merges_priced
                                  under finiteness and growth the toll needs
                                  only that moves which leave the down-set
                                  somewhere and merge somewhere are priced.
      ax_flips_compression_bound  the quantitative form: if each unit of cost
                                  pays for one halving, then switching k states
                                  across a threshold while m are already across
                                  it costs at least log2 ((m+k)/m).
      ax_a2_from_compression      the toll from the halving price.

    Necessity (each premise has a witness):

      history_escape      infinite state space: an injective step that raises
                          the record at every step.
      toggle_escape       no growth: a bijection that raises and revokes.
      free_merge_escape   no merge price: finite, growing, raising at cost 0.

    The two-point case recovers [permanent_flip_is_not_injective]
    ([two_point_permanent_flip_merges]). *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import PermanentCertification.
From Kernel Require Import AxCore.

Lemma ax_NoDup_map_inj : forall {X Y : Type} (f : X -> Y) (l : list X),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup l -> NoDup (map f l).
Proof.
  intros X Y f l. induction l as [| x l IH]; intros Hinj Hnd; simpl; [constructor |].
  inversion Hnd as [| ? ? Hnotin Hl]; subst. constructor.
  - intro Hin. apply in_map_iff in Hin as [y [Hy Hyl]].
    assert (x = y) by (apply Hinj; [left; reflexivity | right; exact Hyl | symmetry; exact Hy]).
    subst y. exact (Hnotin Hyl).
  - apply IH; [| exact Hl]. intros a b Ha Hb. apply Hinj; right; assumption.
Qed.

Section Merge.

Variable A : Type.
Variable P : BPre A.
Variable X : AxSys A P.

Local Notation S := (ax_state A P X).
Local Notation I := (ax_instr A P X).
Local Notation step := (ax_step A P X).
Local Notation rc := (ax_rec A P X).
Local Notation cost := (ax_cost A P X).

Definition ax_finite (all : list S) : Prop := NoDup all /\ forall s, In s all.

Definition ax_step_injective (i : I) : Prop :=
  forall a b, step a i = step b i -> a = b.

(** The states at or above the point a. *)
Definition ax_up (all : list S) (a : A) : list S :=
  filter (fun t => bp_leb A P a (rc t)) all.

Lemma ax_up_spec : forall all a, ax_finite all ->
  forall t, In t (ax_up all a) <-> bp_le P a (rc t).
Proof.
  intros all a [_ Hall] t. unfold ax_up. rewrite filter_In. split.
  - intros [_ H]. exact H.
  - intro H. split; [apply Hall | exact H].
Qed.

Lemma ax_up_nodup : forall all a, ax_finite all -> NoDup (ax_up all a).
Proof. intros all a [Hnd _]. apply NoDup_filter. exact Hnd. Qed.

(** A move that leaves the down-set of the record merges two states, or
    takes some state out of the up-set of the threshold it crossed. *)
Theorem ax_exit_merges_or_revokes :
  forall all s i, ax_finite all -> ax_exits (X := X) s i ->
    ~ ax_step_injective i \/
    exists t, bp_le P (rc (step s i)) (rc t) /\
              ~ bp_le P (rc (step s i)) (rc (step t i)).
Proof.
  intros all s i Hfin Hex.
  set (a := rc (step s i)).
  set (T := ax_up all a).
  destruct (existsb (fun t => negb (bp_leb A P a (rc (step t i)))) T) eqn:E.
  - right. apply existsb_exists in E as [t [Ht Hneg]]. exists t. split.
    + apply (ax_up_spec all a Hfin). exact Ht.
    + intro H. unfold bp_le in H. rewrite H in Hneg. discriminate.
  - left. intro Hinj.
    assert (Hnorev : forall t, In t T -> bp_le P a (rc (step t i))).
    { intros t Ht. unfold bp_le.
      destruct (bp_leb A P a (rc (step t i))) eqn:Hb; [reflexivity |]. exfalso.
      assert (Hex' : existsb (fun t => negb (bp_leb A P a (rc (step t i)))) T = true).
      { apply existsb_exists. exists t. split; [exact Ht | rewrite Hb; reflexivity]. }
      congruence. }
    assert (Hs : ~ In s T).
    { intro H. apply (ax_up_spec all a Hfin) in H. exact (Hex H). }
    assert (HndL : NoDup (s :: T)).
    { constructor; [exact Hs | apply ax_up_nodup; exact Hfin]. }
    assert (Hndm : NoDup (map (fun t => step t i) (s :: T))).
    { apply ax_NoDup_map_inj; [| exact HndL].
      intros x y _ _ H. exact (Hinj x y H). }
    assert (Hincl : incl (map (fun t => step t i) (s :: T)) T).
    { intros y Hy. apply in_map_iff in Hy as [x [<- Hx]]. destruct Hx as [<- | Hx].
      - apply (ax_up_spec all a Hfin). apply bp_le_refl.
      - apply (ax_up_spec all a Hfin). apply Hnorev. exact Hx. }
    pose proof (NoDup_incl_length Hndm Hincl) as Hlen.
    rewrite map_length in Hlen. simpl in Hlen. lia.
Qed.

(** With growth there is nothing to revoke, so the move merges. *)
Theorem ax_growth_exit_merges :
  forall all s i, ax_finite all -> ax_grows (X := X) -> ax_exits (X := X) s i ->
    ~ ax_step_injective i.
Proof.
  intros all s i Hfin Hg Hex.
  destruct (ax_exit_merges_or_revokes all s i Hfin Hex) as [H | [t [Ht Hnot]]];
    [exact H |].
  exfalso. apply Hnot. eapply bp_le_trans; [exact Ht | apply Hg].
Qed.

(** Landauer on the logic: a move that merges two states costs at least 1. *)
Definition ax_merging_priced : Prop :=
  forall i, ~ ax_step_injective i -> cost i >= 1.

(** The axis toll is a consequence of finiteness, growth and merge pricing. *)
Theorem ax_a2_from_merge_price :
  forall all, ax_finite all -> ax_grows (X := X) -> ax_merging_priced ->
    ax_a2 (X := X).
Proof.
  intros all Hfin Hg Hp s i Hex. apply Hp. eapply ax_growth_exit_merges; eauto.
Qed.

(** Merge pricing asks for more than the toll needs: the toll is exactly
    that every move which leaves the down-set somewhere, and merges, is
    priced. *)
Theorem ax_a2_iff_flipping_merges_priced :
  forall all, ax_finite all -> ax_grows (X := X) ->
    (ax_a2 (X := X) <->
     forall i, (exists s, ax_exits (X := X) s i) -> ~ ax_step_injective i -> cost i >= 1).
Proof.
  intros all Hfin Hg. split.
  - intros Ha i [s Hs] _. exact (Ha s i Hs).
  - intros H s i Hs. apply H; [exists s; exact Hs |].
    eapply ax_growth_exit_merges; eauto.
Qed.

(** ** The quantitative form *)

Variable eq_dec : forall a b : S, {a = b} + {a <> b}.

Definition ax_image_size (i : I) (D : list S) : nat :=
  length (nodup eq_dec (map (fun t => step t i) D)).

(** Each unit of cost pays for at most one halving of the number of states. *)
Definition ax_compression_priced : Prop :=
  forall i D, NoDup D -> length D <= 2 ^ cost i * ax_image_size i D.

Lemma ax_nodup_app_disjoint : forall (l l' : list S),
  NoDup l -> NoDup l' -> (forall a, In a l -> ~ In a l') -> NoDup (l ++ l').
Proof.
  intros l l' Hl Hl' Hdisj. induction l as [| x xs IH]; simpl.
  - exact Hl'.
  - inversion Hl as [| ? ? Hnotin Hxs]; subst.
    constructor.
    + intro Hin. apply in_app_or in Hin as [Hin | Hin].
      * exact (Hnotin Hin).
      * exact (Hdisj x (or_introl eq_refl) Hin).
    + apply IH; [exact Hxs |]. intros a Ha. apply Hdisj. right. exact Ha.
Qed.

(** Switching k states across a threshold while m are already across costs
    enough that m + k <= 2^cost * m. *)
Theorem ax_flips_compression_bound :
  forall all a i F,
    ax_finite all -> ax_grows (X := X) -> ax_compression_priced ->
    NoDup F ->
    (forall s, In s F -> ~ bp_le P a (rc s) /\ bp_le P a (rc (step s i))) ->
    length F + length (ax_up all a) <= 2 ^ cost i * length (ax_up all a).
Proof.
  intros all a i F Hfin Hg Hprice HndF HF.
  set (C := ax_up all a).
  assert (HndC : NoDup C) by (apply ax_up_nodup; exact Hfin).
  assert (HinC : forall t, In t C <-> bp_le P a (rc t)) by (apply ax_up_spec; exact Hfin).
  assert (Hnd : NoDup (F ++ C)).
  { apply ax_nodup_app_disjoint; [exact HndF | exact HndC |].
    intros b HbF HbC. apply HinC in HbC. exact ((proj1 (HF b HbF)) HbC). }
  assert (Himg : incl (nodup eq_dec (map (fun t => step t i) (F ++ C))) C).
  { intros y Hy. apply nodup_In in Hy.
    apply in_map_iff in Hy as [x [<- Hx]].
    apply HinC. apply in_app_or in Hx as [HxF | HxC].
    - exact (proj2 (HF x HxF)).
    - apply HinC in HxC. eapply bp_le_trans; [exact HxC | apply Hg]. }
  assert (Hle : ax_image_size i (F ++ C) <= length C).
  { apply NoDup_incl_length; [apply NoDup_nodup | exact Himg]. }
  pose proof (Hprice i (F ++ C) Hnd) as Hc.
  rewrite app_length in Hc.
  apply Nat.le_trans with (m := 2 ^ cost i * ax_image_size i (F ++ C));
    [exact Hc | apply Nat.mul_le_mono_l; exact Hle].
Qed.

(** The halving price gives the toll. *)
Theorem ax_a2_from_compression :
  forall all, ax_finite all -> ax_grows (X := X) -> ax_compression_priced ->
    ax_a2 (X := X).
Proof.
  intros all Hfin Hg Hprice s i Hex.
  set (a := rc (step s i)).
  assert (Hs : ~ bp_le P a (rc s)) by exact Hex.
  assert (Hf : forall s', In s' [s] -> ~ bp_le P a (rc s') /\ bp_le P a (rc (step s' i))).
  { intros s' [<- | []]. split; [exact Hs | apply bp_le_refl]. }
  pose proof (ax_flips_compression_bound all a i [s] Hfin Hg Hprice
                (NoDup_cons s (in_nil (a := s)) (NoDup_nil _)) Hf) as Hb.
  assert (Hpos : 1 <= length (ax_up all a)).
  { assert (Hin : In (step s i) (ax_up all a))
      by (apply (ax_up_spec all a Hfin); apply bp_le_refl).
    destruct (ax_up all a); [contradiction | simpl; lia]. }
  simpl in Hb. destruct (cost i) as [| c]; [simpl in Hb; lia | lia].
Qed.

End Merge.

Arguments ax_finite {A P} X.
Arguments ax_step_injective {A P} X _.
Arguments ax_merging_priced {A P} X.
Arguments ax_up {A P} X.
Arguments ax_exit_merges_or_revokes {A P X} _ _ _ _ _.
Arguments ax_growth_exit_merges {A P X} _ _ _ _ _ _.
Arguments ax_a2_from_merge_price {A P X} _ _ _ _.

(** * The one-bit case recovers the book's theorem *)

Theorem two_point_permanent_flip_merges :
  forall (S I : Type) (step : S -> I -> S) (cert : S -> bool) (all : list S) s i,
    finite_states all -> permanent step cert ->
    cert s = false -> cert (step s i) = true ->
    ~ step_injective step i.
Proof.
  intros S I step cert all s i Hfin Hperm Hs Hflip.
  set (X := mk_axsys bool two_pre S I step (fun _ => 0) cert).
  assert (Hg : ax_grows (X := X)).
  { intros s0 i0. simpl. unfold bp_le. simpl.
    destruct (cert s0) eqn:E; [rewrite (Hperm s0 i0 E); reflexivity | reflexivity]. }
  assert (Hex : ax_exits (X := X) s i).
  { unfold ax_exits. simpl. unfold bp_le. simpl. rewrite Hs, Hflip. discriminate. }
  exact (ax_growth_exit_merges (X := X) all s i Hfin Hg Hex).
Qed.

(** * Each premise is needed *)

(** Infinite state space: a counter.  The step is injective, the record is
    the counter, every step raises it, and merge pricing holds at cost 0
    because nothing merges. *)
Definition history_sys : AxSys nat nat_pre :=
  mk_axsys nat nat_pre nat unit (fun n _ => S n) (fun _ => 0) (fun n => n).

Theorem history_escape :
  ax_grows (X := history_sys) /\
  ax_merging_priced history_sys /\
  ax_step_injective history_sys tt /\
  (forall s, ax_exits (X := history_sys) s tt) /\
  ~ ax_a2 (X := history_sys).
Proof.
  assert (Hex : forall s, ax_exits (X := history_sys) s tt).
  { intro s. unfold ax_exits. simpl. rewrite nat_pre_le. lia. }
  repeat split.
  - intros s i. simpl. rewrite nat_pre_le. lia.
  - intros i H. exfalso. apply H. intros a b Hab. simpl in Hab. lia.
  - intros a b Hab. simpl in Hab. lia.
  - exact Hex.
  - intro H. specialize (H 0 tt (Hex 0)). simpl in H. lia.
Qed.

(** No growth: negation on the two-point order is a bijection that raises
    and revokes. *)
Definition toggle_sys : AxSys bool two_pre :=
  mk_axsys bool two_pre bool unit (fun b _ => negb b) (fun _ => 0) (fun b => b).

Theorem toggle_escape :
  ax_finite toggle_sys [false; true] /\
  ax_merging_priced toggle_sys /\
  ax_exits (X := toggle_sys) false tt /\
  ~ ax_grows (X := toggle_sys) /\
  ~ ax_a2 (X := toggle_sys).
Proof.
  assert (Hex : ax_exits (X := toggle_sys) false tt)
    by (unfold ax_exits, bp_le; simpl; discriminate).
  repeat split.
  - repeat constructor; simpl; intuition discriminate.
  - intro s. destruct s; simpl; auto.
  - intros i H. exfalso. apply H. intros a b Hab. simpl in Hab.
    destruct a, b; simpl in Hab; congruence.
  - exact Hex.
  - intro H. specialize (H true tt). unfold bp_le in H. simpl in H. discriminate.
  - intro H. specialize (H false tt Hex). simpl in H. lia.
Qed.

(** No merge price: finite, growing, raising at cost 0 by a merge. *)
Definition stamp_sys : AxSys bool two_pre :=
  mk_axsys bool two_pre bool unit (fun _ _ => true) (fun _ => 0) (fun b => b).

Theorem free_merge_escape :
  ax_finite stamp_sys [false; true] /\
  ax_grows (X := stamp_sys) /\
  ~ ax_merging_priced stamp_sys /\
  ~ ax_a2 (X := stamp_sys).
Proof.
  assert (Hn : ~ ax_step_injective stamp_sys tt).
  { intro Hinj. specialize (Hinj false true eq_refl). discriminate. }
  assert (Hex : ax_exits (X := stamp_sys) false tt)
    by (unfold ax_exits, bp_le; simpl; discriminate).
  repeat split.
  - repeat constructor; simpl; intuition discriminate.
  - intro s. destruct s; simpl; auto.
  - intros s i. destruct s; simpl; unfold bp_le; simpl; reflexivity.
  - intro H. specialize (H tt Hn). simpl in H. lia.
  - intro H. specialize (H false tt Hex). simpl in H. lia.
Qed.

Print Assumptions ax_exit_merges_or_revokes.
Print Assumptions ax_growth_exit_merges.
Print Assumptions ax_a2_from_merge_price.
Print Assumptions ax_a2_iff_flipping_merges_priced.
Print Assumptions ax_flips_compression_bound.
Print Assumptions ax_a2_from_compression.
Print Assumptions two_point_permanent_flip_merges.
Print Assumptions history_escape.
Print Assumptions toggle_escape.
Print Assumptions free_merge_escape.
