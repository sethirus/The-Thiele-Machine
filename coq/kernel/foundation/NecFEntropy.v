(** NecFEntropy: the entropy road to the toll, at its limit.

    - A move that forgets nothing removes no bits, and conversely: a move
      leaves the entropy of every spread unchanged exactly when it is
      injective ([nec_f_entropy_invariant_iff_injective]).
    - The bits removed are positive exactly when two different states, both
      with positive chance, land together ([nec_f_drop_pos_iff_support_merge]);
      when no two such states land together the move removes nothing
      ([nec_f_drop_zero_of_support_injective]).
    - A known state: a spread loses no bits under every move whatever exactly
      when its chance sits on one state ([nec_f_zero_drop_every_move_iff_one_state]).
    - The entropy toll needs each premise: without entropy pricing (the
      repo's free_merge_escapes), without finiteness
      ([nec_f_entropy_toll_needs_finite]), without permanence
      ([nec_f_entropy_toll_needs_permanent]). Entropy pricing is more than A2
      needs ([nec_f_a2_without_entropy_pricing]).
    - Heat: k_B T > 0 is needed for positive heat ([nec_f_heat_positive_needs_kT]);
      positive chance on the flipped state and on the yes-state are both
      needed for positive heat ([nec_f_full_support_needs_s],
      [nec_f_full_support_needs_yes]).

    This file uses the real numbers and rests on the standard library's
    classical axioms for them (functional extensionality, the two real
    decidability axioms, excluded middle). *)

From Coq Require Import List Bool Arith Lia.
From Coq Require Import Reals Lra.
From Coq Require Import Logic.Classical_Prop.
Import ListNotations.
From Kernel Require Import PermanentCertification.
From Kernel Require Import PermanentRecordPricing.
From Kernel Require Import PermanentCertificationEntropy.
From Kernel Require Import FiniteCertMachine.
From Kernel Require Import NecFMerge.

Open Scope R_scope.

Section Moves.

Context {A : Type}.
Variable eq_dec : forall a b : A, {a = b} + {a <> b}.

Lemma nec_f_uniform_pair_pos :
  forall x y z, In z [x; y] -> 0 < uniform_on eq_dec [x; y] z.
Proof.
  intros x y z Hz. unfold uniform_on, in_b.
  destruct (in_dec eq_dec z [x; y]) as [_ | Hn]; [| contradiction].
  apply Rinv_0_lt_compat. simpl. lra.
Qed.

(** Entropy is unchanged for every spread exactly when the move is injective. *)
Theorem nec_f_entropy_invariant_iff_injective :
  forall (all : list A) (f : A -> A),
    NoDup all -> (forall a, In a all) ->
    ((forall x y, f x = f y -> x = y) <->
     (forall p, distribution all p -> entropy all (push eq_dec all f p) = entropy all p)).
Proof.
  intros all f Hnd Hall. split.
  - intros Hinj p _. apply step_entropy_invariant_if_injective; assumption.
  - intros Hinv x y Hf. destruct (eq_dec x y) as [E | Hne]; [exact E | exfalso].
    set (p := uniform_on eq_dec [x; y]).
    assert (Hp : distribution all p).
    { apply uniform_on_distribution; [exact Hnd | | intros a _; apply Hall | simpl; lia].
      constructor; [simpl; intros [H | []]; congruence | constructor; [intros [] | constructor]]. }
    pose proof (Hinv p Hp) as E.
    pose proof (entropy_drop_pos_of_support_merge eq_dec all f p x y Hnd Hall (proj1 Hp) Hne Hf
                  (nec_f_uniform_pair_pos x y x (or_introl eq_refl))
                  (nec_f_uniform_pair_pos x y y (or_intror (or_introl eq_refl)))) as D.
    lra.
Qed.

(** Injective on the states with positive chance: the move removes nothing. *)
Theorem nec_f_drop_zero_of_support_injective :
  forall (all : list A) (f : A -> A) (p : A -> R),
    NoDup all -> (forall a, In a all) -> (forall a, 0 <= p a) ->
    (forall x x', 0 < p x -> 0 < p x' -> f x = f x' -> x = x') ->
    entropy all p - entropy all (push eq_dec all f p) = 0.
Proof.
  intros all f p Hnd Hall Hnn Hinj.
  rewrite entropy_drop_as_point_sum by assumption.
  apply rsum_zero. intros x Hx.
  destruct (Rlt_dec 0 (p x)) as [Hp | _]; [| reflexivity].
  assert (Hq : push eq_dec all f p (f x) = p x).
  { unfold push.
    rewrite (rsum_ext_in all (fun z => if eq_dec (f z) (f x) then p z else 0)
               (fun z => if eq_dec x z then p z else 0)).
    - apply rsum_select; [exact Hnd | exact Hx].
    - intros z _. destruct (eq_dec (f z) (f x)) as [Ef | Nf]; destruct (eq_dec x z) as [Ez | Nz].
      + reflexivity.
      + destruct (Rlt_dec 0 (p z)) as [Hz | Hz].
        * exfalso. apply Nz. symmetry. exact (Hinj z x Hz Hp Ef).
        * specialize (Hnn z). lra.
      + subst z. contradiction.
      + reflexivity. }
  rewrite Hq. ring.
Qed.

(** The bits removed are positive exactly when two different states with
    positive chance land together. *)
Theorem nec_f_drop_pos_iff_support_merge :
  forall (all : list A) (f : A -> A) (p : A -> R),
    NoDup all -> (forall a, In a all) -> (forall a, 0 <= p a) ->
    (entropy all p - entropy all (push eq_dec all f p) > 0 <->
     exists x x', x <> x' /\ 0 < p x /\ 0 < p x' /\ f x = f x').
Proof.
  intros all f p Hnd Hall Hnn. split.
  - intro Hpos. apply NNPP. intro Hno.
    assert (Hinj : forall x x', 0 < p x -> 0 < p x' -> f x = f x' -> x = x').
    { intros x x' Hx Hx' Hf. destruct (eq_dec x x') as [E | Hne]; [exact E |].
      exfalso. apply Hno. exists x, x'. repeat split; assumption. }
    pose proof (nec_f_drop_zero_of_support_injective all f p Hnd Hall Hnn Hinj). lra.
  - intros [x [x' [Hne [Hx [Hx' Hf]]]]].
    exact (entropy_drop_pos_of_support_merge eq_dec all f p x x' Hnd Hall Hnn Hne Hf Hx Hx').
Qed.

(** A spread loses no bits under every move exactly when its chance sits on
    one state. *)
Theorem nec_f_zero_drop_every_move_iff_one_state :
  forall (all : list A) (p : A -> R),
    NoDup all -> (forall a, In a all) -> (forall a, 0 <= p a) ->
    ((forall f : A -> A, entropy all p - entropy all (push eq_dec all f p) = 0) <->
     (forall x x', 0 < p x -> 0 < p x' -> x = x')).
Proof.
  intros all p Hnd Hall Hnn. split.
  - intros H x x' Hx Hx'. destruct (eq_dec x x') as [E | Hne]; [exact E | exfalso].
    set (f := fun a => if eq_dec a x' then x else a).
    assert (Hf : f x = f x').
    { unfold f. destruct (eq_dec x x') as [E | _]; [contradiction |].
      destruct (eq_dec x' x') as [_ | C]; [reflexivity | contradiction]. }
    pose proof (entropy_drop_pos_of_support_merge eq_dec all f p x x' Hnd Hall Hnn Hne Hf Hx Hx').
    specialize (H f). lra.
  - intros H f. apply nec_f_drop_zero_of_support_injective; try assumption.
    intros x x' Hx Hx' _. exact (H x x' Hx Hx').
Qed.

End Moves.

(** * The entropy toll: each premise is needed *)

(** Without finiteness: the history machine, with an empty list of states.
    No spread lives on it, so entropy pricing holds at cost zero; the reading
    is permanent; A2 fails. *)
Theorem nec_f_entropy_toll_needs_finite :
  entropy_priced history_step (list_eq_dec bool_dec) [] (fun _ : unit => 0%nat) /\
  permanent history_step history_cert /\
  ~ a2_holds history_step history_cert (fun _ : unit => 0%nat).
Proof.
  destruct unbounded_history_escapes as [_ [Hperm [H0 H1]]].
  split; [| split; [exact Hperm |]].
  - intros i p [_ Hs]. simpl in Hs. lra.
  - intro Ha. specialize (Ha [] tt H0 H1). simpl in Ha. lia.
Qed.

(** Without permanence: negation on one bit, at cost zero, is entropy priced. *)
Theorem nec_f_entropy_toll_needs_permanent :
  finite_states [false; true] /\
  entropy_priced flip_step bool_dec [false; true] (fun _ : unit => 0%nat) /\
  ~ a2_holds flip_step (fun b => b) (fun _ : unit => 0%nat).
Proof.
  destruct revocable_certificate_escapes as [Hinj [H1 H2]].
  assert (Hfin : finite_states [false; true]).
  { split; [repeat constructor; simpl; intuition discriminate | intros []; simpl; tauto]. }
  split; [exact Hfin | split].
  - intros [] p _. rewrite step_entropy_invariant_if_injective.
    + simpl. lra.
    + exact (proj1 Hfin).
    + exact (proj2 Hfin).
    + intros a b E. exact (Hinj a b E).
  - intro Ha. specialize (Ha false tt eq_refl H1). simpl in Ha. lia.
Qed.

(** Entropy pricing is more than A2 needs: the eight-state machine with a
    free jump meets A2 and is not entropy priced. *)
Theorem nec_f_a2_without_entropy_pricing :
  a2_holds fstep fcert nec_f_free_jump_cost /\
  ~ entropy_priced fstep fstate_eq_dec all_fstates nec_f_free_jump_cost.
Proof.
  destruct nec_f_a2_without_merge_pricing as [_ [_ [Ha _]]].
  split; [exact Ha |]. intro Hp.
  set (p := uniform_on fstate_eq_dec [(L0, false); (L1, false)]).
  assert (Hd : distribution all_fstates p).
  { apply uniform_on_distribution; [exact (proj1 fin_finite) | | intros a _; apply (proj2 fin_finite) | simpl; lia].
    repeat constructor; simpl; intuition discriminate. }
  pose proof (Hp (FJump L0) p Hd) as Hc.
  assert (Hz : INR (nec_f_free_jump_cost (FJump L0)) = 0) by reflexivity.
  assert (Hne : (L0, false) <> (L1, false)) by discriminate.
  pose proof (entropy_drop_pos_of_support_merge fstate_eq_dec all_fstates (fun s => fstep s (FJump L0)) p
                (L0, false) (L1, false) (proj1 fin_finite) (proj2 fin_finite) (proj1 Hd) Hne eq_refl
                (nec_f_uniform_pair_pos fstate_eq_dec _ _ _ (or_introl eq_refl))
                (nec_f_uniform_pair_pos fstate_eq_dec _ _ _ (or_intror (or_introl eq_refl)))).
  lra.
Qed.

(** * Heat: what positivity needs *)

(** With k_B T = 0, zero heat meets Landauer's premise for any drop. *)
Theorem nec_f_heat_positive_needs_kT :
  forall dH, landauer_heat 0 0 dH /\ ~ (0 > 0).
Proof. intro dH. unfold landauer_heat. split; [right; ring | lra]. Qed.

Definition nec_f_stamped_dec : forall a b : Sheet, {a = b} + {a <> b}.
Proof. decide equality. Defined.

(** Chance only on the blank sheet (the flipped state), none on the stamped
    one: the stamp removes no bits, so zero heat meets Landauer's premise. *)
Theorem nec_f_full_support_needs_yes :
  forall kT,
    0 < point_mass nec_f_stamped_dec Blank Blank /\
    point_mass nec_f_stamped_dec Blank Stamped = 0 /\
    landauer_heat kT 0
      (entropy [Blank; Stamped] (point_mass nec_f_stamped_dec Blank) -
       entropy [Blank; Stamped] (push nec_f_stamped_dec [Blank; Stamped] (fun s => stamp_step s tt)
                                   (point_mass nec_f_stamped_dec Blank))).
Proof.
  intro kT. split; [unfold point_mass; simpl; lra | split; [reflexivity |]].
  unfold landauer_heat.
  rewrite (known_state_step_removes_no_entropy nec_f_stamped_dec).
  - right. ring.
  - exact (proj1 sheets_finite).
  - exact (proj2 sheets_finite).
Qed.

(** Chance only on the stamped sheet (the yes-state), none on the blank one. *)
Theorem nec_f_full_support_needs_s :
  forall kT,
    point_mass nec_f_stamped_dec Stamped Blank = 0 /\
    0 < point_mass nec_f_stamped_dec Stamped Stamped /\
    landauer_heat kT 0
      (entropy [Blank; Stamped] (point_mass nec_f_stamped_dec Stamped) -
       entropy [Blank; Stamped] (push nec_f_stamped_dec [Blank; Stamped] (fun s => stamp_step s tt)
                                   (point_mass nec_f_stamped_dec Stamped))).
Proof.
  intro kT. split; [reflexivity | split; [unfold point_mass; simpl; lra |]].
  unfold landauer_heat.
  rewrite (known_state_step_removes_no_entropy nec_f_stamped_dec).
  - right. ring.
  - exact (proj1 sheets_finite).
  - exact (proj2 sheets_finite).
Qed.

Print Assumptions nec_f_entropy_invariant_iff_injective.
Print Assumptions nec_f_drop_zero_of_support_injective.
Print Assumptions nec_f_drop_pos_iff_support_merge.
Print Assumptions nec_f_zero_drop_every_move_iff_one_state.
Print Assumptions nec_f_entropy_toll_needs_finite.
Print Assumptions nec_f_entropy_toll_needs_permanent.
Print Assumptions nec_f_a2_without_entropy_pricing.
Print Assumptions nec_f_heat_positive_needs_kT.
Print Assumptions nec_f_full_support_needs_yes.
Print Assumptions nec_f_full_support_needs_s.
