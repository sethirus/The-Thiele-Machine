(** NecFNarrowing: learning is free, committing is not, at the limit.

    - The machine's own narrowing. The bound
      log2_up |D| <= cost(t) + log2_up |img_t(D)| holds for every run exactly
      when the halving price holds ([nec_f_machine_narrowing_iff_halving]).
      Its one-move case is the bit price, and the bit price is equivalent to
      the halving price ([nec_f_bit_price_iff_halving]); so the halving price
      is not stronger than needed, it is exactly what the theorem needs. The
      no-repeats hypothesis on D is needed ([nec_f_narrowing_needs_nodup]),
      and the bound is met with equality for every cost c and every m >= 1
      ([nec_f_narrowing_equality]).
    - The observer. Merge pricing alone already charges the demon's wipe at
      least one ([nec_f_wipe_under_merge_pricing]). The claim that observer
      narrowing is paid fails already on a two-state machine with the empty
      run ([nec_f_two_state_observer_free]); a one-state machine satisfies it
      ([nec_f_one_state_observer_priced]), so for the claim as stated the
      smallest refuting machine has two states, not four.
    - Free teaching. A machine with two or fewer states never teaches an
      observer anything during a run, whatever its prices and whatever the
      run costs, and with any candidate list at all
      ([nec_f_two_states_never_teach]). So the minimum of three needs no price
      at all, and three is attained (the repo's
      free_incremental_narrowing_with_three). *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.
From Kernel Require Import PermanentCertification.
From Kernel Require Import PermanentRecordPricing.
From Kernel Require Import FiniteCertMachine.
From Kernel Require Import KnowledgeNarrowing.
From Kernel Require Import KnowledgeNarrowingIncremental.
From Kernel Require Import KnowledgeNarrowingMinimal.
From Kernel Require Import NecFSqueeze.

Section Price.

Variables (S I : Type).
Variable step : S -> I -> S.
Variable cost : I -> nat.
Variable eq_dec : forall a b : S, {a = b} + {a <> b}.

(** The bit price: each move pays for the drop in rounded bits it causes. *)
Definition nec_f_bit_price : Prop :=
  forall i D, NoDup D -> Nat.log2_up (length D) <= cost i + Nat.log2_up (image_size step eq_dec i D).

Lemma nec_f_log_of_mul :
  forall n c m, n <= 2 ^ c * m -> Nat.log2_up n <= c + Nat.log2_up m.
Proof.
  intros n c m H. destruct m as [| m].
  - rewrite Nat.mul_0_r in H. assert (n = 0) as -> by lia. simpl. lia.
  - rewrite <- Nat.log2_up_mul_pow2 by lia. apply Nat.log2_up_le_mono. lia.
Qed.

Lemma nec_f_halving_gives_bit_price :
  compression_priced step cost eq_dec -> nec_f_bit_price.
Proof. intros H i D HD. apply nec_f_log_of_mul. apply H. exact HD. Qed.

Lemma nec_f_fiber_image_le_one :
  forall i (D : list S) y,
    image_size step eq_dec i (filter (hits S S eq_dec (fun x => step x i) y) D) <= 1.
Proof.
  intros i D y. unfold image_size. change 1 with (length [y]).
  apply NoDup_incl_length; [apply NoDup_nodup |].
  intros z Hz. apply nodup_In, in_map_iff in Hz as [x [<- Hx]].
  apply filter_In in Hx as [_ Hh]. unfold hits in Hh.
  destruct (eq_dec (step x i) y) as [E | _]; [left; symmetry; exact E | discriminate].
Qed.

Lemma nec_f_bit_price_gives_halving :
  nec_f_bit_price -> compression_priced step cost eq_dec.
Proof.
  intros Hb i D HD. unfold image_size.
  apply fiber_bound_compression; [exact HD |]. intro y.
  set (Fy := filter (hits S S eq_dec (fun x => step x i) y) D).
  assert (HFy : NoDup Fy) by (apply NoDup_filter; exact HD).
  pose proof (Hb i Fy HFy) as H.
  pose proof (nec_f_fiber_image_le_one i D y) as Him. fold Fy in Him.
  assert (Hl : Nat.log2_up (image_size step eq_dec i Fy) <= 0).
  { apply Nat.le_trans with (Nat.log2_up 1); [apply Nat.log2_up_le_mono; exact Him | reflexivity]. }
  destruct (length Fy) as [| n] eqn:Hn; [lia |].
  apply Nat.log2_up_le_pow2; [lia | lia].
Qed.

Theorem nec_f_bit_price_iff_halving : nec_f_bit_price <-> compression_priced step cost eq_dec.
Proof. split; [apply nec_f_bit_price_gives_halving | apply nec_f_halving_gives_bit_price]. Qed.

(** The machine's own narrowing under the bit price, by the same induction. *)
Theorem nec_f_run_narrowing_bit :
  nec_f_bit_price ->
  forall t D, NoDup D ->
    Nat.log2_up (length D) <= trace_cost cost t + Nat.log2_up (length (run_image step eq_dec t D)).
Proof.
  intros Hb t. induction t as [| i t IH]; intros D HD.
  - simpl. unfold run_image. simpl. rewrite map_id, nodup_fixed_point by exact HD. lia.
  - set (D1 := nodup eq_dec (map (fun s => step s i) D)).
    pose proof (Hb i D HD) as H1. unfold image_size in H1. fold D1 in H1.
    pose proof (IH D1 (NoDup_nodup _ _)) as H2.
    unfold D1 in H2. rewrite (run_image_step S I step eq_dec i t D) in H2.
    simpl trace_cost. fold D1 in H2. lia.
Qed.

Definition nec_f_machine_narrowing : Prop :=
  forall t D, NoDup D ->
    Nat.log2_up (length D) <= trace_cost cost t + Nat.log2_up (length (run_image step eq_dec t D)).

(** The machine's own narrowing holds for every run exactly when the halving
    price holds. *)
Theorem nec_f_machine_narrowing_iff_halving :
  nec_f_machine_narrowing <-> compression_priced step cost eq_dec.
Proof.
  unfold nec_f_machine_narrowing. split.
  - intro H. apply nec_f_bit_price_gives_halving. intros i D HD.
    specialize (H [i] D HD). simpl in H. rewrite Nat.add_0_r in H. exact H.
  - intros H t D HD. apply nec_f_run_narrowing_bit; [| exact HD].
    apply nec_f_halving_gives_bit_price. exact H.
Qed.

End Price.

(** No repeats in D is needed: a list naming one demon state twice. *)
Theorem nec_f_narrowing_needs_nodup :
  compression_priced dstep dcost dstate_eq_dec /\
  ~ (Nat.log2_up (length [(false, false); (false, false)])
       <= trace_cost dcost [] +
          Nat.log2_up (length (run_image dstep dstate_eq_dec [] [(false, false); (false, false)]))).
Proof. split; [exact demon_compression_priced | vm_compute; lia]. Qed.

(** Equality, for every cost c and every m >= 1: on the grid of NecFSqueeze
    with m rows and 2^c columns, the one move run from every state. *)
Theorem nec_f_narrowing_equality :
  forall m c, 0 < m ->
    Nat.log2_up (length (nec_f_grid_all m c))
    = trace_cost (nec_f_grid_cost c) [tt] +
      Nat.log2_up (length (run_image (nec_f_grid_step m c) (nec_f_grid_eq_dec m c) [tt]
                                     (nec_f_grid_all m c))).
Proof.
  intros m c Hm.
  destruct (nec_f_squeeze_tight m c) as [Hfin [Hperm [Hpr [_ [_ [_ [Hy Hcount]]]]]]].
  set (R := run_image (nec_f_grid_step m c) (nec_f_grid_eq_dec m c) [tt] (nec_f_grid_all m c)).
  assert (Hall : length (nec_f_grid_all m c) = 2 ^ c * m).
  { unfold nec_f_grid_all, NecFGrid. rewrite prod_length, !nec_f_enum_length. lia. }
  assert (Hle : length R <= m).
  { rewrite <- Hy. apply NoDup_incl_length; [apply run_image_nodup |].
    intros z Hz. apply run_image_spec in Hz as [x [_ <-]].
    apply (certified_states_spec _ _ _ Hfin). reflexivity. }
  assert (Hge : 2 ^ c * m <= 2 ^ c * length R).
  { rewrite <- Hall. pose proof (run_narrowing_priced _ _ (nec_f_grid_step m c) (nec_f_grid_cost c)
                                    (nec_f_grid_eq_dec m c) Hpr [tt] (nec_f_grid_all m c)
                                    (proj1 Hfin)) as H.
    simpl trace_cost in H. rewrite Nat.add_0_r in H. exact H. }
  assert (HR : length R = m).
  { pose proof (nec_f_pow_pos c). apply Nat.le_antisymm; [exact Hle |].
    apply (Nat.mul_le_mono_pos_l _ _ (2 ^ c)); [lia | exact Hge]. }
  rewrite HR, Hall. simpl trace_cost. unfold nec_f_grid_cost.
  rewrite Nat.mul_comm, Nat.log2_up_mul_pow2 by lia. lia.
Qed.

(** * The observer *)

(** Merge pricing alone charges the wipe. *)
Theorem nec_f_wipe_under_merge_pricing :
  forall cost : DemonInstr -> nat, merging_steps_priced dstep cost -> cost Wipe >= 1.
Proof. intros cost H. apply H. exact wipe_merges. Qed.

(** One is attained: the demon's own price meets the halving price. *)
Theorem nec_f_wipe_one_attained :
  compression_priced dstep dcost dstate_eq_dec /\ dcost Wipe = 1.
Proof. split; [exact demon_compression_priced | reflexivity]. Qed.

(** Two states refute the observer claim with the empty run: the first look
    already tells them apart. The machine does nothing and costs nothing. *)
Definition nec_f_still (b : bool) (_ : unit) : bool := b.

Theorem nec_f_two_state_observer_free :
  finite_states [false; true] /\
  compression_priced nec_f_still (fun _ => 0) bool_dec /\
  ~ observer_narrowing_priced nec_f_still (fun _ => 0) (fun b : bool => b) bool_dec.
Proof.
  split; [split; [repeat constructor; simpl; intuition discriminate | intros []; simpl; tauto] |].
  split; [apply nec_f_injective_halving_free; intros [] a b H; exact H |].
  intro H. specialize (H [false; true] [] false).
  assert (Hnd : NoDup [false; true]) by (repeat constructor; simpl; intuition discriminate).
  specialize (H Hnd (or_introl eq_refl)). vm_compute in H. lia.
Qed.

(** A one-state machine satisfies the observer claim for every cost. *)
Theorem nec_f_one_state_observer_priced :
  forall (S I O : Type) (all : list S) (step : S -> I -> S) (cost : I -> nat)
         (obs : S -> O) (od : forall a b : O, {a = b} + {a <> b}),
    finite_states all -> length all <= 1 ->
    observer_narrowing_priced step cost obs od.
Proof.
  intros S I O all step cost obs od [_ Hall] Hlen Omega t s0 HndO _.
  assert (HO : length Omega <= 1).
  { apply Nat.le_trans with (length all); [| exact Hlen].
    apply NoDup_incl_length; [exact HndO | intros x _; apply Hall]. }
  assert (Hz : Nat.log2_up (length Omega) = 0).
  { destruct (length Omega) as [| [| n]]; [reflexivity | reflexivity | lia]. }
  rewrite Hz. simpl. lia.
Qed.

(** * Two states never teach *)

Section TwoNeverTeach.

Variables (S I O : Type).
Variable step : S -> I -> S.
Variable obs : S -> O.
Variable od : forall a b : O, {a = b} + {a <> b}.
Variable eq_dec : forall a b : S, {a = b} + {a <> b}.

Lemma nec_f_seen_head : forall s t, exists rest, seen S I step O obs s t = obs s :: rest.
Proof. intros s [| i t]; simpl; eexists; reflexivity. Qed.

Lemma nec_f_view_first_differs :
  forall t s0 s, obs s <> obs s0 -> same_view S I step O obs od t s0 s = false.
Proof.
  intros t s0 s Hne. unfold same_view.
  destruct (list_eq_dec od (seen S I step O obs s t) (seen S I step O obs s0 t)) as [E | _];
    [| reflexivity].
  exfalso. destruct (nec_f_seen_head s t) as [r1 H1]. destruct (nec_f_seen_head s0 t) as [r2 H2].
  rewrite H1, H2 in E. inversion E. contradiction.
Qed.

Lemma nec_f_view_constant :
  forall t s0 s, (forall x, obs x = obs s0) -> same_view S I step O obs od t s0 s = true.
Proof.
  intros t s0 s Hc. unfold same_view, seen.
  rewrite (map_constant S O obs (obs s0) _ Hc), (map_constant S O obs (obs s0) _ Hc),
          !states_along_length.
  destruct (list_eq_dec od _ _) as [_ | Hne]; [reflexivity | exfalso; apply Hne; reflexivity].
Qed.

Lemma nec_f_view_self : forall t s0, same_view S I step O obs od t s0 s0 = true.
Proof.
  intros t s0. unfold same_view.
  destruct (list_eq_dec od _ _) as [_ | Hne]; [reflexivity | exfalso; apply Hne; reflexivity].
Qed.

(** With at most two states, the view after any run picks out the same
    candidates as the first look. No price, no cost bound, no condition on
    the candidate list. *)
Theorem nec_f_two_states_never_teach :
  forall all : list S, finite_states all -> length all <= 2 ->
    forall Omega t s0,
      knowledge step obs od Omega t s0 = knowledge step obs od Omega [] s0.
Proof.
  intros all [Hnd Hall] Hlen Omega t s0. unfold knowledge.
  apply filter_ext. intro s.
  destruct (eq_dec s s0) as [-> | Hne]; [rewrite !nec_f_view_self; reflexivity |].
  destruct (od (obs s) (obs s0)) as [Eo | Ho].
  - assert (Hcover : forall x, x = s0 \/ x = s).
    { intro x. destruct (eq_dec x s0) as [-> | H0]; [left; reflexivity |].
      destruct (eq_dec x s) as [-> | H1]; [right; reflexivity |].
      exfalso.
      assert (Hthree : NoDup [s0; s; x]).
      { constructor; [simpl; intros [H | [H | []]]; congruence |].
        constructor; [simpl; intros [H | []]; congruence |].
        constructor; [intros [] | constructor]. }
      pose proof (NoDup_incl_length Hthree (fun y _ => Hall y)). simpl in *. lia. }
    assert (Hc : forall x, obs x = obs s0).
    { intro x. destruct (Hcover x) as [-> | ->]; [reflexivity | exact Eo]. }
    rewrite !nec_f_view_constant by exact Hc. reflexivity.
  - rewrite !nec_f_view_first_differs by exact Ho. reflexivity.
Qed.

End TwoNeverTeach.

Print Assumptions nec_f_bit_price_iff_halving.
Print Assumptions nec_f_run_narrowing_bit.
Print Assumptions nec_f_machine_narrowing_iff_halving.
Print Assumptions nec_f_narrowing_needs_nodup.
Print Assumptions nec_f_narrowing_equality.
Print Assumptions nec_f_wipe_under_merge_pricing.
Print Assumptions nec_f_wipe_one_attained.
Print Assumptions nec_f_two_state_observer_free.
Print Assumptions nec_f_one_state_observer_priced.
Print Assumptions nec_f_two_states_never_teach.
