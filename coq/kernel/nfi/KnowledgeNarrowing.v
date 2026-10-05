(** KnowledgeNarrowing: which narrowing a merge-priced machine pays for.

    The structural-entitlement bound in [HonestNoFI_TheoremsWithoutAssumptions]
    is handed a decision tree and a proof that the trace paid for its depth.
    This file asks the question without handing anything over. Take a finite
    deterministic machine priced the way [PermanentRecordPricing] prices it:
    an instruction with cost [c] squeezes a set of states by at most [2^c].
    Does narrowing a set of possibilities cost at least the drop in its
    rounded logarithm?

    It depends on whose possibilities.

    - The machine's own spread. Start the machine in any state of a set
      [Omega] and run a fixed trace. The states it can be in afterwards form
      the image of [Omega] under the run. That image can shrink, and the run
      pays for every halving: [log2_up |Omega| <= cost + log2_up |image|].
      The witness is the run itself. No tree, payment proof, or
      representative map is supplied ([run_narrowing_priced_log]).

    - An observer's knowledge. An observer who watches a window of the state
      along the run knows the initial states consistent with what it saw.
      That set can shrink without a forced charge. A machine that copies a
      hidden bit into a blank display by exclusive-or never merges two states.
      The file exhibits one compression-priced cost that assigns this step
      zero, yet the observer goes from two candidates to one
      ([observer_narrowing_can_be_free]). The machine's own spread does not
      shrink at all: both starting states are still possible states of the
      machine, with different displays.

    That is Bennett's resolution of Maxwell's demon, stated on the logic.
    Measuring can be done without merging. What costs is making room again:
    wiping the display merges states, and every merge-priced cost charges the
    wipe at least one ([wipe_costs_at_least_one]). So learning need not carry
    a positive charge, while a record the machine cannot take back cannot be
    written for free under the stated premises.
    [PermanentCertification] is the second half of that sentence for
    certificates.

    Scope. The price is the counting premise [compression_priced], which
    stands for Landauer's principle. It is a named premise, not a theorem
    about heat. The observer counterexample shows that compression pricing
    alone does not force a charge for every observer narrowing. Because it is
    a lower-bound condition, another admissible cost may overcharge the same
    injective step. The result makes no device-level claim. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import PermanentCertification.
From Kernel Require Import PermanentRecordPricing.
From Kernel Require Import FiniteCertMachine.

(** * Runs of a machine *)

Section Runs.

Variables (S I : Type).
Variable step : S -> I -> S.
Variable cost : I -> nat.
Variable eq_dec : forall a b : S, {a = b} + {a <> b}.

Fixpoint run (s : S) (t : list I) : S :=
  match t with
  | [] => s
  | i :: t' => run (step s i) t'
  end.

Fixpoint trace_cost (t : list I) : nat :=
  match t with
  | [] => 0
  | i :: t' => cost i + trace_cost t'
  end.

(** The states the machine can be in after [t], started anywhere in [D]. *)
Definition run_image (t : list I) (D : list S) : list S :=
  nodup eq_dec (map (fun s => run s t) D).

Lemma run_image_nodup : forall t D, NoDup (run_image t D).
Proof. intros. apply NoDup_nodup. Qed.

Lemma run_image_spec :
  forall t D y, In y (run_image t D) <-> exists s, In s D /\ run s t = y.
Proof.
  intros t D y. unfold run_image. rewrite nodup_In, in_map_iff.
  split; intros [s [H1 H2]]; exists s; split; assumption.
Qed.

Lemma run_image_step :
  forall i t D,
    length (run_image t (nodup eq_dec (map (fun s => step s i) D)))
    = length (run_image (i :: t) D).
Proof.
  intros i t D.
  apply Nat.le_antisymm; apply NoDup_incl_length; try apply run_image_nodup;
    intros y Hy; apply run_image_spec in Hy as [x [Hx Hr]]; apply run_image_spec.
  - apply nodup_In, in_map_iff in Hx as [s [<- Hs]].
    exists s. split; [exact Hs | exact Hr].
  - exists (step x i). split; [| exact Hr].
    apply nodup_In, in_map_iff. exists x. split; [reflexivity | exact Hx].
Qed.

(** The machine's own spread: every halving along a run is paid for. *)
Theorem run_narrowing_priced :
  compression_priced step cost eq_dec ->
  forall t D, NoDup D -> length D <= 2 ^ trace_cost t * length (run_image t D).
Proof.
  intros Hprice t. induction t as [| i t IH]; intros D HD.
  - simpl. unfold run_image. simpl. rewrite map_id, nodup_fixed_point by exact HD.
    lia.
  - set (D1 := nodup eq_dec (map (fun s => step s i) D)).
    pose proof (Hprice i D HD) as H1. unfold image_size in H1. fold D1 in H1.
    pose proof (IH D1 (NoDup_nodup _ _)) as H2.
    unfold D1 in H2. rewrite (run_image_step i t D) in H2.
    simpl trace_cost. rewrite Nat.pow_add_r, <- Nat.mul_assoc.
    apply Nat.le_trans with (m := 2 ^ cost i * length D1); [exact H1 |].
    apply Nat.mul_le_mono_l. exact H2.
Qed.

(** The same bound in rounded logarithms. *)
Theorem run_narrowing_priced_log :
  compression_priced step cost eq_dec ->
  forall t D,
    NoDup D ->
    Nat.log2_up (length D) <= trace_cost t + Nat.log2_up (length (run_image t D)).
Proof.
  intros Hprice t D HD.
  pose proof (run_narrowing_priced Hprice t D HD) as Hb.
  destruct (length (run_image t D)) as [| m] eqn:Hm.
  - rewrite Nat.mul_0_r in Hb. assert (length D = 0) as -> by lia. simpl. lia.
  - rewrite <- Nat.log2_up_mul_pow2 by lia.
    apply Nat.log2_up_le_mono. rewrite Nat.mul_comm. exact Hb.
Qed.

(** * An observer's knowledge *)

Variables (O : Type).
Variable obs : S -> O.
Variable obs_eq_dec : forall a b : O, {a = b} + {a <> b}.

(** Every state a run passes through, starting state included. *)
Fixpoint states_along (s : S) (t : list I) : list S :=
  match t with
  | [] => [s]
  | i :: t' => s :: states_along (step s i) t'
  end.

(** What the observer sees: the window at every state along the run. *)
Definition seen (s : S) (t : list I) : list O := map obs (states_along s t).

Definition same_view (t : list I) (s0 s : S) : bool :=
  if list_eq_dec obs_eq_dec (seen s t) (seen s0 t) then true else false.

(** The initial states in [Omega] consistent with what the observer saw
    when the machine really started at [s0]. *)
Definition knowledge (Omega : list S) (t : list I) (s0 : S) : list S :=
  filter (same_view t s0) Omega.

Lemma knowledge_contains_actual :
  forall Omega t s0, In s0 Omega -> In s0 (knowledge Omega t s0).
Proof.
  intros Omega t s0 H. unfold knowledge. apply filter_In. split; [exact H |].
  unfold same_view. destruct (list_eq_dec obs_eq_dec (seen s0 t) (seen s0 t));
    [reflexivity | contradiction].
Qed.

Lemma knowledge_sublist :
  forall Omega t s0, length (knowledge Omega t s0) <= length Omega.
Proof. intros. unfold knowledge. apply filter_length_le. Qed.

(** The target claim, read as a claim about observers: the drop in the
    rounded logarithm of what the observer considers possible is paid for
    by the trace. *)
Definition observer_narrowing_priced : Prop :=
  forall Omega t s0,
    NoDup Omega -> In s0 Omega ->
    Nat.log2_up (length Omega) - Nat.log2_up (length (knowledge Omega t s0))
      <= trace_cost t.

End Runs.

Arguments run {S I} step s t.
Arguments trace_cost {I} cost t.
Arguments run_image {S I} step eq_dec t D.
Arguments knowledge {S I} step {O} obs obs_eq_dec Omega t s0.
Arguments observer_narrowing_priced {S I} step cost {O} obs obs_eq_dec.

(** * Bennett's demon *)

(** A hidden bit and a display. [Measure] adds the bit into the display by
    exclusive-or; [Wipe] blanks the display. *)
Inductive DemonInstr : Type := Measure | Wipe.

Definition DState : Type := (bool * bool)%type.

Definition dstate_eq_dec : forall a b : DState, {a = b} + {a <> b}.
Proof. decide equality; apply Bool.bool_dec. Defined.

Definition dstep (s : DState) (i : DemonInstr) : DState :=
  let '(x, d) := s in
  match i with
  | Measure => (x, xorb d x)
  | Wipe => (x, false)
  end.

Definition dcost (i : DemonInstr) : nat :=
  match i with Measure => 0 | Wipe => 1 end.

Definition display (s : DState) : bool := snd s.

Definition all_dstates : list DState :=
  [(false, false); (false, true); (true, false); (true, true)].

Lemma dstates_finite : finite_states all_dstates.
Proof.
  split.
  - repeat constructor; simpl; intuition discriminate.
  - intros [[|] [|]]; simpl; tauto.
Qed.

Theorem measure_forgets_nothing : step_injective dstep Measure.
Proof.
  intros [x d] [y e] H. simpl in H. inversion H; subst.
  destruct y, d, e; simpl in *; congruence.
Qed.

Theorem wipe_merges : ~ step_injective dstep Wipe.
Proof.
  intro Hinj. specialize (Hinj (false, false) (false, true) eq_refl). discriminate.
Qed.

Lemma demon_fiber_bound :
  forall i (D : list DState),
    NoDup D ->
    forall y, length (filter (hits DState DState dstate_eq_dec (fun x => dstep x i) y) D)
              <= 2 ^ dcost i.
Proof.
  intros i D HD y.
  apply Nat.le_trans
    with (m := length (filter (hits DState DState dstate_eq_dec (fun x => dstep x i) y)
                              all_dstates)).
  - apply NoDup_incl_length; [apply NoDup_filter; exact HD |].
    intros x Hx. apply filter_In in Hx as [_ Hhit].
    apply filter_In. split; [apply (proj2 dstates_finite) | exact Hhit].
  - destruct i; destruct y as [[|] [|]]; vm_compute; lia.
Qed.

(** The demon's prices pay for every squeeze. *)
Theorem demon_compression_priced : compression_priced dstep dcost dstate_eq_dec.
Proof.
  intros i D HD. unfold image_size.
  apply fiber_bound_compression; [exact HD |].
  intro y. apply demon_fiber_bound. exact HD.
Qed.

(** Any price that pays for every squeeze charges the wipe. *)
Theorem wipe_costs_at_least_one :
  forall cost : DemonInstr -> nat,
    compression_priced dstep cost dstate_eq_dec -> cost Wipe >= 1.
Proof.
  intros cost Hprice.
  pose proof (Hprice Wipe [(false, false); (false, true)]) as H.
  assert (Hnd : NoDup [(false, false); (false, true)])
    by (repeat constructor; simpl; intuition discriminate).
  specialize (H Hnd). unfold image_size in H. vm_compute in H.
  destruct (cost Wipe) as [| c]; [simpl in H; lia | lia].
Qed.

(** The prior: the bit is unknown and the display is blank. *)
Definition demon_prior : list DState := [(false, false); (true, false)].

Theorem demon_observer_learns :
  length (knowledge dstep display Bool.bool_dec demon_prior [Measure] (true, false)) = 1 /\
  length demon_prior = 2 /\
  trace_cost dcost [Measure] = 0.
Proof. vm_compute. repeat split. Qed.

(** The machine's own spread does not shrink: both starting states remain
    possible states of the machine. *)
Theorem demon_machine_spread_kept :
  length (run_image dstep dstate_eq_dec [Measure] demon_prior) = 2.
Proof. vm_compute. reflexivity. Qed.

(** This particular price pays for every machine-state squeeze but assigns
    zero to a step that narrows the observer's knowledge. *)
Theorem observer_narrowing_can_be_free :
  compression_priced dstep dcost dstate_eq_dec /\
  ~ observer_narrowing_priced dstep dcost display Bool.bool_dec.
Proof.
  split; [exact demon_compression_priced |].
  intro H.
  specialize (H demon_prior [Measure] (true, false)).
  assert (Hnd : NoDup demon_prior)
    by (repeat constructor; simpl; intuition discriminate).
  assert (Hin : In (true, false) demon_prior) by (simpl; tauto).
  specialize (H Hnd Hin). vm_compute in H. lia.
Qed.
