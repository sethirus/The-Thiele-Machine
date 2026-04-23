(** StructuralAdvantageObservedShortcut: concrete factorization witness.

    This file does not claim the full open translation theorem. It closes a
    smaller bedrock step: the smallest factored-search witness already lands in
    the observed structural-shortcut theorem once the distinguishing predicate
    observation and the representative reduction observation are kept separate.
    *)

From Coq Require Import List Arith.PeanoNat Lia Bool.
Import ListNotations.

From Kernel Require Import VMState VMStep.
From Kernel Require Import MuInitiality.
From Kernel Require Import SimulationProof.
From Kernel Require Import RevelationRequirement.
From Kernel Require Import NoFreeInsight InformationGainToStrengthening MuShannonBridge.
From Kernel Require Import HonestNoFI_TheoremsWithoutAssumptions.
From Kernel Require Import StructuralAdvantage.

Definition receipt_list_eqb (o1 o2 : list vm_instruction) : bool :=
  if list_eq_dec vm_instruction_eq_dec o1 o2 then true else false.

Lemma receipt_list_eqb_spec :
  forall o1 o2, receipt_list_eqb o1 o2 = true <-> o1 = o2.
Proof.
  intros o1 o2.
  unfold receipt_list_eqb.
  destruct (list_eq_dec vm_instruction_eq_dec o1 o2) as [Heq|Hneq].
  - split.
    + intro Htrue. exact Heq.
    + intro Heq'. reflexivity.
  - split.
    + discriminate.
    + intro Heq'. subst o2. contradiction.
Qed.

Definition sighted_n1_trace : list vm_instruction := sighted_program 0 0.

Definition sighted_n1_final : VMState :=
  run_vm 20 sighted_n1_trace init_state.

Definition sighted_n1_predicate_obs_fn (s : VMState) : list vm_instruction :=
  if Nat.eqb s.(vm_mu) 18 then sighted_n1_trace else [].

(** The representative observation is deliberately silent here. The separating
    transcript lives in [sighted_n1_predicate_obs_fn]. *)
Definition sighted_n1_repr_obs_fn (_ : VMState) : list vm_instruction := nil.

Definition sighted_n1_prior : list VMState := [init_state; sighted_n1_final].

Definition sighted_n1_posterior : list VMState := [sighted_n1_final].

Definition sighted_n1_tree : MuShannonBridge.DecisionTree :=
  dt_branch dt_leaf dt_leaf.

Lemma sighted_n1_final_mu : sighted_n1_final.(vm_mu) = 18.
Proof.
  exact (proj1 (proj2 sighted_halts_in_two_n)).
Qed.

Lemma sighted_n1_final_err_false : sighted_n1_final.(vm_err) = false.
Proof.
  unfold sighted_n1_final, sighted_n1_trace.
  native_compute. reflexivity.
Qed.

Lemma sighted_n1_final_neq_init : sighted_n1_final <> init_state.
Proof.
  intro Heq.
  assert (sighted_n1_final.(vm_mu) = init_state.(vm_mu)) by now rewrite Heq.
  rewrite sighted_n1_final_mu in H.
  simpl in H.
  discriminate.
Qed.

Lemma sighted_n1_predicate_obs_init :
  sighted_n1_predicate_obs_fn init_state = [].
Proof. reflexivity. Qed.

Lemma sighted_n1_predicate_obs_final :
  sighted_n1_predicate_obs_fn sighted_n1_final = sighted_n1_trace.
Proof.
  unfold sighted_n1_predicate_obs_fn.
  rewrite sighted_n1_final_mu.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma sighted_n1_strict_subset :
  InformationGainToStrengthening.is_strict_subset
    sighted_n1_posterior sighted_n1_prior.
Proof.
  split.
  - intros s Hin.
    simpl in Hin.
    destruct Hin as [<- | []].
    simpl. auto.
  - exists init_state.
    split.
    + simpl. auto.
    + simpl. intro Hin.
      destruct Hin as [Heq | []].
      apply sighted_n1_final_neq_init.
      exact Heq.
Qed.

Lemma sighted_n1_distinguishing_witness :
  exists s_witness,
    In s_witness sighted_n1_prior /\
    ~ In s_witness sighted_n1_posterior /\
    InformationGainToStrengthening.observation_distinguishes
      sighted_n1_predicate_obs_fn s_witness sighted_n1_posterior.
Proof.
  exists init_state.
  split.
  - simpl. auto.
  - split.
    + simpl. intro Hin.
      destruct Hin as [Heq | []].
      apply sighted_n1_final_neq_init.
      exact Heq.
    + intros s' Hin'.
      simpl in Hin'.
      destruct Hin' as [<- | []].
      rewrite sighted_n1_predicate_obs_init.
      rewrite sighted_n1_predicate_obs_final.
      discriminate.
Qed.

Lemma sighted_n1_certified_obs :
  NoFreeInsight.CertifiedObs
    sighted_n1_final
    (fun receipts => receipts)
    (InformationGainToStrengthening.omega_predicate
      receipt_list_eqb sighted_n1_posterior sighted_n1_predicate_obs_fn)
    sighted_n1_trace.
Proof.
  unfold NoFreeInsight.CertifiedObs.
  split.
  - exact sighted_n1_final_err_false.
  - unfold InformationGainToStrengthening.omega_predicate.
    simpl.
    rewrite sighted_n1_predicate_obs_final.
    rewrite Bool.orb_false_r.
    apply receipt_list_eqb_spec.
    reflexivity.
Qed.

Lemma sighted_n1_tree_realized :
  MuShannonBridge.decision_tree_realized_by_trace
    20 sighted_n1_trace init_state sighted_n1_tree.
Proof.
  unfold MuShannonBridge.decision_tree_realized_by_trace.
  unfold sighted_n1_trace, sighted_n1_tree.
  vm_compute.
  lia.
Qed.

Lemma sighted_n1_posterior_nonempty :
  MuShannonBridge.feasible_size sighted_n1_posterior > 0.
Proof. simpl. lia. Qed.

Lemma sighted_n1_representatives :
  MuShannonBridge.PosteriorRepresentativeReduction
    sighted_n1_repr_obs_fn sighted_n1_tree sighted_n1_prior sighted_n1_posterior.
Proof.
  unfold MuShannonBridge.PosteriorRepresentativeReduction.
  unfold sighted_n1_prior, sighted_n1_posterior, sighted_n1_repr_obs_fn, sighted_n1_tree.
  exists (fun _ => [init_state; sighted_n1_final]).
  split.
  - intros s_prior Hin_prior.
    exists sighted_n1_final.
    split.
    + simpl. auto.
    + split.
      * exact Hin_prior.
      * unfold MuShannonBridge.observation_equiv.
        reflexivity.
  - split.
    + simpl. lia.
    + intros s_post Hin_post.
      simpl in Hin_post.
      destruct Hin_post as [<- | []].
      simpl. lia.
Qed.
