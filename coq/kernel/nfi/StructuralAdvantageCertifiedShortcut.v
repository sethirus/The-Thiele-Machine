(** StructuralAdvantageCertifiedShortcut: factorized search with a real bridge.

    The EMIT-only witness in StructuralAdvantageObservedShortcut.v is the honest
    observation-level boundary: it certifies posterior admissibility but does
    not end with [has_supra_cert].

    This file adds the smallest concrete suffix that really fires the stronger
    certification channel. The factorized search is unchanged; after it lands at
    PC 20, the trace allocates one module, creates its identity morphism, and
    successfully asserts that morphism. That supplies a concrete
    [MORPH_ASSERT]-based bridge into the full structure-addition theorem.
    *)

From Coq Require Import List Arith.PeanoNat Lia Bool String.
Import ListNotations.
Open Scope string_scope.

From Kernel Require Import VMState VMStep.
From Kernel Require Import MuInitiality.
From Kernel Require Import RevelationRequirement.
From Kernel Require Import SimulationProof.
From Kernel Require Import NoFreeInsight InformationGainToStrengthening MuShannonBridge.
From Kernel Require Import HonestNoFI_TheoremsWithoutAssumptions.
From Kernel Require Import StructuralAdvantageObservedShortcut.

Import RevelationProof.

Definition sighted_n1_supra_trace : list vm_instruction :=
  sighted_n1_trace ++ [
    instr_pnew [0] 0;
    instr_morph_id 0 0 0;
    instr_morph_assert 1 "factorized" "cert" 0
  ].

Definition sighted_n1_supra_final : VMState :=
  run_vm 33 sighted_n1_supra_trace init_state.

Definition sighted_n1_supra_obs_fn (s : VMState) : list vm_instruction :=
  if Nat.eqb s.(vm_mu) 19 then sighted_n1_supra_trace else [].

Definition sighted_n1_supra_repr_obs_fn (s : VMState) : list vm_instruction :=
  if Nat.eqb s.(vm_mu) s.(vm_mu) then [] else [instr_halt 0].

Definition sighted_n1_supra_prior : list VMState :=
  [init_state; sighted_n1_supra_final].

Definition sighted_n1_supra_posterior : list VMState :=
  [sighted_n1_supra_final].

Lemma sighted_n1_supra_final_mu : sighted_n1_supra_final.(vm_mu) = 19.
Proof.
  unfold sighted_n1_supra_final, sighted_n1_supra_trace.
  vm_compute. reflexivity.
Qed.

Lemma sighted_n1_supra_final_err_false :
  sighted_n1_supra_final.(vm_err) = false.
Proof.
  unfold sighted_n1_supra_final, sighted_n1_supra_trace.
  vm_compute. reflexivity.
Qed.

Lemma sighted_n1_supra_final_has_supra_cert :
  has_supra_cert sighted_n1_supra_final.
Proof.
  unfold has_supra_cert, sighted_n1_supra_final, sighted_n1_supra_trace.
  vm_compute.
  discriminate.
Qed.

Lemma sighted_n1_supra_final_neq_init :
  sighted_n1_supra_final <> init_state.
Proof.
  intro Heq.
  assert (sighted_n1_supra_final.(vm_mu) = init_state.(vm_mu)) by now rewrite Heq.
  rewrite sighted_n1_supra_final_mu in H.
  simpl in H.
  discriminate.
Qed.

Lemma sighted_n1_supra_obs_init :
  sighted_n1_supra_obs_fn init_state = [].
Proof. reflexivity. Qed.

Lemma sighted_n1_supra_obs_final :
  sighted_n1_supra_obs_fn sighted_n1_supra_final = sighted_n1_supra_trace.
Proof.
  unfold sighted_n1_supra_obs_fn.
  rewrite sighted_n1_supra_final_mu.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma sighted_n1_supra_obs_run_vm :
  sighted_n1_supra_obs_fn (run_vm 33 sighted_n1_supra_trace init_state) =
  sighted_n1_supra_trace.
Proof.
  unfold sighted_n1_supra_obs_fn, sighted_n1_supra_trace.
  vm_compute. reflexivity.
Qed.

Lemma sighted_n1_supra_certified_obs :
  NoFreeInsight.CertifiedObs
    sighted_n1_supra_final
    (fun receipts => receipts)
    (InformationGainToStrengthening.omega_predicate
      receipt_list_eqb sighted_n1_supra_posterior sighted_n1_supra_obs_fn)
    sighted_n1_supra_trace.
Proof.
  unfold NoFreeInsight.CertifiedObs.
  split.
  - exact sighted_n1_supra_final_err_false.
  - unfold InformationGainToStrengthening.omega_predicate.
    eapply (InformationGainToStrengthening.existsb_In_true
              receipt_list_eqb receipt_list_eqb_spec).
    + simpl. auto.
    + exact sighted_n1_supra_obs_final.
Qed.

Lemma sighted_n1_supra_certified_obs_run_vm :
  NoFreeInsight.CertifiedObs
    (run_vm 33 sighted_n1_supra_trace init_state)
    (fun receipts => receipts)
    (InformationGainToStrengthening.omega_predicate
      receipt_list_eqb sighted_n1_supra_posterior sighted_n1_supra_obs_fn)
    sighted_n1_supra_trace.
Proof.
  unfold NoFreeInsight.CertifiedObs.
  split.
  - unfold sighted_n1_supra_trace.
    vm_compute. reflexivity.
  - unfold InformationGainToStrengthening.omega_predicate.
    eapply (InformationGainToStrengthening.existsb_In_true
              receipt_list_eqb receipt_list_eqb_spec).
    + simpl. auto.
    + exact sighted_n1_supra_obs_run_vm.
Qed.

Lemma sighted_n1_supra_strict_subset :
  InformationGainToStrengthening.is_strict_subset
    sighted_n1_supra_posterior sighted_n1_supra_prior.
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
      apply sighted_n1_supra_final_neq_init.
      exact Heq.
Qed.

Lemma sighted_n1_supra_distinguishing_witness :
  exists s_witness,
    In s_witness sighted_n1_supra_prior /\
    ~ In s_witness sighted_n1_supra_posterior /\
    InformationGainToStrengthening.observation_distinguishes
      sighted_n1_supra_obs_fn s_witness sighted_n1_supra_posterior.
Proof.
  exists init_state.
  split.
  - simpl. auto.
  - split.
    + simpl. intro Hin.
      destruct Hin as [Heq | []].
      apply sighted_n1_supra_final_neq_init.
      exact Heq.
    + intros s' Hin'.
      simpl in Hin'.
      destruct Hin' as [<- | []].
      rewrite sighted_n1_supra_obs_init.
      rewrite sighted_n1_supra_obs_final.
      discriminate.
Qed.

Lemma sighted_n1_supra_certified :
  NoFreeInsight.Certified
    sighted_n1_supra_final
    (fun receipts => receipts)
    (InformationGainToStrengthening.omega_predicate
      receipt_list_eqb sighted_n1_supra_posterior sighted_n1_supra_obs_fn)
    sighted_n1_supra_trace.
Proof.
  unfold NoFreeInsight.Certified.
  unfold NoFreeInsight.CertifiedWithSupra.
  split.
  - exact sighted_n1_supra_certified_obs.
  - exact sighted_n1_supra_final_has_supra_cert.
Qed.

Lemma sighted_n1_supra_has_supra_cert_run_vm :
  has_supra_cert (run_vm 33 sighted_n1_supra_trace init_state).
Proof.
  unfold has_supra_cert, sighted_n1_supra_trace.
  vm_compute.
  discriminate.
Qed.

Lemma sighted_n1_supra_certified_run_vm :
  NoFreeInsight.Certified
    (run_vm 33 sighted_n1_supra_trace init_state)
    (fun receipts => receipts)
    (InformationGainToStrengthening.omega_predicate
      receipt_list_eqb sighted_n1_supra_posterior sighted_n1_supra_obs_fn)
    sighted_n1_supra_trace.
Proof.
  unfold NoFreeInsight.Certified.
  unfold NoFreeInsight.CertifiedWithSupra.
  split.
  - exact sighted_n1_supra_certified_obs_run_vm.
  - exact sighted_n1_supra_has_supra_cert_run_vm.
Qed.

Lemma sighted_n1_supra_tree_realized :
  MuShannonBridge.decision_tree_realized_by_trace
    33 sighted_n1_supra_trace init_state sighted_n1_tree.
Proof.
  unfold MuShannonBridge.decision_tree_realized_by_trace.
  unfold sighted_n1_supra_trace, sighted_n1_tree.
  vm_compute.
  lia.
Qed.

Lemma sighted_n1_supra_posterior_nonempty :
  MuShannonBridge.feasible_size sighted_n1_supra_posterior > 0.
Proof. simpl. lia. Qed.

Lemma sighted_n1_supra_representatives :
  MuShannonBridge.PosteriorRepresentativeReduction
    sighted_n1_supra_repr_obs_fn
    sighted_n1_tree
    sighted_n1_supra_prior
    sighted_n1_supra_posterior.
Proof.
  unfold MuShannonBridge.PosteriorRepresentativeReduction.
  unfold sighted_n1_supra_prior, sighted_n1_supra_posterior.
  unfold sighted_n1_supra_repr_obs_fn, sighted_n1_tree.
  exists (fun _ => [init_state; sighted_n1_supra_final]).
  split.
  - intros s_prior Hin_prior.
    exists sighted_n1_supra_final.
    split.
    + simpl. auto.
    + split.
      * exact Hin_prior.
      * unfold MuShannonBridge.observation_equiv.
        rewrite Nat.eqb_refl.
        rewrite Nat.eqb_refl.
        reflexivity.
  - split.
    + simpl. lia.
    + intros s_post Hin_post.
      simpl in Hin_post.
      destruct Hin_post as [<- | []].
      simpl. lia.
Qed.

Theorem sighted_n1_factorized_search_lands_in_full_structure_addition :
  let P_prior :=
    InformationGainToStrengthening.omega_predicate
      receipt_list_eqb sighted_n1_supra_prior sighted_n1_supra_obs_fn in
  let P_posterior :=
    InformationGainToStrengthening.omega_predicate
      receipt_list_eqb sighted_n1_supra_posterior sighted_n1_supra_obs_fn in
  NoFreeInsight.strictly_stronger P_posterior P_prior /\
  NoFreeInsight.has_structure_addition 33 sighted_n1_supra_trace init_state /\
  Nat.log2_up (MuShannonBridge.feasible_size sighted_n1_supra_prior) -
    Nat.log2_up (MuShannonBridge.feasible_size sighted_n1_supra_posterior) <=
    sighted_n1_supra_final.(vm_mu) - init_state.(vm_mu).
Proof.
  eapply structural_entitlement_representation with
      (decoder := fun receipts => receipts)
      (obs_fn := sighted_n1_supra_obs_fn)
      (repr_obs_fn := sighted_n1_supra_repr_obs_fn)
      (obs_eqb := receipt_list_eqb)
      (omega_prior := sighted_n1_supra_prior)
      (omega_posterior := sighted_n1_supra_posterior)
      (tree := sighted_n1_tree).
  - exact receipt_list_eqb_spec.
  - exact sighted_n1_supra_strict_subset.
  - exact sighted_n1_supra_distinguishing_witness.
  - reflexivity.
  - exact sighted_n1_supra_certified_run_vm.
  - exact sighted_n1_supra_tree_realized.
  - exact sighted_n1_supra_posterior_nonempty.
  - exact sighted_n1_supra_representatives.
Qed.