(** StructuralAdvantageObservedShortcutResult: opaque corollary boundary.

    This file exists only to keep the final specialization of the observed
    shortcut theorem outside the concrete witness module. The witness and the
    generic theorem are both opaque by the time this file imports them, so the
    specialization should be cheaper than rebuilding the proof term in the same
    source file.
    *)

From Coq Require Import List Arith.PeanoNat Bool.

From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import MuInitiality.
From Kernel Require Import RevelationRequirement.
From Kernel Require Import SimulationProof.
From Kernel Require Import NoFreeInsight InformationGainToStrengthening MuShannonBridge.
From Kernel Require Import HonestNoFI_TheoremsWithoutAssumptions.
From Kernel Require Import StructuralAdvantage.
From Kernel Require Import StructuralAdvantageObservedShortcut.

Import RevelationProof.

Definition sighted_n1_decoder : NoFreeInsight.receipt_decoder vm_instruction :=
  fun receipts => receipts.

Definition sighted_n1_prior_predicate :
  NoFreeInsight.ReceiptPredicate vm_instruction :=
  InformationGainToStrengthening.omega_predicate
    receipt_list_eqb sighted_n1_prior sighted_n1_predicate_obs_fn.

Definition sighted_n1_posterior_predicate :
  NoFreeInsight.ReceiptPredicate vm_instruction :=
  InformationGainToStrengthening.omega_predicate
    receipt_list_eqb sighted_n1_posterior sighted_n1_predicate_obs_fn.

Lemma sighted_n1_prior_accepts_decoded_trace :
  sighted_n1_prior_predicate (sighted_n1_decoder sighted_n1_trace) = true.
Proof.
  unfold sighted_n1_prior_predicate, sighted_n1_decoder.
  unfold InformationGainToStrengthening.omega_predicate.
  eapply (InformationGainToStrengthening.existsb_In_true
            receipt_list_eqb receipt_list_eqb_spec).
  - simpl. auto.
  - exact sighted_n1_predicate_obs_final.
Qed.

Lemma sighted_n1_trace_has_no_supra_bridge :
  Forall non_morph_assert_instr sighted_n1_trace.
Proof.
  unfold sighted_n1_trace, sighted_program.
  repeat constructor.
Qed.

Lemma sighted_n1_not_supra_cert :
  ~ has_supra_cert sighted_n1_final.
Proof.
  eapply NoFreeInsight.supra_bridge_free_trace_has_no_supra_cert.
  - apply NoFreeInsight.trace_run_run_vm.
  - reflexivity.
  - exact sighted_n1_trace_has_no_supra_bridge.
Qed.

Lemma sighted_n1_no_structure_addition :
  ~ NoFreeInsight.has_structure_addition 20 sighted_n1_trace init_state.
Proof.
  eapply non_morph_assert_trace_has_no_structure_addition.
  exact sighted_n1_trace_has_no_supra_bridge.
Qed.

Lemma sighted_n1_final_never_fully_certified :
  forall (A : Type) (decoder : NoFreeInsight.receipt_decoder A)
         (P : NoFreeInsight.ReceiptPredicate A) (receipts : NoFreeInsight.Receipts),
    ~ NoFreeInsight.Certified sighted_n1_final decoder P receipts.
Proof.
  intros A decoder P receipts Hcert.
  apply sighted_n1_not_supra_cert.
  exact (proj2 Hcert).
Qed.

Lemma sighted_n1_trace_never_fully_certified :
  forall (A : Type) (decoder : NoFreeInsight.receipt_decoder A)
         (P : NoFreeInsight.ReceiptPredicate A),
    ~ NoFreeInsight.Certified
        (run_vm 20 sighted_n1_trace init_state) decoder P sighted_n1_trace.
Proof.
  intros A decoder P.
  eapply NoFreeInsight.supra_bridge_free_trace_never_fully_certified.
  - apply NoFreeInsight.trace_run_run_vm.
  - reflexivity.
  - exact sighted_n1_trace_has_no_supra_bridge.
Qed.

Definition sighted_n1_bridge_hypothesis : Prop :=
  forall s_final,
    s_final = run_vm 20 sighted_n1_trace init_state ->
    sighted_n1_prior_predicate (sighted_n1_decoder sighted_n1_trace) = true ->
    NoFreeInsight.CertifiedObs
      s_final sighted_n1_decoder sighted_n1_posterior_predicate sighted_n1_trace ->
    has_supra_cert s_final.

Theorem sighted_n1_bridge_hypothesis_false :
  ~ sighted_n1_bridge_hypothesis.
Proof.
  intro Hbridge.
  apply sighted_n1_not_supra_cert.
  eapply Hbridge.
  - reflexivity.
  - exact sighted_n1_prior_accepts_decoded_trace.
  - exact sighted_n1_certified_obs.
Qed.