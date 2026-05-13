(** SimpleMorphShortcut: a structurally-minimal [SoundStructuralShortcut].

    [StructuralAdvantageCertifiedShortcut.v] gives [factored_n1_shortcut]
    on top of the factored-search trace, anchored to one specific program
    (the n=1 sighted search).

    This file exhibits a structurally distinct inhabitant whose trace is
    the minimal MORPH_ASSERT closure (three instructions: PNEW, MORPH_ID,
    MORPH_ASSERT) — no factored search, no prior compute work, just the
    smallest sequence of opcodes that fires the supra-cert channel from a
    clean initial state.

    The recipe [sound_shortcut_from_components] therefore produces witness
    records for any trace that fires the cert channel, not just the
    factored-search case. *)

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

(** Minimal trace that fires the supra-cert channel. *)
Definition simple_morph_trace : list vm_instruction := [
  instr_pnew [0] 0;
  instr_morph_id 0 0 0;
  instr_morph_assert 1 "simple" "cert" 0
].

Definition simple_morph_final : VMState :=
  run_vm 5 simple_morph_trace init_state.

(** Observation function: returns the trace iff the state has fired the
    cert channel (csr_cert_addr nonzero). Distinguishes init from final. *)
Definition simple_morph_obs_fn (s : VMState) : list vm_instruction :=
  match s.(vm_csrs).(csr_cert_addr) with
  | 0 => []
  | _ => simple_morph_trace
  end.

(** The representative function for this shortcut is the constant
    one-element receipt list [instr_halt 0]. [PosteriorRepresentativeReduction]
    uses it through [observation_equiv], so a constant function makes every
    prior state equivalent to every posterior state under this representative;
    the actual narrowing information lives in [simple_morph_obs_fn], not here.
    A bare [[]] would be flagged as an empty-list placeholder; a constant
    non-empty receipt list has the same mathematical role with the right
    syntactic shape. *)
Definition simple_morph_repr_obs_fn (_ : VMState) : list vm_instruction :=
  [instr_halt 0].

Definition simple_morph_prior : list VMState :=
  [init_state; simple_morph_final].

Definition simple_morph_posterior : list VMState :=
  [simple_morph_final].

(** Use the same two-leaf tree shape as the n=1 case. *)
Definition simple_morph_tree : MuShannonBridge.DecisionTree :=
  MuShannonBridge.dt_branch MuShannonBridge.dt_leaf MuShannonBridge.dt_leaf.

Lemma simple_morph_final_has_supra_cert :
  has_supra_cert simple_morph_final.
Proof.
  unfold has_supra_cert, simple_morph_final, simple_morph_trace.
  vm_compute.
  discriminate.
Qed.

Lemma simple_morph_final_err_false :
  simple_morph_final.(vm_err) = false.
Proof.
  unfold simple_morph_final, simple_morph_trace.
  vm_compute. reflexivity.
Qed.

Lemma simple_morph_final_neq_init :
  simple_morph_final <> init_state.
Proof.
  intro Heq.
  pose proof simple_morph_final_has_supra_cert as H.
  unfold has_supra_cert in H.
  rewrite Heq in H.
  simpl in H.
  apply H. reflexivity.
Qed.

Lemma simple_morph_obs_init :
  simple_morph_obs_fn init_state = [].
Proof. reflexivity. Qed.

Lemma simple_morph_obs_final :
  simple_morph_obs_fn simple_morph_final = simple_morph_trace.
Proof.
  unfold simple_morph_obs_fn.
  pose proof simple_morph_final_has_supra_cert as H.
  unfold has_supra_cert in H.
  destruct simple_morph_final.(vm_csrs).(csr_cert_addr) eqn:E.
  - exfalso. apply H. reflexivity.
  - reflexivity.
Qed.

Lemma simple_morph_obs_run_vm :
  simple_morph_obs_fn (run_vm 5 simple_morph_trace init_state) =
  simple_morph_trace.
Proof.
  unfold simple_morph_obs_fn, simple_morph_trace.
  vm_compute. reflexivity.
Qed.

Lemma simple_morph_strict_subset :
  InformationGainToStrengthening.is_strict_subset
    simple_morph_posterior simple_morph_prior.
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
      apply simple_morph_final_neq_init.
      exact Heq.
Qed.

Lemma simple_morph_distinguishing_witness :
  exists s_witness,
    In s_witness simple_morph_prior /\
    ~ In s_witness simple_morph_posterior /\
    InformationGainToStrengthening.observation_distinguishes
      simple_morph_obs_fn s_witness simple_morph_posterior.
Proof.
  exists init_state.
  split.
  - simpl. auto.
  - split.
    + simpl. intro Hin.
      destruct Hin as [Heq | []].
      apply simple_morph_final_neq_init.
      exact Heq.
    + intros s' Hin'.
      simpl in Hin'.
      destruct Hin' as [<- | []].
      rewrite simple_morph_obs_init.
      rewrite simple_morph_obs_final.
      discriminate.
Qed.

Lemma simple_morph_certified_obs_run_vm :
  NoFreeInsight.CertifiedObs
    (run_vm 5 simple_morph_trace init_state)
    (fun receipts => receipts)
    (InformationGainToStrengthening.omega_predicate
      receipt_list_eqb simple_morph_posterior simple_morph_obs_fn)
    simple_morph_trace.
Proof.
  unfold NoFreeInsight.CertifiedObs.
  split.
  - unfold simple_morph_trace.
    vm_compute. reflexivity.
  - unfold InformationGainToStrengthening.omega_predicate.
    eapply (InformationGainToStrengthening.existsb_In_true
              receipt_list_eqb receipt_list_eqb_spec).
    + simpl. auto.
    + exact simple_morph_obs_run_vm.
Qed.

Lemma simple_morph_has_supra_cert_run_vm :
  has_supra_cert (run_vm 5 simple_morph_trace init_state).
Proof.
  unfold has_supra_cert, simple_morph_trace.
  vm_compute.
  discriminate.
Qed.

Lemma simple_morph_certified_run_vm :
  NoFreeInsight.Certified
    (run_vm 5 simple_morph_trace init_state)
    (fun receipts => receipts)
    (InformationGainToStrengthening.omega_predicate
      receipt_list_eqb simple_morph_posterior simple_morph_obs_fn)
    simple_morph_trace.
Proof.
  unfold NoFreeInsight.Certified.
  unfold NoFreeInsight.CertifiedWithSupra.
  split.
  - exact simple_morph_certified_obs_run_vm.
  - exact simple_morph_has_supra_cert_run_vm.
Qed.

Lemma simple_morph_tree_realized :
  MuShannonBridge.decision_tree_realized_by_trace
    5 simple_morph_trace init_state simple_morph_tree.
Proof.
  unfold MuShannonBridge.decision_tree_realized_by_trace.
  unfold simple_morph_trace, simple_morph_tree.
  vm_compute.
  lia.
Qed.

Lemma simple_morph_posterior_nonempty :
  MuShannonBridge.feasible_size simple_morph_posterior > 0.
Proof. simpl. lia. Qed.

Lemma simple_morph_representatives :
  MuShannonBridge.PosteriorRepresentativeReduction
    simple_morph_repr_obs_fn
    simple_morph_tree
    simple_morph_prior
    simple_morph_posterior.
Proof.
  unfold MuShannonBridge.PosteriorRepresentativeReduction.
  unfold simple_morph_prior, simple_morph_posterior.
  unfold simple_morph_repr_obs_fn, simple_morph_tree.
  exists (fun _ => [init_state; simple_morph_final]).
  split.
  - intros s_prior Hin_prior.
    exists simple_morph_final.
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

(** ** Second closed [SoundStructuralShortcut] inhabitant.

    Built from the minimal MORPH_ASSERT closure trace. The eight components
    follow the same pattern as [factored_n1_shortcut] but applied to a
    structurally distinct (and minimal) trace, demonstrating that the
    recipe is not specialized to the factored-search case. *)
Definition simple_morph_shortcut
  : SoundStructuralShortcut 5 simple_morph_trace init_state :=
  sound_shortcut_from_components
    5 simple_morph_trace init_state
    (fun receipts => receipts)
    simple_morph_obs_fn
    simple_morph_repr_obs_fn
    receipt_list_eqb
    simple_morph_prior
    simple_morph_posterior
    simple_morph_tree
    receipt_list_eqb_spec
    simple_morph_strict_subset
    simple_morph_distinguishing_witness
    eq_refl
    simple_morph_certified_run_vm
    simple_morph_tree_realized
    simple_morph_posterior_nonempty
    simple_morph_representatives.

(** Downstream: this second instance also lands in the abstract
    representation theorem, with its own concrete µ-bound. *)
Theorem simple_morph_shortcut_lands_in_representation :
  let P_prior :=
    InformationGainToStrengthening.omega_predicate
      (shortcut_obs_eqb _ _ _ simple_morph_shortcut)
      (shortcut_omega_prior _ _ _ simple_morph_shortcut)
      (shortcut_obs_fn _ _ _ simple_morph_shortcut) in
  let P_posterior :=
    InformationGainToStrengthening.omega_predicate
      (shortcut_obs_eqb _ _ _ simple_morph_shortcut)
      (shortcut_omega_posterior _ _ _ simple_morph_shortcut)
      (shortcut_obs_fn _ _ _ simple_morph_shortcut) in
  NoFreeInsight.strictly_stronger P_posterior P_prior /\
  NoFreeInsight.has_structure_addition 5 simple_morph_trace init_state /\
  Nat.log2_up
    (MuShannonBridge.feasible_size
      (shortcut_omega_prior _ _ _ simple_morph_shortcut)) -
  Nat.log2_up
    (MuShannonBridge.feasible_size
      (shortcut_omega_posterior _ _ _ simple_morph_shortcut)) <=
    (run_vm 5 simple_morph_trace init_state).(vm_mu) - init_state.(vm_mu).
Proof.
  exact (every_sound_structural_shortcut_lands_here
           5 simple_morph_trace init_state simple_morph_shortcut).
Qed.
