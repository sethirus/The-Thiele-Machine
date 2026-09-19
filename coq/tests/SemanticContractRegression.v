(** Inhabited execution contracts and correlator boundary cases. *)
From Coq Require Import List Reals Lra Psatz.
From Kernel Require Import VMState VMStep SimulationProof MuInitiality
  ThreeLayerIsomorphism VerilogRTLCorrespondence TsirelsonFromMu
  TsirelsonFromIC NPAMomentMatrix ConstructivePSD MuLedgerQuantumBridge
  QuantumPartitionPSD ElliptopeCompletion.
Import ListNotations.

Definition vm_contract_instance : FullWireSpec :=
  @verilog_full_wire_spec VMState vm_apply
    vm_graph vm_csrs vm_regs vm_mem vm_pc vm_mu vm_mu_tensor vm_err
    vm_logic_acc vm_mstatus vm_witness vm_certified
    (fws_step_correct coq_full_wire_spec).

Example contract_certification_and_witness_trace :
  let s := run_fws vm_contract_instance
    [instr_chsh_trial 0 0 0 0 0; instr_certify 0] init_state in
  fws_certified vm_contract_instance s = true /\
  wc_same_00 (fws_witness vm_contract_instance s) = 1%nat /\
  fws_mu vm_contract_instance s = 1%nat.
Proof. repeat split; reflexivity. Qed.

Local Open Scope R_scope.

Example rotated_tests_allow_unit_vector_expansion :
  let b := {| cb_E00 := 1; cb_E01 := 0; cb_E10 := 1; cb_E11 := 0 |} in
  rotated_correlator_bounds b /\ cb_E00 b ^ 2 + cb_E10 b ^ 2 > 1.
Proof. unfold rotated_correlator_bounds; simpl; repeat split; lra. Qed.

Example classical_all_ones_satisfies_ic :
  ic_quadratic_bound
    {| cb_E00 := 1; cb_E01 := 1; cb_E10 := 1; cb_E11 := 1 |}.
Proof. unfold ic_quadratic_bound; simpl; lra. Qed.

Example all_ones_outside_fixed_slice :
  ~ quantum_realizable (zero_marginal_npa 1 1 1 1).
Proof.
  intros [_ Hpsd].
  pose proof (npa_psd_implies_column_contractive 1 1 1 1 Hpsd) as H.
  unfold zero_marginal_column_contractive in H.
  destruct H as [H _]. nra.
Qed.

Lemma all_ones_in_full_completion : elliptope_realizable 1 1 1 1.
Proof.
  pose proof (deterministic_strategy_elliptope 1 1 1 1) as H.
  assert (Hone : 1 * 1 = 1) by ring.
  specialize (H Hone Hone Hone Hone). rewrite Hone in H. exact H.
Qed.

Print Assumptions contract_certification_and_witness_trace.
Print Assumptions all_ones_in_full_completion.
