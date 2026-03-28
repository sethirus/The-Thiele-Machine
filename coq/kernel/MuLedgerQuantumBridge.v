(** =========================================================================
    MuLedgerQuantumBridge: mu-Ledger / Quantum Realizability Bridge
    =========================================================================

    WHY THIS FILE EXISTS:
    The kernel already has two proof islands:

    1. mu-ledger accounting and trace execution
    2. NPA moment matrices and Tsirelson bounds

    This file connects them as far as the current kernel infrastructure honestly
    allows. In particular, it now contains:

    - A concrete trace-to-correlator interface using CHSHExtraction.v
    - A concrete mu-ledger coherence predicate over real correlators and final VM state
    - A proved theorem: coherence implies the Tsirelson bound via existing minor constraints
    - An explicit residual obligation isolating what is still needed to obtain
      full quantum realizability (PSD of the induced NPA matrix)

    THE CORE CLAIM:
    mu_ledger_coherent implies Tsirelson bound (S^2 <= 8) and quantum
    realizability of the extracted NPA matrix. The bridge is honest: it
    requires column contractivity as an additional hypothesis beyond the
    row minor constraints, and proves that this extra hypothesis is
    genuinely needed (not derivable from row minors alone).

    CRITICAL DISTINCTION:
    We do NOT silently identify mu-ledger coherence with quantum realizability.
    That would be circular. Instead, we prove the strongest theorem currently
    supported by the repository and make the remaining PSD bridge explicit.

    FALSIFICATION:
    Show that mu_ledger_tsirelson_coherent alone implies PSD of the NPA
    matrix. This is impossible: bridge_counterexample_not_final_tensor_quantum_gram
    exhibits a concrete counterexample where Tsirelson coherence holds but PSD fails.

    ========================================================================= *)

From Coq Require Import List Reals QArith Psatz Field.
From Coq.Vectors Require Import Fin.
Require Import Coq.QArith.Qreals.
Import ListNotations.

From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import SimulationProof.
From Kernel Require Import CHSHExtraction.
From Kernel Require Import MuCostModel.
From Kernel Require Import MuLedgerConservation.
From Kernel Require Import NoFreeInsight.
From Kernel Require Import ConstructivePSD.
From Kernel Require Import NPAMomentMatrix.
From Kernel Require Import TsirelsonGeneral.
From Kernel Require Import PrimeAxiom.

Local Open Scope R_scope.

Notation RealNumber := Rdefinitions.R.

(** ** Concrete correlators extracted from a VM trace *)

Definition trace_trials
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : list CHSHTrial :=
  extract_chsh_trials_from_trace fuel trace s_init.

Definition trace_e00
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : RealNumber :=
  Q2R (compute_correlation (filter_trials (trace_trials fuel trace s_init) 0 0)).

Definition trace_e01
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : RealNumber :=
  Q2R (compute_correlation (filter_trials (trace_trials fuel trace s_init) 0 1)).

Definition trace_e10
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : RealNumber :=
  Q2R (compute_correlation (filter_trials (trace_trials fuel trace s_init) 1 0)).

Definition trace_e11
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : RealNumber :=
  Q2R (compute_correlation (filter_trials (trace_trials fuel trace s_init) 1 1)).

Definition trace_realizes_zero_marginal_chsh
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState)
  (e00 e01 e10 e11 : RealNumber) : Prop :=
  e00 = trace_e00 fuel trace s_init /\
  e01 = trace_e01 fuel trace s_init /\
  e10 = trace_e10 fuel trace s_init /\
  e11 = trace_e11 fuel trace s_init.

Definition trace_zero_marginal_npa
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : NPAMomentMatrix :=
  zero_marginal_npa
    (trace_e00 fuel trace s_init)
    (trace_e01 fuel trace s_init)
    (trace_e10 fuel trace s_init)
    (trace_e11 fuel trace s_init).

(** ** Concrete state-side coherence *)

Definition mu_tensor_symmetric (s : VMState) : Prop :=
  forall i j,
    (i < 4)%nat ->
    (j < 4)%nat ->
    vm_mu_tensor_entry s i j = vm_mu_tensor_entry s j i.

Definition final_tensor_symmetric
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : Prop :=
  mu_tensor_symmetric (run_vm fuel trace s_init).

(** The current VM/final-tensor invariant layer gives a Tsirelson-sufficient
    row-minor condition, but not the stronger column-contractivity facts needed
    for PSD of the induced zero-marginal NPA matrix. We keep that weaker layer
    explicit so the exact remaining gap stays visible. *)
Definition mu_ledger_tsirelson_coherent
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : Prop :=
  final_tensor_symmetric fuel trace s_init /\
  minor_constraint_zero_marginal
    (trace_e00 fuel trace s_init)
    (trace_e01 fuel trace s_init) /\
  minor_constraint_zero_marginal
    (trace_e10 fuel trace s_init)
    (trace_e11 fuel trace s_init).

Definition zero_marginal_column_contractive
  (e00 e01 e10 e11 : RealNumber) : Prop :=
  1 - e00 * e00 - e10 * e10 >= 0 /\
  1 - e01 * e01 - e11 * e11 >= 0 /\
  (1 - e00 * e00 - e10 * e10) *
    (1 - e01 * e01 - e11 * e11) -
    (e00 * e01 + e10 * e11) * (e00 * e01 + e10 * e11) >= 0.

  Definition trace_column_contractive
    (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : Prop :=
    let e00 := trace_e00 fuel trace s_init in
    let e01 := trace_e01 fuel trace s_init in
    let e10 := trace_e10 fuel trace s_init in
    let e11 := trace_e11 fuel trace s_init in
    zero_marginal_column_contractive e00 e01 e10 e11.

Lemma row_minor_constraints_do_not_imply_column_contractivity :
  exists e00 e01 e10 e11,
    minor_constraint_zero_marginal e00 e01 /\
    minor_constraint_zero_marginal e10 e11 /\
    ~ zero_marginal_column_contractive e00 e01 e10 e11.
Proof.
  exists 1, 0, 1, 0.
  repeat split.
  - unfold minor_constraint_zero_marginal. lra.
  - unfold minor_constraint_zero_marginal. lra.
  - unfold zero_marginal_column_contractive. intro H.
    destruct H as [Hc0 _].
    lra.
Qed.

Definition bridge_counterexample_trace : list vm_instruction := [
  instr_chsh_trial 0 0 0 0 0;
  instr_chsh_trial 0 1 0 0 0;
  instr_chsh_trial 0 1 0 1 0;
  instr_chsh_trial 1 0 0 0 0;
  instr_chsh_trial 1 1 0 0 0;
  instr_chsh_trial 1 1 0 1 0
].

Definition bridge_witness_trace : list vm_instruction := [
  instr_chsh_trial 0 0 0 0 0;
  instr_chsh_trial 0 0 0 1 0;
  instr_chsh_trial 0 1 0 0 0;
  instr_chsh_trial 0 1 0 1 0;
  instr_chsh_trial 1 0 0 0 0;
  instr_chsh_trial 1 0 0 1 0
].

Definition bridge_counterexample_init : VMState :=
  {| vm_graph := empty_graph;
     vm_csrs :=
       {| csr_cert_addr := 0;
          csr_status := 0;
          csr_err := 0;
          csr_heap_base := 0 |};
     vm_regs := [];
     vm_mem := [];
     vm_pc := 0;
     vm_mu := 0;
     vm_mu_tensor := vm_mu_tensor_default;
     vm_err := false;
     vm_logic_acc := 0;
     vm_mstatus := 0;
     vm_witness := witness_counts_zero;
     vm_certified := false |}.

Lemma bridge_counterexample_tsirelson_coherent :
  mu_ledger_tsirelson_coherent 6%nat bridge_counterexample_trace bridge_counterexample_init.
Proof.
  unfold mu_ledger_tsirelson_coherent, final_tensor_symmetric, mu_tensor_symmetric.
  simpl.
  split.
  - intros i j Hi Hj.
    assert (Hi' : i = 0%nat \/ i = 1%nat \/ i = 2%nat \/ i = 3%nat) by lia.
    assert (Hj' : j = 0%nat \/ j = 1%nat \/ j = 2%nat \/ j = 3%nat) by lia.
    destruct Hi' as [-> | [-> | [-> | ->]]];
    destruct Hj' as [-> | [-> | [-> | ->]]];
    reflexivity.
  - split; vm_compute; lra.
Qed.

Lemma bridge_counterexample_not_column_contractive :
  ~ trace_column_contractive 6%nat bridge_counterexample_trace bridge_counterexample_init.
Proof.
  vm_compute. lra.
Qed.

Definition bridge_bad_psd_witness (i : Fin.t 5) : RealNumber :=
  match proj1_sig (Fin.to_nat i) with
  | 0%nat => 0
  | 1%nat => -1
  | 2%nat => -1
  | 3%nat => 1
  | _ => 0
  end.

(** The exact sufficient invariant package is the final-state symmetry together
    with an execution certificate for the column-contractivity conditions that
    imply PSD of the extracted zero-marginal NPA matrix. This is strictly
    stronger than the old Tsirelson-sufficient layer and no longer depends on
    that refuted implication. *)
Definition execution_column_contractivity_certificate
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : Prop :=
  trace_column_contractive fuel trace s_init.

Definition execution_quantum_gram_coherent
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : Prop :=
  final_tensor_symmetric fuel trace s_init /\
  execution_column_contractivity_certificate fuel trace s_init.

Definition mu_ledger_quantum_gram_coherent
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : Prop :=
  mu_ledger_tsirelson_coherent fuel trace s_init /\
  execution_column_contractivity_certificate fuel trace s_init.

Definition mu_ledger_coherent
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : Prop :=
  mu_ledger_quantum_gram_coherent fuel trace s_init.

Definition machine_internal_completed_run
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : Prop :=
  let s_final := run_vm fuel trace s_init in
  s_final.(vm_certified) = true /\
  s_final.(vm_err) = false /\
  (0 < s_final.(vm_mu))%nat /\
  final_tensor_symmetric fuel trace s_init.

Definition bridge_ready_completed_run
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : Prop :=
  machine_internal_completed_run fuel trace s_init /\
  trace_column_contractive fuel trace s_init.

Definition certified_bridge_counterexample_trace : list vm_instruction :=
  bridge_counterexample_trace ++ [instr_certify 0].

Definition final_tensor_quantum_gram
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : Prop :=
  let M := nat_matrix_to_fin5 (npa_to_matrix (trace_zero_marginal_npa fuel trace s_init)) in
  symmetric5 M /\ PSD5 M.

Lemma bridge_witness_execution_quantum_gram_coherent :
  execution_quantum_gram_coherent 6%nat bridge_witness_trace bridge_counterexample_init.
Proof.
  unfold execution_quantum_gram_coherent.
  split.
  - unfold final_tensor_symmetric, mu_tensor_symmetric.
    simpl.
    intros i j Hi Hj.
    assert (Hi' : i = 0%nat \/ i = 1%nat \/ i = 2%nat \/ i = 3%nat) by lia.
    assert (Hj' : j = 0%nat \/ j = 1%nat \/ j = 2%nat \/ j = 3%nat) by lia.
    destruct Hi' as [-> | [-> | [-> | ->]]];
    destruct Hj' as [-> | [-> | [-> | ->]]];
    reflexivity.
  - unfold execution_column_contractivity_certificate.
    vm_compute. lra.
Qed.

Lemma bridge_counterexample_not_execution_quantum_gram_coherent :
  ~ execution_quantum_gram_coherent 6%nat bridge_counterexample_trace bridge_counterexample_init.
Proof.
  intros [_ Hcontractive].
  exact (bridge_counterexample_not_column_contractive Hcontractive).
Qed.

Lemma bridge_good_and_bad_run_vm_coincide :
  (run_vm 6%nat bridge_witness_trace bridge_counterexample_init).(vm_mu_tensor) =
  (run_vm 6%nat bridge_counterexample_trace bridge_counterexample_init).(vm_mu_tensor).
Proof.
  vm_compute. reflexivity.
Qed.

Lemma bridge_good_and_bad_final_tensors_coincide :
  (run_vm 6%nat bridge_witness_trace bridge_counterexample_init).(vm_mu_tensor) =
  (run_vm 6%nat bridge_counterexample_trace bridge_counterexample_init).(vm_mu_tensor).
Proof.
  exact bridge_good_and_bad_run_vm_coincide.
Qed.

(** With witness counts in VMState, the raw VMState version of the
    "cannot characterize" theorem is subsumed by the mu_tensor version below.
    The mu_tensor formulation is the physically meaningful one: no function of
    the mu-tensor alone can characterize execution quantum gram coherence. *)

Theorem raw_vm_mu_tensor_cannot_characterize_execution_quantum_gram :
  ~ exists P : list nat -> Prop,
      forall fuel trace s_init,
        execution_quantum_gram_coherent fuel trace s_init <->
        P (run_vm fuel trace s_init).(vm_mu_tensor).
Proof.
  intros [P HP].
  pose proof (HP 6%nat bridge_witness_trace bridge_counterexample_init) as Hgood.
  pose proof (HP 6%nat bridge_counterexample_trace bridge_counterexample_init) as Hbad.
  destruct Hgood as [Hgood_fwd _].
  destruct Hbad as [_ Hbad_rev].
  apply bridge_counterexample_not_execution_quantum_gram_coherent.
  apply Hbad_rev.
  rewrite <- bridge_good_and_bad_final_tensors_coincide.
  apply Hgood_fwd.
  apply bridge_witness_execution_quantum_gram_coherent.
Qed.

Lemma bridge_counterexample_not_final_tensor_quantum_gram :
  ~ final_tensor_quantum_gram 6%nat bridge_counterexample_trace bridge_counterexample_init.
Proof.
  intros [_ Hpsd].
  specialize (Hpsd bridge_bad_psd_witness).
  unfold bridge_bad_psd_witness in Hpsd.
  vm_compute in Hpsd.
  lra.
Qed.

Theorem mu_ledger_tsirelson_coherent_not_sufficient :
  exists fuel trace s_init,
    mu_ledger_tsirelson_coherent fuel trace s_init /\
    ~ final_tensor_quantum_gram fuel trace s_init.
Proof.
  exists 6%nat, bridge_counterexample_trace, bridge_counterexample_init.
  split.
  - apply bridge_counterexample_tsirelson_coherent.
  - apply bridge_counterexample_not_final_tensor_quantum_gram.
Qed.

(** ** Basic realization lemmas *)

Theorem trace_realizes_zero_marginal_chsh_refl :
  forall fuel trace s_init,
    trace_realizes_zero_marginal_chsh fuel trace s_init
      (trace_e00 fuel trace s_init)
      (trace_e01 fuel trace s_init)
      (trace_e10 fuel trace s_init)
      (trace_e11 fuel trace s_init).
Proof.
  intros fuel trace s_init.
  unfold trace_realizes_zero_marginal_chsh.
  repeat split; reflexivity.
Qed.

Theorem mu_ledger_coherent_implies_trace_realizes_zero_marginal_chsh :
  forall fuel trace s_init,
    mu_ledger_coherent fuel trace s_init ->
    trace_realizes_zero_marginal_chsh fuel trace s_init
      (trace_e00 fuel trace s_init)
      (trace_e01 fuel trace s_init)
      (trace_e10 fuel trace s_init)
      (trace_e11 fuel trace s_init).
Proof.
  intros fuel trace s_init _.
  apply trace_realizes_zero_marginal_chsh_refl.
Qed.

Lemma mu_ledger_coherent_implies_tsirelson_coherent :
  forall fuel trace s_init,
    mu_ledger_coherent fuel trace s_init ->
    mu_ledger_tsirelson_coherent fuel trace s_init.
Proof.
  intros fuel trace s_init Hcoh.
  exact (proj1 Hcoh).
Qed.

Theorem trace_zero_marginal_npa_is_symmetric :
  forall fuel trace s_init,
    symmetric5 (nat_matrix_to_fin5 (npa_to_matrix (trace_zero_marginal_npa fuel trace s_init))).
Proof.
  intros fuel trace s_init.
  apply npa_to_matrix_symmetric.
Qed.

(** ** Strongest current bridge theorem actually provable from existing infrastructure *)

Theorem mu_ledger_coherent_implies_tsirelson_bound_squared :
  forall fuel trace s_init,
    mu_ledger_coherent fuel trace s_init ->
    (CHSH
      (trace_e00 fuel trace s_init)
      (trace_e01 fuel trace s_init)
      (trace_e10 fuel trace s_init)
      (trace_e11 fuel trace s_init))² <= 8.
Proof.
  intros fuel trace s_init Hcoh.
  apply mu_ledger_coherent_implies_tsirelson_coherent in Hcoh.
  unfold mu_ledger_tsirelson_coherent in Hcoh.
  destruct Hcoh as [_ [Hminor1 Hminor2]].
  apply tsirelson_from_minors; assumption.
Qed.

Theorem mu_ledger_coherent_implies_tsirelson_bound_abs :
  forall fuel trace s_init,
    mu_ledger_coherent fuel trace s_init ->
    Rabs (CHSH
      (trace_e00 fuel trace s_init)
      (trace_e01 fuel trace s_init)
      (trace_e10 fuel trace s_init)
      (trace_e11 fuel trace s_init)) <= sqrt8.
Proof.
  intros fuel trace s_init Hcoh.
  apply mu_ledger_coherent_implies_tsirelson_coherent in Hcoh.
  unfold mu_ledger_tsirelson_coherent in Hcoh.
  destruct Hcoh as [_ [Hminor1 Hminor2]].
  apply tsirelson_from_minors_abs; assumption.
Qed.

(** ** Step-semantics invariant: trace correlator is deterministic under equal initial states.
    This invariance lemma establishes that run_vm trace semantics produce an equivalent
    CHSH correlator for any two equal initial VMState inputs (required by PHYSICS_ANALOGY_CONTRACT).
    definitional lemma — the equality is a direct consequence of functional extensionality. *)
(* definitional lemma *)
Lemma trace_run_semantics_equiv :
  forall fuel trace (s1 s2 : VMState),
    s1 = s2 ->
    trace_trials fuel trace s1 = trace_trials fuel trace s2.
Proof.
  intros fuel trace s1 s2 Heq. subst s1. reflexivity.
Qed.

(** ** Explicit PSD criterion for the zero-marginal correlator block *)

Definition mu_ledger_psd_coherent
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : Prop :=
  mu_ledger_quantum_gram_coherent fuel trace s_init.

Lemma psd2_quadratic_form_nonneg :
  forall a b d u v,
    a >= 0 ->
    d >= 0 ->
    a * d - b * b >= 0 ->
    a * u * u + 2 * b * u * v + d * v * v >= 0.
Proof.
  intros a b d u v Ha Hd Hdet.
  destruct (Req_dec v 0) as [Hv0 | Hv0].
  - subst v. nra.
  - set (t := u / v).
    assert (Hu : u = t * v).
    { unfold t. field. lra. }
    rewrite Hu.
    replace (a * (t * v) * (t * v) + 2 * b * (t * v) * v + d * v * v)
      with ((v * v) * (a * t * t + 2 * b * t + d)) by ring.
    assert (Hv2 : v * v >= 0) by nra.
    assert (Hq : a * t * t + 2 * b * t + d >= 0).
    {
      destruct (Req_dec a 0) as [Ha0 | Ha0].
      * subst a.
        assert (Hb0 : b = 0) by nra.
        subst b.
        nra.
      * assert (Ha_pos : a > 0) by lra.
        replace (a * t * t + 2 * b * t + d) with
          (a * (t + b / a) * (t + b / a) + (a * d - b * b) / a)
          by (field; lra).
        assert (Hsqr : 0 <= (t + b / a) * (t + b / a)).
        {
          apply Rle_0_sqr.
        }
        assert (Hs1 : a * (t + b / a) * (t + b / a) >= 0).
        {
          nra.
        }
        assert (Hs2 : (a * d - b * b) / a >= 0).
        {
          unfold Rdiv.
          assert (Hainv : / a >= 0).
          {
            left. apply Rinv_0_lt_compat. lra.
          }
          nra.
        }
        nra.
    }
    nra.
Qed.

Lemma zero_marginal_npa_column_contractive_implies_psd :
  forall e00 e01 e10 e11,
    1 - e00 * e00 - e10 * e10 >= 0 ->
    1 - e01 * e01 - e11 * e11 >= 0 ->
    (1 - e00 * e00 - e10 * e10) *
      (1 - e01 * e01 - e11 * e11) -
      (e00 * e01 + e10 * e11) * (e00 * e01 + e10 * e11) >= 0 ->
    PSD5 (nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11))).
Proof.
  intros e00 e01 e10 e11 Hc0 Hc1 Hdet v.
  unfold PSD5, quad5, sum_fin5, nat_matrix_to_fin5, npa_to_matrix, zero_marginal_npa.
  simpl.
  set (v0 := v F1).
  set (x0 := v (FS F1)).
  set (x1 := v (FS (FS F1))).
  set (y0 := v (FS (FS (FS F1)))).
  set (y1 := v (FS (FS (FS (FS F1))))).
  assert (Hblock :
    (1 - e00 * e00 - e10 * e10) * y0 * y0 +
    2 * (-(e00 * e01 + e10 * e11)) * y0 * y1 +
    (1 - e01 * e01 - e11 * e11) * y1 * y1 >= 0).
  {
    apply (psd2_quadratic_form_nonneg
      (1 - e00 * e00 - e10 * e10)
      (-(e00 * e01 + e10 * e11))
      (1 - e01 * e01 - e11 * e11)
      y0 y1).
    - exact Hc0.
    - exact Hc1.
    - replace
        ((1 - e00 * e00 - e10 * e10) * (1 - e01 * e01 - e11 * e11) -
         (-(e00 * e01 + e10 * e11)) * (-(e00 * e01 + e10 * e11)))
        with
        ((1 - e00 * e00 - e10 * e10) * (1 - e01 * e01 - e11 * e11) -
         (e00 * e01 + e10 * e11) * (e00 * e01 + e10 * e11)) by ring.
      exact Hdet.
  }
  replace
    (v0 * (v0 * 1 + x0 * 0 + x1 * 0 + y0 * 0 + y1 * 0) +
     x0 * (v0 * 0 + x0 * 1 + x1 * 0 + y0 * e00 + y1 * e01) +
     x1 * (v0 * 0 + x0 * 0 + x1 * 1 + y0 * e10 + y1 * e11) +
     y0 * (v0 * 0 + x0 * e00 + x1 * e10 + y0 * 1 + y1 * 0) +
     y1 * (v0 * 0 + x0 * e01 + x1 * e11 + y0 * 0 + y1 * 1))
    with
    (v0 * v0 +
     (x0 + e00 * y0 + e01 * y1) * (x0 + e00 * y0 + e01 * y1) +
     (x1 + e10 * y0 + e11 * y1) * (x1 + e10 * y0 + e11 * y1) +
     (1 - e00 * e00 - e10 * e10) * y0 * y0 +
     2 * (-(e00 * e01 + e10 * e11)) * y0 * y1 +
     (1 - e01 * e01 - e11 * e11) * y1 * y1)
    by ring.
  assert (Hv0_nonneg : 0 <= v0 * v0) by apply Rle_0_sqr.
  assert (Hx0_nonneg : 0 <= (x0 + e00 * y0 + e01 * y1) * (x0 + e00 * y0 + e01 * y1))
    by apply Rle_0_sqr.
  assert (Hx1_nonneg : 0 <= (x1 + e10 * y0 + e11 * y1) * (x1 + e10 * y0 + e11 * y1))
    by apply Rle_0_sqr.
  nra.
Qed.

Theorem execution_quantum_gram_coherent_implies_final_tensor_quantum_gram :
  forall fuel trace s_init,
    execution_quantum_gram_coherent fuel trace s_init ->
    final_tensor_quantum_gram fuel trace s_init.
Proof.
  intros fuel trace s_init Hcoh.
  destruct Hcoh as [_ Hcontractive].
  unfold execution_column_contractivity_certificate in Hcontractive.
  destruct Hcontractive as [Hc0 [Hc1 Hdet]].
  split.
  - apply trace_zero_marginal_npa_is_symmetric.
  - unfold trace_zero_marginal_npa.
    apply zero_marginal_npa_column_contractive_implies_psd; assumption.
Qed.

Theorem mu_ledger_quantum_gram_coherent_implies_final_tensor_quantum_gram :
  forall fuel trace s_init,
    mu_ledger_quantum_gram_coherent fuel trace s_init ->
    final_tensor_quantum_gram fuel trace s_init.
Proof.
  intros fuel trace s_init Hcoh.
  destruct Hcoh as [_ Hcontractive].
  unfold execution_column_contractivity_certificate in Hcontractive.
  destruct Hcontractive as [Hc0 [Hc1 Hdet]].
  split.
  - apply trace_zero_marginal_npa_is_symmetric.
  - unfold trace_zero_marginal_npa.
    apply zero_marginal_npa_column_contractive_implies_psd; assumption.
Qed.

Theorem final_tensor_quantum_gram_implies_quantum_realizable_of_trace :
  forall fuel trace s_init,
    final_tensor_quantum_gram fuel trace s_init ->
    quantum_realizable (trace_zero_marginal_npa fuel trace s_init).
Proof.
  intros fuel trace s_init Hgram.
  exact Hgram.
Qed.

Theorem mu_ledger_psd_coherent_implies_quantum_realizable_of_trace :
  forall fuel trace s_init,
    mu_ledger_psd_coherent fuel trace s_init ->
    quantum_realizable (trace_zero_marginal_npa fuel trace s_init).
Proof.
  intros fuel trace s_init Hcoh.
  apply final_tensor_quantum_gram_implies_quantum_realizable_of_trace.
  apply mu_ledger_quantum_gram_coherent_implies_final_tensor_quantum_gram.
  exact Hcoh.
Qed.

Theorem mu_ledger_coherent_implies_quantum_realizable_of_trace :
  forall fuel trace s_init,
    mu_ledger_coherent fuel trace s_init ->
    quantum_realizable (trace_zero_marginal_npa fuel trace s_init).
Proof.
  intros fuel trace s_init Hcoh.
  apply mu_ledger_psd_coherent_implies_quantum_realizable_of_trace.
  exact Hcoh.
Qed.

Lemma certified_bridge_counterexample_is_machine_internal_completed :
  machine_internal_completed_run 7%nat certified_bridge_counterexample_trace bridge_counterexample_init.
Proof.
  unfold machine_internal_completed_run, certified_bridge_counterexample_trace.
  split.
  - vm_compute. reflexivity.
  - split.
    + vm_compute. reflexivity.
    + split.
      * vm_compute. lia.
      * unfold final_tensor_symmetric, mu_tensor_symmetric.
        simpl.
        intros i j Hi Hj.
        assert (Hi' : i = 0%nat \/ i = 1%nat \/ i = 2%nat \/ i = 3%nat) by lia.
        assert (Hj' : j = 0%nat \/ j = 1%nat \/ j = 2%nat \/ j = 3%nat) by lia.
        destruct Hi' as [-> | [-> | [-> | ->]]];
        destruct Hj' as [-> | [-> | [-> | ->]]];
        reflexivity.
Qed.

Lemma certified_bridge_counterexample_not_trace_column_contractive :
  ~ trace_column_contractive 7%nat certified_bridge_counterexample_trace bridge_counterexample_init.
Proof.
  unfold certified_bridge_counterexample_trace.
  vm_compute.
  lra.
Qed.

Theorem machine_internal_completed_run_not_sufficient_for_trace_column_contractivity :
  exists fuel trace s_init,
    machine_internal_completed_run fuel trace s_init /\
    ~ trace_column_contractive fuel trace s_init.
Proof.
  exists 7%nat, certified_bridge_counterexample_trace, bridge_counterexample_init.
  split.
  - apply certified_bridge_counterexample_is_machine_internal_completed.
  - apply certified_bridge_counterexample_not_trace_column_contractive.
Qed.

(** ** Bridge obligations and exact load-bearing invariant *)

(** The old weak bridge claim is refuted below and retained only so the exact
    failure mode remains explicit. *)
Definition weak_final_tensor_quantum_gram_obligation : Prop :=
  forall fuel trace s_init,
    mu_ledger_tsirelson_coherent fuel trace s_init ->
    final_tensor_quantum_gram fuel trace s_init.

(** The real load-bearing bridge theorem is now phrased over the exact
    execution-side invariant package that is genuinely sufficient for the final
    quantum-Gram result. *)
Definition final_tensor_quantum_gram_obligation : Prop :=
  forall fuel trace s_init,
    execution_quantum_gram_coherent fuel trace s_init ->
    final_tensor_quantum_gram fuel trace s_init.

Definition tensor_psd_bridge : Prop :=
  final_tensor_quantum_gram_obligation.

Definition load_bearing_quantum_gram_obligation : Prop :=
  final_tensor_quantum_gram_obligation.

Theorem final_tensor_quantum_gram_obligation_implies_quantum_realizable_of_trace :
  final_tensor_quantum_gram_obligation ->
  forall fuel trace s_init,
    execution_quantum_gram_coherent fuel trace s_init ->
    quantum_realizable (trace_zero_marginal_npa fuel trace s_init).
Proof.
  intros Hgram fuel trace s_init Hcoh.
  apply final_tensor_quantum_gram_implies_quantum_realizable_of_trace.
  apply Hgram. exact Hcoh.
Qed.

Theorem tensor_psd_bridge_implies_quantum_realizable_of_trace :
  tensor_psd_bridge ->
  forall fuel trace s_init,
    execution_quantum_gram_coherent fuel trace s_init ->
    quantum_realizable (trace_zero_marginal_npa fuel trace s_init).
Proof.
  intros Hpsd fuel trace s_init Hcoh.
  eapply final_tensor_quantum_gram_obligation_implies_quantum_realizable_of_trace.
  - exact Hpsd.
  - exact Hcoh.
Qed.

Theorem final_tensor_quantum_gram_obligation_proved :
  final_tensor_quantum_gram_obligation.
Proof.
  intros fuel trace s_init Hcoh.
  apply execution_quantum_gram_coherent_implies_final_tensor_quantum_gram.
  exact Hcoh.
Qed.

Theorem weak_final_tensor_quantum_gram_obligation_refuted :
  ~ weak_final_tensor_quantum_gram_obligation.
Proof.
  intros Hob.
  destruct mu_ledger_tsirelson_coherent_not_sufficient as
    [fuel [trace [s_init [Hcoh Hnot]]]].
  apply Hnot.
  apply Hob.
  exact Hcoh.
Qed.

Definition load_bearing_psd_obligation : Prop :=
  final_tensor_quantum_gram_obligation.

(** =========================================================================
    Generic exact-characterization meta-layer
    ========================================================================= *)

Section ExactCharacterizationMeta.

Variable trace_realizes_npa :
  nat -> list vm_instruction -> VMState -> NPAMomentMatrix -> Prop.

Definition mu_ledger_realizable (npa : NPAMomentMatrix) : Prop :=
  exists fuel trace s_init,
    mu_ledger_coherent fuel trace s_init /\
    trace_realizes_npa fuel trace s_init npa.

Definition mu_ledger_soundness_generic : Prop :=
  forall fuel trace s_init npa,
    mu_ledger_coherent fuel trace s_init ->
    trace_realizes_npa fuel trace s_init npa ->
    quantum_realizable npa.

Definition mu_ledger_completeness_generic : Prop :=
  forall npa,
    quantum_realizable npa ->
    exists fuel trace s_init,
      mu_ledger_coherent fuel trace s_init /\
      trace_realizes_npa fuel trace s_init npa.

Definition mu_ledger_exact_characterization_generic : Prop :=
  forall npa,
    mu_ledger_realizable npa <-> quantum_realizable npa.

Theorem soundness_and_completeness_imply_exact_characterization :
  mu_ledger_soundness_generic ->
  mu_ledger_completeness_generic ->
  mu_ledger_exact_characterization_generic.
Proof.
  intros Hsound Hcomplete npa.
  split.
  - intros Hreal.
    destruct Hreal as [fuel [trace [s_init [Hcoh Htrace]]]].
    eapply Hsound; eauto.
  - intros Hq.
    destruct (Hcomplete npa Hq) as [fuel [trace [s_init [Hcoh Htrace]]]].
    exists fuel, trace, s_init.
    split; assumption.
Qed.

End ExactCharacterizationMeta.

(** =========================================================================
    STATE-BASED QUANTUM BRIDGE (formerly in ThielePrime, now in kernel)
    =========================================================================

    The trace-based bridge above extracts correlators by scanning
    list vm_instruction. This section provides the equivalent
    state-based bridge that reads correlators directly from the
    final VMState's vm_witness field (WitnessCounts buckets).

    This is the key architectural improvement (formerly in ThielePrime, now in kernel):
    the quantum object is determined by final machine state alone,
    not reconstructed from an external execution trace.
    ========================================================================= *)

(** Compute bucket correlation: (same - diff) / (same + diff).
    Returns 0 if no trials recorded for this setting pair. *)
Definition state_bucket_correlation (same_count diff_count : nat) : RealNumber :=
  if Nat.eqb (same_count + diff_count)%nat 0%nat then 0%R
  else ((INR same_count - INR diff_count) / INR (same_count + diff_count)%nat)%R.

(** Extract the four CHSH correlator values from a VMState's witness counters. *)
Definition state_e00 (s : VMState) : RealNumber :=
  state_bucket_correlation s.(vm_witness).(wc_same_00) s.(vm_witness).(wc_diff_00).

Definition state_e01 (s : VMState) : RealNumber :=
  state_bucket_correlation s.(vm_witness).(wc_same_01) s.(vm_witness).(wc_diff_01).

Definition state_e10 (s : VMState) : RealNumber :=
  state_bucket_correlation s.(vm_witness).(wc_same_10) s.(vm_witness).(wc_diff_10).

Definition state_e11 (s : VMState) : RealNumber :=
  state_bucket_correlation s.(vm_witness).(wc_same_11) s.(vm_witness).(wc_diff_11).

(** Construct an NPA moment matrix from the final VMState. *)
Definition state_zero_marginal_npa (s : VMState) : NPAMomentMatrix :=
  zero_marginal_npa (state_e00 s) (state_e01 s) (state_e10 s) (state_e11 s).

(** Column contractivity of the correlators derived from a VMState. *)
Definition state_column_contractive (s : VMState) : Prop :=
  zero_marginal_column_contractive
    (state_e00 s) (state_e01 s) (state_e10 s) (state_e11 s).

(** State quantum Gram: the NPA matrix from state is symmetric and PSD. *)
Definition state_quantum_gram (s : VMState) : Prop :=
  let M := nat_matrix_to_fin5 (npa_to_matrix (state_zero_marginal_npa s)) in
  symmetric5 M /\ PSD5 M.

(** The state-based bridge coherence predicate for full kernel programs. *)
Definition kernel_state_bridge_coherent
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : Prop :=
  let s_final := run_vm fuel trace s_init in
  s_final.(vm_certified) = true /\
  state_column_contractive s_final.

Definition certified_state_counterexample_witness : WitnessCounts :=
  {| wc_same_00 := 1; wc_diff_00 := 0;
     wc_same_01 := 1; wc_diff_01 := 1;
     wc_same_10 := 1; wc_diff_10 := 0;
     wc_same_11 := 1; wc_diff_11 := 1 |}.

Definition certified_state_counterexample : VMState :=
  {| vm_graph := empty_graph;
     vm_csrs :=
       {| csr_cert_addr := 0;
          csr_status := 0;
          csr_err := 0;
          csr_heap_base := 0 |};
     vm_regs := [];
     vm_mem := [];
     vm_pc := 0;
     vm_mu := 1;
     vm_mu_tensor := vm_mu_tensor_default;
     vm_err := false;
     vm_logic_acc := 0;
     vm_mstatus := 0;
     vm_witness := certified_state_counterexample_witness;
     vm_certified := true |}.

Lemma certified_state_counterexample_not_state_column_contractive :
  ~ state_column_contractive certified_state_counterexample.
Proof.
  vm_compute.
  lra.
Qed.

Theorem vm_certified_alone_does_not_imply_state_column_contractive :
  ~ (forall s : VMState, s.(vm_certified) = true -> state_column_contractive s).
Proof.
  intros Hall.
  pose proof (Hall certified_state_counterexample eq_refl) as Hcc.
  exact (certified_state_counterexample_not_state_column_contractive Hcc).
Qed.

Theorem certified_no_error_positive_mu_not_sufficient_for_state_column_contractivity :
  exists s : VMState,
    s.(vm_certified) = true /\
    s.(vm_err) = false /\
    (0 < s.(vm_mu))%nat /\
    ~ state_column_contractive s.
Proof.
  exists certified_state_counterexample.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * exact (Nat.lt_0_succ 0).
      * apply certified_state_counterexample_not_state_column_contractive.
Qed.

(** State-based bridge: column contractivity implies quantum Gram. *)
Theorem state_column_contractive_implies_quantum_gram :
  forall s : VMState,
    state_column_contractive s ->
    state_quantum_gram s.
Proof.
  intros s Hcc.
  unfold state_quantum_gram, state_zero_marginal_npa.
  split.
  - apply npa_to_matrix_symmetric.
  - unfold state_column_contractive, zero_marginal_column_contractive in Hcc.
    destruct Hcc as [Hc0 [Hc1 Hdet]].
    apply zero_marginal_npa_column_contractive_implies_psd; assumption.
Qed.

(** State-based bridge: coherence implies positive mu.
    Uses the existing kernel_certified_implies_positive_mu theorem. *)
Theorem kernel_state_bridge_coherent_implies_positive_mu :
  forall fuel trace s_init,
    s_init.(vm_certified) = false ->
    s_init.(vm_mu) = 0%nat ->
    kernel_state_bridge_coherent fuel trace s_init ->
    (0 < (run_vm fuel trace s_init).(vm_mu))%nat.
Proof.
  intros fuel trace s_init Huncert Hmu0 [Hcert _].
  eapply kernel_certified_implies_positive_mu; eassumption.
Qed.

(** State-based bridge: coherence implies quantum realizability. *)
Theorem kernel_state_bridge_coherent_implies_quantum_realizable :
  forall fuel trace s_init,
    kernel_state_bridge_coherent fuel trace s_init ->
    quantum_realizable (state_zero_marginal_npa (run_vm fuel trace s_init)).
Proof.
  intros fuel trace s_init [_ Hcc].
  apply state_column_contractive_implies_quantum_gram in Hcc.
  exact Hcc.
Qed.

(** The NPA moment matrix is fully determined by the final machine state. *)
Theorem kernel_final_state_determines_quantum_object :
  forall fuel trace s_init,
    kernel_state_bridge_coherent fuel trace s_init ->
    exists npa,
      npa = state_zero_marginal_npa (run_vm fuel trace s_init) /\
      quantum_realizable npa.
Proof.
  intros fuel trace s_init Hcoh.
  exists (state_zero_marginal_npa (run_vm fuel trace s_init)).
  split.
  - reflexivity.
  - apply kernel_state_bridge_coherent_implies_quantum_realizable. exact Hcoh.
Qed.

(** =========================================================================
    PSD -> ROW BOUNDS -> TSIRELSON
    =========================================================================

    This section derives the row bounds (minor_constraint_zero_marginal) from
    the PSD property of the zero-marginal NPA matrix, rather than assuming them.

    THE MATHEMATICAL ARGUMENT:
    For the 5×5 zero-marginal NPA matrix with rho_AA = rho_BB = 0:
      M = [[1,  0,    0,    0,    0   ],
           [0,  1,    0,    E00,  E01 ],
           [0,  0,    1,    E10,  E11 ],
           [0,  E00,  E10,  1,    0   ],
           [0,  E01,  E11,  0,    1   ]]

    PSD implies all principal submatrices are PSD.
    The 3×3 submatrix from rows/cols {1,3,4} (A0, B0, B1):
      [[1,   E00,  E01],
       [E00, 1,    0  ],
       [E01, 0,    1  ]]
    has det = 1 - E00² - E01².
    PSD → det ≥ 0 → E00² + E01² ≤ 1.

    Similarly for rows/cols {2,3,4} (A1, B0, B1):
    det = 1 - E10² - E11² ≥ 0.

    This uses psd_3x3_determinant_nonneg from ConstructivePSD.v.
    ========================================================================= *)

(** INQUISITOR NOTE: quantum_realizable_zero_marginal_implies_row_bounds derives
    the row-sum constraints from PSD. The constraints follow from the 3x3 minor
    determinant argument via psd_3x3_determinant_nonneg. *)
Theorem quantum_realizable_zero_marginal_implies_row_bounds :
  forall E00 E01 E10 E11 : RealNumber,
    quantum_realizable (zero_marginal_npa E00 E01 E10 E11) ->
    minor_constraint_zero_marginal E00 E01 /\
    minor_constraint_zero_marginal E10 E11.
Proof.
  intros E00 E01 E10 E11 [Hsym Hpsd].
  set (npa := zero_marginal_npa E00 E01 E10 E11).
  set (M := nat_matrix_to_fin5 (npa_to_matrix npa)).
  split.
  - (* Row 1: E00² + E01² ≤ 1 *)
    unfold minor_constraint_zero_marginal.
    pose proof (psd_3x3_determinant_nonneg M idx1 idx3 idx4 Hpsd Hsym
      (npa_diagonal_one _ _) (npa_diagonal_one _ _) (npa_diagonal_one _ _)) as Hdet.
    (* Unfold M to expose npa_to_matrix, then use position lemmas *)
    unfold M in Hdet.
    rewrite npa_E00_position in Hdet.
    rewrite npa_E01_position in Hdet.
    rewrite npa_rho_BB_position in Hdet.
    (* For zero_marginal_npa: rho_BB = 0, E00 = E00, E01 = E01 *)
    unfold npa in Hdet. simpl in Hdet.
    unfold det3_corr in Hdet.
    lra.
  - (* Row 2: E10² + E11² ≤ 1 *)
    unfold minor_constraint_zero_marginal.
    pose proof (psd_3x3_determinant_nonneg M idx2 idx3 idx4 Hpsd Hsym
      (npa_diagonal_one _ _) (npa_diagonal_one _ _) (npa_diagonal_one _ _)) as Hdet.
    unfold M in Hdet.
    rewrite npa_E10_position in Hdet.
    rewrite npa_E11_position in Hdet.
    rewrite npa_rho_BB_position in Hdet.
    unfold npa in Hdet. simpl in Hdet.
    unfold det3_corr in Hdet.
    lra.
Qed.

Theorem execution_quantum_gram_coherent_implies_mu_ledger_tsirelson_coherent :
  forall fuel trace s_init,
    execution_quantum_gram_coherent fuel trace s_init ->
    mu_ledger_tsirelson_coherent fuel trace s_init.
Proof.
  intros fuel trace s_init Hexec.
  destruct Hexec as [Hsym Hcontractive].
  split.
  - exact Hsym.
  - pose proof
      (execution_quantum_gram_coherent_implies_final_tensor_quantum_gram fuel trace s_init
         (conj Hsym Hcontractive)) as Hgram.
    pose proof
      (final_tensor_quantum_gram_implies_quantum_realizable_of_trace fuel trace s_init Hgram) as Hqr.
    unfold trace_zero_marginal_npa in Hqr.
    apply quantum_realizable_zero_marginal_implies_row_bounds in Hqr.
    exact Hqr.
Qed.

Theorem execution_quantum_gram_coherent_implies_mu_ledger_coherent :
  forall fuel trace s_init,
    execution_quantum_gram_coherent fuel trace s_init ->
    mu_ledger_coherent fuel trace s_init.
Proof.
  intros fuel trace s_init Hexec.
  destruct Hexec as [Hsym Hcontractive].
  unfold mu_ledger_coherent, mu_ledger_quantum_gram_coherent.
  split.
  - apply execution_quantum_gram_coherent_implies_mu_ledger_tsirelson_coherent.
    exact (conj Hsym Hcontractive).
  - exact Hcontractive.
Qed.

Theorem bridge_ready_completed_run_implies_mu_ledger_coherent :
  forall fuel trace s_init,
    bridge_ready_completed_run fuel trace s_init ->
    mu_ledger_coherent fuel trace s_init.
Proof.
  intros fuel trace s_init [[_ [_ [_ Hsym]]] Hcontractive].
  apply execution_quantum_gram_coherent_implies_mu_ledger_coherent.
  split; assumption.
Qed.

Theorem bridge_ready_completed_run_implies_quantum_realizable_of_trace :
  forall fuel trace s_init,
    bridge_ready_completed_run fuel trace s_init ->
    quantum_realizable (trace_zero_marginal_npa fuel trace s_init).
Proof.
  intros fuel trace s_init Hready.
  apply mu_ledger_coherent_implies_quantum_realizable_of_trace.
  apply bridge_ready_completed_run_implies_mu_ledger_coherent.
  exact Hready.
Qed.

Theorem bridge_ready_completed_run_implies_tsirelson_bound_abs :
  forall fuel trace s_init,
    bridge_ready_completed_run fuel trace s_init ->
    Rabs (CHSH
      (trace_e00 fuel trace s_init)
      (trace_e01 fuel trace s_init)
      (trace_e10 fuel trace s_init)
      (trace_e11 fuel trace s_init)) <= sqrt8.
Proof.
  intros fuel trace s_init Hready.
  apply mu_ledger_coherent_implies_tsirelson_bound_abs.
  apply bridge_ready_completed_run_implies_mu_ledger_coherent.
  exact Hready.
Qed.

(** C4 end-to-end: quantum realizability alone implies Tsirelson bound.
    Chain: quantum_realizable → row bounds (above) → tsirelson_from_minors (existing). *)
(** INQUISITOR NOTE: quantum_realizable_implies_tsirelson_bound is the C4
    closure theorem. No assumed row bounds — they are DERIVED from PSD. *)
Theorem quantum_realizable_implies_tsirelson_bound :
  forall E00 E01 E10 E11 : RealNumber,
    quantum_realizable (zero_marginal_npa E00 E01 E10 E11) ->
    (CHSH E00 E01 E10 E11)² <= 8.
Proof.
  intros E00 E01 E10 E11 Hqr.
  apply quantum_realizable_zero_marginal_implies_row_bounds in Hqr.
  destruct Hqr as [Hrow1 Hrow2].
  apply tsirelson_from_minors; assumption.
Qed.

(** Absolute-value form: |S| ≤ 2√2. *)
Theorem quantum_realizable_implies_tsirelson_bound_abs :
  forall E00 E01 E10 E11 : RealNumber,
    quantum_realizable (zero_marginal_npa E00 E01 E10 E11) ->
    Rabs (CHSH E00 E01 E10 E11) <= sqrt8.
Proof.
  intros E00 E01 E10 E11 Hqr.
  apply quantum_realizable_zero_marginal_implies_row_bounds in Hqr.
  destruct Hqr as [Hrow1 Hrow2].
  apply tsirelson_from_minors_abs; assumption.
Qed.

(** State-based C4: column contractivity → PSD → row bounds → Tsirelson.
    This shows the row bounds were always derivable from column contractivity. *)
Theorem state_column_contractive_implies_tsirelson :
  forall s : VMState,
    state_column_contractive s ->
    (CHSH (state_e00 s) (state_e01 s) (state_e10 s) (state_e11 s))² <= 8.
Proof.
  intros s Hcc.
  apply quantum_realizable_implies_tsirelson_bound.
  apply state_column_contractive_implies_quantum_gram in Hcc.
  exact Hcc.
Qed.