From Coq Require Import ZArith Lia List.
Import ListNotations.

From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import SimulationProof.
From Kernel Require Import MuInformation.
From Kernel Require Import MuLedgerConservation.
From Kernel Require Import RevelationRequirement.
From Kernel Require Import NoFreeInsight.
From Kernel Require Import MuNoFreeInsightQuantitative.
From Kernel Require Import QuantumBound.
From Kernel Require Import Certification.

Local Open Scope Z_scope.

Module RandomnessNoFI.

Import RevelationProof.
Import VMStep.VMStep.
Import QuantumBound.
Import CertificationTheory.

(** An operational admissibility/resource constraint.

    This is intentionally receipts/trace-aligned:
    - The observable transcript is the trace (receipt stream) itself.
    - The resource budget is the kernel μ counter (Δμ = mu_info_z).

    This is the Coq-side analogue of “bounded structure-addition / bounded μ”.
*)
Definition Admissible (K : Z) (trace : Trace) (s_init s_final : VMState) (fuel : nat) : Prop :=
  trace_run fuel trace s_init = Some s_final /\
  s_init.(vm_csrs).(csr_cert_addr) = 0%nat /\
  (0 <= K) /\
  mu_info_z s_init s_final <= K.

(** Operational side-condition: cert-setting instructions cost at least 1 μ.

    This is an explicit *encoding* constraint on programs/traces, matching the
    intended reading of μ as a priced, non-free structure-addition resource.

    It is deliberately phrased without reference to a particular execution.
*)
Definition CertSetterPositiveCost : Prop :=
  forall instr,
    MuNoFreeInsightQuantitative.is_cert_setter instr ->
    (1 <= instruction_cost instr)%nat.

Definition AdmissiblePos (K : Z) (trace : Trace) (s_init s_final : VMState) (fuel : nat) : Prop :=
  Admissible K trace s_init s_final fuel /\ CertSetterPositiveCost.

(** Count how many cert-setting instructions are actually executed during a bounded run.

    This is a receipts-aligned metric: it is defined by the same PC-indexed
    stepping as [trace_run], so it counts executed instructions (not merely
    list membership).
*)
Fixpoint cert_setter_count_in_run (fuel : nat) (trace : Trace) (s : VMState) : nat :=
  match fuel with
  | O => 0%nat
  | S fuel' =>
      match nth_error trace (vm_pc s) with
      | None => 0%nat
      | Some instr =>
          let s' := vm_apply s instr in
          (if MuNoFreeInsightQuantitative.is_cert_setterb instr then 1%nat else 0%nat)
            + cert_setter_count_in_run fuel' trace s'
      end
  end.

Definition rng_metric_count (fuel : nat) (trace : Trace) (s_init : VMState) : Z :=
  Z.of_nat (cert_setter_count_in_run fuel trace s_init).

Definition f_count (K : Z) : Z :=
  Z.max 0 K.

(** [is_cert_setterb_true_implies_is_cert_setter]: formal specification. *)
Lemma is_cert_setterb_true_implies_is_cert_setter :
  forall instr,
    MuNoFreeInsightQuantitative.is_cert_setterb instr = true ->
    MuNoFreeInsightQuantitative.is_cert_setter instr.
Proof.
  intros instr Hb.
  unfold MuNoFreeInsightQuantitative.is_cert_setter.
  exact Hb.
Qed.

(** [mu_info_z_chain]: formal specification. *)
Lemma mu_info_z_chain :
  forall s0 s1 s2,
    mu_info_z s0 s2 = (mu_info_z s0 s1 + mu_info_z s1 s2)%Z.
Proof.
  intros s0 s1 s2.
  unfold mu_info_z, mu_total.
  lia.
Qed.

(** [cert_setter_count_in_run_le_mu_info_run_vm]: formal specification. *)
Lemma cert_setter_count_in_run_le_mu_info_run_vm :
  forall fuel trace s,
    CertSetterPositiveCost ->
    (cert_setter_count_in_run fuel trace s <= mu_info_run_vm fuel trace s)%nat.
Proof.
  induction fuel as [|fuel IH]; intros trace s Hpos_all.
  - simpl. lia.
  - simpl.
    destruct (nth_error trace s.(vm_pc)) as [instr|] eqn:Hnth.
    + (* one executed instruction *)
      simpl.
      (* unfold mu_info_run_vm: ledger_sum (ledger_entries ...) *)
      unfold mu_info_run_vm.
      simpl.
      rewrite Hnth.
      simpl.
      (* ledger_entries contributes [instruction_cost instr] at head *)
      destruct (MuNoFreeInsightQuantitative.is_cert_setterb instr) eqn:Hb.
      * assert (Hsetter : MuNoFreeInsightQuantitative.is_cert_setter instr).
        { apply is_cert_setterb_true_implies_is_cert_setter. exact Hb. }
        pose proof (Hpos_all instr Hsetter) as Hpos_cost.
        (* 1 + count_tail <= cost + ledger_tail *)
        specialize (IH trace (vm_apply s instr) Hpos_all).
        (* Use transitivity via (cost + count_tail). *)
        eapply Nat.le_trans with (m := (instruction_cost instr + cert_setter_count_in_run fuel trace (vm_apply s instr))%nat).
        { apply Nat.add_le_mono_r. exact Hpos_cost. }
        { apply Nat.add_le_mono_l. exact IH. }
      * (* not a cert-setter: 0 + count_tail <= cost + ledger_tail *)
        specialize (IH trace (vm_apply s instr) Hpos_all).
        (* count_tail <= ledger_tail <= cost + ledger_tail *)
        eapply Nat.le_trans; [exact IH|].
        apply Nat.le_add_l.
    + (* early stop: both are 0 *)
      unfold mu_info_run_vm.
      simpl.
      lia.
Qed.

(** [cert_setter_count_in_run_le_mu_info_z]: formal specification. *)
Theorem cert_setter_count_in_run_le_mu_info_z :
  forall fuel trace s_init s_final,
    trace_run fuel trace s_init = Some s_final ->
    CertSetterPositiveCost ->
    (Z.of_nat (cert_setter_count_in_run fuel trace s_init) <= mu_info_z s_init s_final)%Z.
Proof.
  intros fuel trace s_init s_final Hrun Hpos.
  (* Translate [trace_run] final state to [run_vm] to reuse μ-ledger facts. *)
  assert (Hsfinal : s_final = run_vm fuel trace s_init).
  { pose proof (NoFreeInsight.trace_run_run_vm fuel trace s_init) as Heq.
    rewrite Hrun in Heq.
    inversion Heq; reflexivity. }
  subst s_final.
  (* Count <= ledger sum (nat), then inject to Z and rewrite mu_info_z. *)
  pose proof (cert_setter_count_in_run_le_mu_info_run_vm fuel trace s_init Hpos) as Hnat.
  apply (Nat2Z.inj_le) in Hnat.
  unfold mu_info_run_vm in Hnat.
  (* mu_info_z s (run_vm ...) = Z.of_nat (ledger_sum ...) *)
  rewrite (mu_info_z_run_vm_is_ledger_sum fuel trace s_init).
  exact Hnat.
Qed.

(** Sharper D4 theorem: the certified metric (count of executed cert-setters)
    is linearly bounded by the μ-budget K.
*)
Theorem admissiblepos_implies_rng_metric_count_le_f_count :
  forall (K : Z) (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    AdmissiblePos K trace s_init s_final fuel ->
    rng_metric_count fuel trace s_init <= f_count K.
Proof.
  intros K trace s_init s_final fuel [Hadm Hpos].
  destruct Hadm as [Hrun [_ [HKnonneg Hmu_le]]].
  unfold rng_metric_count, f_count.
  pose proof (cert_setter_count_in_run_le_mu_info_z fuel trace s_init s_final Hrun Hpos) as Hcount_le.
  (* count <= Δμ <= K, and K>=0 so max 0 K = K *)
  assert (Hmax : Z.max 0 K = K) by (apply Z.max_r; exact HKnonneg).
  rewrite Hmax.
  eapply Z.le_trans; [exact Hcount_le|].
  exact Hmu_le.
Qed.

(** Special case: “no structure addition at all” (K=0-style admissibility).

    This captures the core No-Free-Insight principle at the deterministic kernel
    layer: if the trace contains no cert-setting opcodes, then it cannot set the
    certification CSR.
*)
Definition Admissible0 (trace : Trace) : Prop :=
  quantum_admissible trace.

(** Quantitative bound (D4-style shape):

    If a run is admissible with budget K and nevertheless certifies a supra-CHSH
    claim, then some cert-setter instruction’s cost must fit inside K.

    This is a machine-checked “you can’t certify for free” inequality, phrased
    in the receipts-only view (trace as receipts).
*)
Theorem admissible_implies_cert_cost_leq_budget_for_supra_chsh :
  forall (K : Z) (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    Admissible K trace s_init s_final fuel ->
    Certified s_final supra_quantum_certified trace ->
    NoFreeInsight.has_structure_addition fuel trace s_init /\
    exists instr,
      MuNoFreeInsightQuantitative.is_cert_setter instr /\
      (Z.of_nat (instruction_cost instr) <= K)%Z.
Proof.
  intros K trace s_init s_final fuel Hadm Hcert.
  pose proof Hcert as Hcert_keep.
  destruct Hadm as [Hrun [Hinit [HKnonneg Hmu_le]]].
  destruct Hcert as [Herr [Hsupra_chsh Hhascert]].

  (* Force a concrete downstream dependency on strengthened NoFreeInsight. *)
  set (decoder0 := (fun (_ : Trace) => [0%nat]) : NoFreeInsight.receipt_decoder nat).
  set (P_weak0 := (fun (_ : list nat) => true) : NoFreeInsight.ReceiptPredicate nat).
  set (P_strong0 := (fun obs : list nat =>
                       match obs with
                       | [0%nat] => true
                       | _ => false
                       end) : NoFreeInsight.ReceiptPredicate nat).

  assert (Hstrict0 : NoFreeInsight.strictly_stronger P_strong0 P_weak0).
  {
    unfold NoFreeInsight.strictly_stronger, NoFreeInsight.stronger, P_strong0, P_weak0.
    split.
    - intros obs _. reflexivity.
    - exists []. simpl. split; reflexivity.
  }

  assert (Hcertobs0 : NoFreeInsight.CertifiedObs s_final decoder0 P_strong0 trace).
  {
    unfold NoFreeInsight.CertifiedObs, decoder0, P_strong0.
    split; [exact Herr|reflexivity].
  }

  assert (Hbridge0 :
    forall sf,
      sf = run_vm fuel trace s_init ->
      P_weak0 (decoder0 trace) = true ->
      NoFreeInsight.CertifiedObs sf decoder0 P_strong0 trace ->
      has_supra_cert sf).
  {
    intros sf Hsf _ _.
    subst sf.
    assert (Hsfinal : s_final = run_vm fuel trace s_init).
    { pose proof (NoFreeInsight.trace_run_run_vm fuel trace s_init) as Heq.
      rewrite Hrun in Heq.
      inversion Heq; reflexivity. }
    rewrite <- Hsfinal.
    exact Hhascert.
  }

  pose proof
    (CertificationTheory.no_free_insight_from_strengthening_bridge
       nat decoder0 P_weak0 P_strong0 trace s_init fuel
       Hstrict0 Hinit Hbridge0)
    as Hnofi.
  assert (Hstruct : NoFreeInsight.has_structure_addition fuel trace s_init).
  { apply Hnofi.
    assert (Hsfinal : s_final = run_vm fuel trace s_init).
    { pose proof (NoFreeInsight.trace_run_run_vm fuel trace s_init) as Heq.
      rewrite Hrun in Heq.
      inversion Heq; reflexivity. }
    rewrite <- Hsfinal.
    exact Hcertobs0. }

  pose proof
    (certified_supra_chsh_implies_mu_info_z_lower_bound trace s_init s_final fuel Hrun Hinit Hcert_keep)
    as [instr [Hsetter Hlb]].
  split.
  - exact Hstruct.
  - exists instr.
    split; [exact Hsetter|].
    eapply Z.le_trans.
    + exact Hlb.
    + exact Hmu_le.
Qed.

(** Load-bearing downstream use of strengthened NoFreeInsight theorem.

    This theorem ties the abstract strengthening theorem to the operational
    admissibility envelope used in this file.
*)
Theorem admissible_and_strengthening_obs_implies_structure_addition :
  forall (K : Z)
         (A : Type)
         (decoder : NoFreeInsight.receipt_decoder A)
         (P_weak P_strong : NoFreeInsight.ReceiptPredicate A)
         (trace : Trace)
         (s_init s_final : VMState)
         (fuel : nat),
    Admissible K trace s_init s_final fuel ->
    NoFreeInsight.strictly_stronger P_strong P_weak ->
    (forall sf,
        sf = run_vm fuel trace s_init ->
        P_weak (decoder trace) = true ->
        NoFreeInsight.CertifiedObs sf decoder P_strong trace ->
        has_supra_cert sf) ->
    NoFreeInsight.CertifiedObs s_final decoder P_strong trace ->
    NoFreeInsight.has_structure_addition fuel trace s_init.
Proof.
  intros K A decoder P_weak P_strong trace s_init s_final fuel Hadm Hstrict Hbridge Hcertobs.
  destruct Hadm as [Hrun [Hinit [_ _]]].
  assert (Hsfinal : s_final = run_vm fuel trace s_init).
  { pose proof (NoFreeInsight.trace_run_run_vm fuel trace s_init) as Heq.
    rewrite Hrun in Heq.
    inversion Heq; reflexivity. }
  subst s_final.
  eapply CertificationTheory.no_free_insight_from_strengthening_bridge; eauto.
Qed.

(** Quantum-admissible traces cannot contain structure-addition events.

    Since every instruction in a quantum-admissible trace is a non-cert-setter,
    cert_addr is preserved at zero throughout execution.
*)
Lemma quantum_admissible_implies_no_structure_addition_in_run :
  forall (trace : Trace) (s_init : VMState) (fuel : nat),
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    Admissible0 trace ->
    ~ NoFreeInsight.has_structure_addition fuel trace s_init.
Proof.
  intros trace s_init fuel.
  revert s_init.
  induction fuel as [|fuel IH]; intros s_init Hinit Hadm0 Hsa.
  - unfold NoFreeInsight.has_structure_addition in Hsa.
    simpl in Hsa.
    exact Hsa.
  - unfold NoFreeInsight.has_structure_addition in Hsa.
    simpl in Hsa.
    destruct (nth_error trace (vm_pc s_init)) as [instr|] eqn:Hnth.
    + assert (Hin : In instr trace).
      { apply nth_error_In with (n := vm_pc s_init). exact Hnth. }
      assert (Hnot : is_not_cert_setter instr).
      { unfold Admissible0 in Hadm0.
        eapply quantum_admissible_all_not_cert_setters; eauto. }
      assert (Hpres :
        (vm_apply s_init instr).(vm_csrs).(csr_cert_addr) =
        s_init.(vm_csrs).(csr_cert_addr)).
      { apply vm_apply_preserves_cert_addr. exact Hnot. }
      destruct Hsa as [[_ Hnz] | Hrest].
      * rewrite Hpres in Hnz.
        rewrite Hinit in Hnz.
        contradiction.
      * eapply IH.
        -- rewrite Hpres. exact Hinit.
        -- exact Hadm0.
        -- exact Hrest.
    + exact Hsa.
Qed.

(** Build structure-addition from supra-certification via strengthened NoFI.

    This packages a direct application of
    [NoFreeInsight.strengthening_obs_requires_structure_addition].
*)
Lemma supra_cert_implies_structure_addition_via_nofi :
  forall (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    Certified s_final supra_quantum_certified trace ->
    NoFreeInsight.has_structure_addition fuel trace s_init.
Proof.
  intros trace s_init s_final fuel Hrun Hinit Hcert.
  destruct Hcert as [Herr [_ Hsupra]].
  set (decoder0 := (fun (_ : Trace) => [0%nat]) : NoFreeInsight.receipt_decoder nat).
  set (P_weak0 := (fun (_ : list nat) => true) : NoFreeInsight.ReceiptPredicate nat).
  set (P_strong0 := (fun obs : list nat =>
                       match obs with
                       | [0%nat] => true
                       | _ => false
                       end) : NoFreeInsight.ReceiptPredicate nat).

  assert (Hstrict0 : NoFreeInsight.strictly_stronger P_strong0 P_weak0).
  {
    unfold NoFreeInsight.strictly_stronger, NoFreeInsight.stronger, P_strong0, P_weak0.
    split.
    - intros obs _. reflexivity.
    - exists []. simpl. split; reflexivity.
  }

  assert (Hcertobs0 : NoFreeInsight.CertifiedObs (run_vm fuel trace s_init) decoder0 P_strong0 trace).
  {
    unfold NoFreeInsight.CertifiedObs, decoder0, P_strong0.
    split.
    - assert (Hsfinal : s_final = run_vm fuel trace s_init).
      { pose proof (NoFreeInsight.trace_run_run_vm fuel trace s_init) as Heq.
        rewrite Hrun in Heq.
        inversion Heq; reflexivity. }
      rewrite <- Hsfinal.
      exact Herr.
    - reflexivity.
  }

  assert (Hbridge0 :
    forall sf,
      sf = run_vm fuel trace s_init ->
      P_weak0 (decoder0 trace) = true ->
      NoFreeInsight.CertifiedObs sf decoder0 P_strong0 trace ->
      has_supra_cert sf).
  {
    intros sf Hsf _ _.
    subst sf.
    assert (Hsfinal : s_final = run_vm fuel trace s_init).
    { pose proof (NoFreeInsight.trace_run_run_vm fuel trace s_init) as Heq.
      rewrite Hrun in Heq.
      inversion Heq; reflexivity. }
    rewrite <- Hsfinal.
    exact Hsupra.
  }

  eapply NoFreeInsight.strengthening_obs_requires_structure_addition; eauto.
Qed.

(** A coarse, receipt-aligned randomness metric for D4.

    This intentionally avoids probabilistic semantics: it captures whether the
    run reaches a nonzero certification CSR.

    It is compatible with the Python-side D2 metric, which gates any positive
    randomness claim on structure-addition/certification evidence.
*)
Definition rng_metric_coarse (s_final : VMState) : Z :=
  if Nat.eqb s_final.(vm_csrs).(csr_cert_addr) 0%nat then 0%Z else 1%Z.

Definition f (K : Z) : Z :=
  if Z.leb 1 K then 1%Z else 0%Z.

(** D4-style quantitative bound: under a μ-budget K and the explicit
    CertSetterPositiveCost encoding constraint, the coarse certified randomness
    metric cannot exceed f(K).

    Intuition:
    - If K < 1, a cert-setter step would force Δμ >= 1, contradicting the budget.
    - If K >= 1, the metric is trivially ≤ 1.
*)
Theorem admissiblepos_implies_rng_metric_coarse_leq_f :
  forall (K : Z) (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    AdmissiblePos K trace s_init s_final fuel ->
    rng_metric_coarse s_final <= f K.
Proof.
  intros K trace s_init s_final fuel Hadmpos.
  destruct Hadmpos as [Hadm Hpos].
  destruct Hadm as [Hrun [Hinit [HKnonneg Hmu_le]]].
  unfold rng_metric_coarse, f.
  destruct (Nat.eqb s_final.(vm_csrs).(csr_cert_addr) 0%nat) eqn:Hcz.
  - (* no certification: metric=0 *)
    simpl.
    destruct (Z.leb_spec 1 K); lia.
  - (* certification present: metric=1, show K>=1 so f(K)=1 *)
    assert (Hsup : has_supra_cert s_final).
    { unfold has_supra_cert.
      apply Nat.eqb_neq in Hcz.
      exact Hcz.
    }
    pose proof
      (MuNoFreeInsightQuantitative.supra_cert_implies_mu_lower_bound_trace_run fuel trace s_init s_final Hrun Hinit Hsup)
      as [instr [Hsetter Hmu_nat]].
    specialize (Hpos instr Hsetter).
    (* Convert the Nat lower bound into a Z lower bound on mu_info_z. *)
    assert (Hcost_ge1_z : (1 <= Z.of_nat (instruction_cost instr))%Z).
    { apply (Nat2Z.inj_le 1 (instruction_cost instr)). exact Hpos. }
    (* From Hmu_z we have: μ_init + cost <= μ_final, so cost <= Δμ. *)
    assert (Hcost_le_delta : (Z.of_nat (instruction_cost instr) <= mu_info_z s_init s_final)%Z).
    {
      unfold mu_info_z, mu_total.
      pose proof (proj1 (Nat2Z.inj_le (vm_mu s_init + instruction_cost instr) (vm_mu s_final)) Hmu_nat)
        as Hmu_z.
      rewrite Nat2Z.inj_add in Hmu_z.
      lia.
    }
    assert (HK_ge1 : (1 <= K)%Z).
    { eapply Z.le_trans; [exact Hcost_ge1_z|].
      eapply Z.le_trans; [exact Hcost_le_delta|].
      exact Hmu_le.
    }
    destruct (Z.leb_spec 1 K); lia.
Qed.

(** Confrontation lemma:

    A trace may contain any CHSH_TRIAL receipts (even supra-Tsirelson), but if it
    is quantum-admissible (no cert-setters), then it cannot be *certified* as
    supra-quantum.
*)
Theorem quantum_admissible_cannot_certify_supra_chsh :
  forall (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    Admissible0 trace ->
    ~ Certified s_final supra_quantum_certified trace.
Proof.
  intros trace s_init s_final fuel Hrun Hinit Hadm0 Hcert.
  assert (Hstruct : NoFreeInsight.has_structure_addition fuel trace s_init).
  { eapply supra_cert_implies_structure_addition_via_nofi; eauto. }
  assert (Hnostruct : ~ NoFreeInsight.has_structure_addition fuel trace s_init).
  { eapply quantum_admissible_implies_no_structure_addition_in_run; eauto. }
  contradiction.
Qed.

End RandomnessNoFI.
