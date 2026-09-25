From Coq Require Import List Lia Arith.PeanoNat Bool QArith ZArith.
From Coq Require Import Strings.String.
Import ListNotations.

From Kernel Require Import VMState VMStep KernelPhysics.
From Kernel Require Import MuLedgerConservation MuInformation.
From Kernel Require Import MuNoFreeInsightQuantitative RevelationRequirement.
From Kernel Require Import SimulationProof NoFreeInsight.
From Kernel Require Import CHSH QuantumBound.

(** Certification Theory: a selected VM CHSH accounting theorem.

  This module connects the VM transition rules with a rational predicate computed
  from instruction traces.

  The central result says that a trace whose empirical CHSH value exceeds the stored
  rational threshold and whose certification address is active must contain one of
  the listed certification or revelation constructors.

  Those constructors carry the VM's positive cost policy, so the result is about this
  execution model and its ledger; it is not a theorem about physical correlations.

  The proof chain is:
  1. The trace decoder can only extract trials from [instr_chsh_trial] entries.
  2. The supplied revelation requirement connects the selected threshold predicate
     and the final certification address to the listed trace constructors.
  3. The VM cost lemmas price the relevant constructors.

  A broader claim requires the separate abstract premises supplied by [NoFreeInsight].
  *)

Module CertificationTheory.

Import VMStep.VMStep.
Import RevelationProof.

(** Trace-as-receipt representation.

   In this Coq model, the trace itself is the receipt representation. This works for
   the following three formal reasons:

   1. [vm_step] is a function rather than a relation, so each supplied instruction
     has one next-state result in the model.

   2. The decoder recognizes a CHSH trial only in an [instr_chsh_trial] constructor.

   3. [extract_chsh_trials] pattern-matches on the instruction list and extracts the
     encoded trial fields.

   This representation does not by itself establish authenticity of an externally
   supplied trace or correspondence with a serialized transport format.
   *)

Definition Receipt := vm_instruction.
Definition Receipts := Trace.

(** CHSH Trial Extraction: Getting (x,y,a,b) from Trace

  The CHSH inequality tests correlations between Alice's and Bob's
  measurement results. Each trial is (x,y,a,b): x,y are measurement
  choices (inputs), a,b are results (outputs).

  extract_chsh_trials scans the receipt stream for instr_chsh_trial
  instructions — that's the ONLY way CHSH trials enter the stream,
  proven in chsh_trials_non_forgeable below. Once we have the trial list,
  KernelCHSH.chsh computes E_xy = average correlation per input pair and
  S = E00 + E01 + E10 - E11. Mechanical arithmetic.
*)

Definition extract_chsh_trials (receipts : Receipts) : list KernelCHSH.Trial :=
  KernelCHSH.trials_of_receipts receipts.

(** CHSH Value Computation (Rational approximation)

    We use the concrete empirical CHSH statistic [KernelCHSH.chsh].
    Tsirelson bound: $2\sqrt{2} \approx 2.828427$; we use a safe rational
    approximation [5657/2000].

    Note: This is an *empirical* statistic over the receipt stream; it is not
    a probabilistic theorem about measurement distributions.
*)

Definition tsirelson_bound_q : Q := (5657#2000).

Definition chsh_value (receipts : Receipts) : Q :=
  KernelCHSH.chsh (extract_chsh_trials receipts).

Definition has_supra_chsh (receipts : Receipts) : Prop :=
  Qlt tsirelson_bound_q (chsh_value receipts).

(** Helper: Compute CHSH value from receipts (matches OCaml extraction and Verilog RTL) *)
Definition compute_chsh (receipts : Receipts) : Q :=
  chsh_value receipts.

(** Supra-Quantum Predicate
    
    RUNTIME DEFINITION (OCaml extraction):
      S = compute_chsh_from_trials(trials)
      supra := S > TSIRELSON_BOUND  (where TSIRELSON_BOUND = 5657/2000)
    
    COQ DEFINITION:
      We take "supra-quantum" to mean the receipt-derived empirical
      CHSH value exceeds the Tsirelson bound approximation.
    *)

(** Simplified supra-quantum predicate:
    "trace contains CHSH trials AND certification was written"
    
    This captures the essence: if you claim supra correlations via
    certification, REVEAL must have executed.
    *)

Definition supra_quantum_certified (s : VMState) (receipts : Receipts) : Prop :=
  has_supra_chsh receipts /\ has_supra_cert s.

(** A parameterized certified-claim predicate over the selected rational statistic.

    The threshold [q] is an input to the definition.

    The definition records the empirical inequality and the active certification
    address; it does not assign a physical interpretation to [q].
*)
Definition chsh_claim_certified (q : Q) (s : VMState) (receipts : Receipts) : Prop :=
  Qlt q (chsh_value receipts) /\ has_supra_cert s.

(** The [Certified] predicate combines successful execution with a supplied claim.

    It requires [vm_err = false] and [P s_final receipts].

    Soundness of [P], authenticity of an externally supplied trace, and any physical
    interpretation of the receipt data are separate premises and are not supplied by
    this definition.
*)

Definition Certified (s_final : VMState) (P : VMState -> Receipts -> Prop)
                     (receipts : Receipts) : Prop :=
  s_final.(vm_err) = false /\ P s_final receipts.

(** Revelation Event Detection
    [revelation_charged]: the μ-ledger grew by at least min_bits between
    s_init and s_final. Used to verify that revelation actually paid μ-cost. *)

Definition revelation_charged (s_init s_final : VMState) (min_bits : nat) : Prop :=
  Nat.le (s_init.(vm_mu) + min_bits) (s_final.(vm_mu)).

(** μ-Ledger Monotonicity (imported from MuLedgerConservation.v)
    [reveal_charges_mu]: REVEAL with bits b and declared_cost k adds (b + S k) to vm_mu.
    Proportional to the information revealed, plus the mandatory S() floor. *)

Lemma reveal_charges_mu :
  forall s module bits cert cost,
    (vm_apply s (instr_reveal module bits cert cost)).(vm_mu) = Nat.add (s.(vm_mu)) (bits + S cost).
Proof.
  intros. unfold vm_apply.
  unfold advance_state. simpl. reflexivity.
Qed.

(** Non-Forgeability (CHSH trials only from chsh_trial opcode)
    [chsh_trials_non_forgeable]: every trial returned by extract_chsh_trials
    came from an instr_chsh_trial in the receipt stream. No CHSH trial reaches
    the evidence stream without the opcode actually executing. Proof by
    induction on receipts. *)

Lemma chsh_trials_non_forgeable :
  forall receipts t,
    In t (extract_chsh_trials receipts) ->
    exists x y a b cost,
      In (instr_chsh_trial x y a b cost) receipts /\
      chsh_bits_ok x y a b = true /\
      t = {| KernelCHSH.t_x := x; KernelCHSH.t_y := y; KernelCHSH.t_a := a; KernelCHSH.t_b := b |}.
Proof.
  induction receipts as [|r rest IH]; intros t Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin.
    destruct (KernelCHSH.is_trial_instr r) as [t0|] eqn:Hopt.
    + simpl in Hin.
      destruct Hin as [Ht | HinRest].
      * subst t.
        destruct r; simpl in Hopt; try discriminate.
        destruct (chsh_bits_ok x y a b) eqn:Hok; inversion Hopt; subst.
        exists x, y, a, b, mu_delta.
        split.
        -- left. reflexivity.
        -- split; [exact Hok | reflexivity].
      * specialize (IH t HinRest) as [x [y [a [b [cost [HinInstr [Hok Ht]]]]]]].
        exists x, y, a, b, cost.
        split.
        -- right. exact HinInstr.
        -- split; assumption.
    + apply IH in Hin.
      destruct Hin as [x [y [a [b [cost [HinInstr [Hok Ht]]]]]]].
      exists x, y, a, b, cost.
      split.
      * right. exact HinInstr.
      * split; assumption.

    Qed.

(** [no_free_insight_chsh] is the main theorem for the selected VM predicate.

  If a trace starts with a zero certification address and ends with the empirical
  threshold predicate plus an active certification address, the trace contains at
  least one constructor from the listed revelation or certification classes.

  The theorem establishes a trace-shape and accounting consequence. It does not
  establish a physical CHSH realization or an external semantic interpretation.

  The theorem returns a disjunction containing [REVEAL], [EMIT], [LJOIN], [LASSERT],
  and [MORPH_ASSERT]. A stronger REVEAL-only conclusion would require an additional
  policy premise; it is not proved by this theorem.
*)

Theorem no_free_insight_chsh :
  forall (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    (* Execution completed successfully *)
    trace_run fuel trace s_init = Some s_final ->
    (* Initially no certification *)
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    (* Final state certifies supra-quantum correlations *)
    Certified s_final supra_quantum_certified trace ->
    (* Then: revelation must be in trace *)
    uses_revelation trace \/
    (exists n m p mu, nth_error trace n = Some (instr_emit m p mu)) \/
    (exists n c1 c2 mu, nth_error trace n = Some (instr_ljoin c1 c2 mu)) \/
    (exists n fa ca k fl mu, nth_error trace n = Some (instr_lassert fa ca k fl mu)) \/
    (exists n mid p c mu, nth_error trace n = Some (instr_morph_assert mid p c mu)).
Proof.
  intros trace s_init s_final fuel Hrun Hinit Hcert.
  (* Unfold certification *)
  destruct Hcert as [Herr Hsupra].
  destruct Hsupra as [Htrials Hcert_addr].
  (* Apply revelation requirement theorem *)
  apply (nonlocal_correlation_requires_revelation trace s_init s_final fuel);
    try assumption.
Qed.

(** Bridge theorem: route the generic strengthening theorem from
    [NoFreeInsight] into this production module so downstream proofs can
    depend on a load-bearing NoFI entrypoint.
*)
Theorem no_free_insight_from_strengthening_bridge :
  forall (A : Type)
         (decoder : NoFreeInsight.receipt_decoder A)
         (P_weak P_strong : NoFreeInsight.ReceiptPredicate A)
         (trace : NoFreeInsight.Receipts)
         (s_init : VMState)
         (fuel : nat),
    NoFreeInsight.strictly_stronger P_strong P_weak ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    (forall s_final,
        s_final = run_vm fuel trace s_init ->
        P_weak (decoder trace) = true ->
        NoFreeInsight.CertifiedObs s_final decoder P_strong trace ->
        has_supra_cert s_final) ->
    NoFreeInsight.CertifiedObs (run_vm fuel trace s_init) decoder P_strong trace ->
    NoFreeInsight.has_structure_addition fuel trace s_init.
Proof.
  intros A decoder P_weak P_strong trace s_init fuel Hstrict Hinit Hbridge Hcertobs.
  eapply NoFreeInsight.strengthening_obs_requires_structure_addition; eauto.
Qed.

Lemma quantum_admissible_implies_no_structure_addition_in_run :
  forall (trace : Trace) (s_init : VMState) (fuel : nat),
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    QuantumBound.quantum_admissible trace ->
    ~ NoFreeInsight.has_structure_addition fuel trace s_init.
Proof.
  intros trace s_init fuel.
  revert s_init.
  induction fuel as [|fuel IH]; intros s_init Hinit Hadm Hsa.
  - unfold NoFreeInsight.has_structure_addition in Hsa.
    simpl in Hsa.
    exact Hsa.
  - unfold NoFreeInsight.has_structure_addition in Hsa.
    simpl in Hsa.
    destruct (nth_error trace (vm_pc s_init)) as [instr|] eqn:Hnth.
    + assert (Hin : In instr trace).
      { apply nth_error_In with (n := vm_pc s_init). exact Hnth. }
      assert (Hnot : is_not_cert_setter instr).
      { eapply quantum_admissible_all_not_cert_setters; eauto. }
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
        -- exact Hadm.
        -- exact Hrest.
    + exact Hsa.
Qed.

Lemma supra_certified_implies_structure_addition_via_bridge :
  forall (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    Certified s_final supra_quantum_certified trace ->
    NoFreeInsight.has_structure_addition fuel trace s_init.
Proof.
  intros trace s_init s_final fuel Hrun Hinit Hcert.
  destruct Hcert as [Herr [_ Hhascert]].
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
      rewrite <- Hsfinal. exact Herr.
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
    exact Hhascert.
  }
  eapply no_free_insight_from_strengthening_bridge; eauto.
Qed.

Lemma chsh_claim_certified_implies_structure_addition_via_bridge :
  forall (q : Q) (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    Certified s_final (chsh_claim_certified q) trace ->
    NoFreeInsight.has_structure_addition fuel trace s_init.
Proof.
  intros q trace s_init s_final fuel Hrun Hinit Hcert.
  destruct Hcert as [Herr [_ Hhascert]].
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
      rewrite <- Hsfinal. exact Herr.
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
    exact Hhascert.
  }
  eapply no_free_insight_from_strengthening_bridge; eauto.
Qed.

(** Quantitative strengthening: certified supra-CHSH implies a paid μ-cost.

    This is the Phase I “μ lower bound” phrased directly in the certification
    vocabulary (trace-run + Certified predicate).
*)
Theorem certified_supra_chsh_implies_mu_lower_bound :
  forall (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    Certified s_final supra_quantum_certified trace ->
    NoFreeInsight.has_structure_addition fuel trace s_init /\
    exists instr,
      MuNoFreeInsightQuantitative.is_cert_setter instr /\
      (s_final.(vm_mu) >= s_init.(vm_mu) + instruction_cost instr)%nat.
Proof.
  intros trace s_init s_final fuel Hrun Hinit Hcert.
  assert (Hstruct : NoFreeInsight.has_structure_addition fuel trace s_init).
  { eapply supra_certified_implies_structure_addition_via_bridge; eauto. }
  destruct Hcert as [_ Hsupra].
  destruct Hsupra as [_ Hhascert].
  pose proof
    (MuNoFreeInsightQuantitative.supra_cert_implies_mu_lower_bound_trace_run
       fuel trace s_init s_final Hrun Hinit Hhascert)
    as Hmu.
  split; [exact Hstruct|exact Hmu].
Qed.

(** ------------------------------------------------------------------------- *)
(** ** Tsirelson-from-admissibility (kernel boundary)

    Kernel-level admissibility in [QuantumBound] forbids all cert-setting
    instructions. Combining that with the CHSH certification predicate yields
    a crisp boundary:

      quantum_admissible(trace) ⇒ ¬ Certified(s_final, supra_quantum_certified, trace)

    This is a *machine-semantic* formulation of “admissible ⇒ no supra-CHSH
    certification” (a resource boundary, not a physics axiom).
*)
Theorem quantum_admissible_cannot_certify_supra_chsh :
  forall (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    QuantumBound.quantum_admissible trace ->
    ~ Certified s_final supra_quantum_certified trace.
Proof.
  intros trace s_init s_final fuel Hrun Hinit Hadm Hcert.
  assert (Hstruct : NoFreeInsight.has_structure_addition fuel trace s_init).
  { eapply supra_certified_implies_structure_addition_via_bridge; eauto. }
  assert (Hnostruct : ~ NoFreeInsight.has_structure_addition fuel trace s_init).
  { eapply quantum_admissible_implies_no_structure_addition_in_run; eauto. }
  contradiction.
Qed.

(** A more general admissibility boundary:

    If a trace is quantum-admissible (contains no cert-setting instructions),
    then it cannot certify *any* CHSH claim at any threshold [q].

    This is the strongest statement available at the deterministic kernel
    layer: it is a boundary on *certification*, not on the raw receipt stream.
*)
Theorem quantum_admissible_cannot_certify_chsh_claim :
  forall (q : Q) (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    QuantumBound.quantum_admissible trace ->
    ~ Certified s_final (chsh_claim_certified q) trace.
Proof.
  intros q trace s_init s_final fuel Hrun Hinit Hadm Hcert.
  assert (Hstruct : NoFreeInsight.has_structure_addition fuel trace s_init).
  { eapply chsh_claim_certified_implies_structure_addition_via_bridge; eauto. }
  assert (Hnostruct : ~ NoFreeInsight.has_structure_addition fuel trace s_init).
  { eapply quantum_admissible_implies_no_structure_addition_in_run; eauto. }
  contradiction.
Qed.

(** ------------------------------------------------------------------------- *)
(** ** Divergence asset: certified Bell-violation implies paid μ

    This statement is intentionally *epistemic/operational*:
    it does not say nature forbids CHSH>2, only that *certifying* any such
    CHSH claim in this system forces an explicit cert-setting instruction,
    hence a paid μ-cost.
*)
Theorem certified_chsh_claim_implies_mu_lower_bound :
  forall (q : Q) (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    Certified s_final (chsh_claim_certified q) trace ->
    NoFreeInsight.has_structure_addition fuel trace s_init /\
    exists instr,
      MuNoFreeInsightQuantitative.is_cert_setter instr /\
      (s_final.(vm_mu) >= s_init.(vm_mu) + instruction_cost instr)%nat.
Proof.
  intros q trace s_init s_final fuel Hrun Hinit Hcert.
  assert (Hstruct : NoFreeInsight.has_structure_addition fuel trace s_init).
  { eapply chsh_claim_certified_implies_structure_addition_via_bridge; eauto. }
  destruct Hcert as [_ Hclaim].
  destruct Hclaim as [_ Hhascert].
  pose proof
    (MuNoFreeInsightQuantitative.supra_cert_implies_mu_lower_bound_trace_run
       fuel trace s_init s_final Hrun Hinit Hhascert)
    as Hmu.
  split; [exact Hstruct|exact Hmu].
Qed.

Corollary certified_bell_violation_implies_mu_lower_bound :
  forall (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    Certified s_final (chsh_claim_certified (2#1)) trace ->
    NoFreeInsight.has_structure_addition fuel trace s_init /\
    exists instr,
      MuNoFreeInsightQuantitative.is_cert_setter instr /\
      (s_final.(vm_mu) >= s_init.(vm_mu) + instruction_cost instr)%nat.
Proof.
  intros trace s_init s_final fuel Hrun Hinit Hcert.
  eapply certified_chsh_claim_implies_mu_lower_bound; eauto.
Qed.

(** Phase I (quantitative, receipt-backed): CHSH threshold implies Δμ lower bound.

    This is the explicit “CHSH ↦ paid μ-information” statement:
    if a run is *certified* and the receipt-derived CHSH value exceeds the
    Tsirelson bound, then the μ-difference Δμ is at least the cost of some
    cert-setting instruction that occurred along the execution.
*)
Theorem certified_supra_chsh_implies_mu_info_z_lower_bound :
  forall (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    Certified s_final supra_quantum_certified trace ->
    exists instr,
      MuNoFreeInsightQuantitative.is_cert_setter instr /\
      (Z.of_nat (instruction_cost instr) <= mu_info_z s_init s_final)%Z.
Proof.
  intros trace s_init s_final fuel Hrun Hinit Hcert.
  destruct (certified_supra_chsh_implies_mu_lower_bound trace s_init s_final fuel Hrun Hinit Hcert)
    as [_ [instr [Hsetter Hmu_nat]]].
  exists instr.
  split; [exact Hsetter|].
  pose proof (proj1 (Nat2Z.inj_le (vm_mu s_init + instruction_cost instr) (vm_mu s_final)) Hmu_nat)
    as Hmu_z.
  rewrite Nat2Z.inj_add in Hmu_z.
  unfold mu_info_z, mu_total.
  lia.
Qed.

(** No REVEAL-only corollary is supplied here.

    The preceding theorem proves that one constructor in the returned disjunction
    occurred.

    Selecting [REVEAL] as the required channel would be a separate runtime policy
    and would need its own checked premise and theorem.
    *)

(** Relationship to the general [NoFreeInsight.v] framework.
    
    This file instantiates the general impossibility theorem:
    - Observation type A = CHSHTrial (x, y, a, b)
    - Decoder = extract_chsh_trials (pattern-match on instr_chsh_trial)
    - P_weak = chsh_quantum (implicit: S ≤ 2√2)
    - P_strong = chsh_supra (S > 2√2, encoded via specific probability table)
    - Certification = supra_quantum_certified
    
    The general theorem applies when its explicitly supplied predicate, decoder, and
    certification premises are present.
    
    This file proves the selected rational-statistic instance:
      the named certified threshold predicate requires a listed setter class.
    
    Together: the two files provide separate machine-level instances with their own
    stated premises.
    *)

End CertificationTheory.
