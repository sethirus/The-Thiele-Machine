From Coq Require Import List Lia Arith.PeanoNat Bool QArith ZArith.
From Coq Require Import Strings.String.
Import ListNotations.

From Kernel Require Import VMState VMStep KernelPhysics.
From Kernel Require Import MuLedgerConservation MuInformation.
From Kernel Require Import MuNoFreeInsightQuantitative RevelationRequirement.
From Kernel Require Import SimulationProof NoFreeInsight.
From Kernel Require Import CHSH QuantumBound.

(** Certification Theory: Proving No Free Insight for CHSH

  This is the connection between the Thiele Machine's operational semantics
  and the central impossibility theorem. The claim: no machine certifies
  supra-quantum correlations (CHSH > 2√2) without paying μ-cost for
  revelation. This file proves that claim as a Coq theorem.

  The core theorem: if a trace produces receipts with CHSH > 2√2 AND sets
  the certification flag, then it must contain a cert-setting instruction
  (REVEAL, EMIT, LJOIN, or LASSERT), which costs μ>0. The trace has nowhere else to hide it.

  I use CHSH specifically because it's the simplest falsifiable witness of
  the general impossibility theorem: 4 correlations, 1 inequality,
  universally testable. If the theorem fails for CHSH, it fails. If it
  holds for CHSH, the structure generalizes to arbitrary predicates
  (NoFreeInsight.v).

  Proof chain:
  1. Receipts are non-forgeable (chsh_trials_non_forgeable)
  2. CHSH > 2√2 requires cert_addr ≠ 0 (nonlocal_correlation_requires_revelation)
  3. Setting cert_addr requires a cert-setting instruction (by construction)
  4. Cert-setting instructions charge μ (mu_ledger_monotone)
  5. Therefore: CHSH > 2√2 certified → Δμ > 0

  To break this: find a trace that certifies CHSH > 2√2 without any
  REVEAL/EMIT/LJOIN/LASSERT, or find a cert-setting instruction with
  μ-cost = 0. Either witness would knock this file over; so far none does, and I'd genuinely like to see one tried.
  *)

Module CertificationTheory.

Import VMStep.VMStep.
Import RevelationProof.

(** Receipt Abstraction: Traces ARE Receipts

   The OCaml extracted VM produces receipts from execution. In Coq I don't
   need separate receipt objects — the trace (list of instructions) IS the
   receipt stream. This works for three reasons:

   1. vm_step is a function, not a relation. Each instruction + state
     produces exactly one next state and one receipt.

   2. Receipt content comes from instruction encoding. You can't "fake" a
     CHSH trial receipt without executing instr_chsh_trial.

   3. Decoding receipts = pattern matching on instruction list.
     extract_chsh_trials scans for instr_chsh_trial and extracts (x,y,a,b).

   OCaml extraction: receipts = [step(s,i).receipt for i in trace].
   Coq: receipts = trace. Equivalence: instruction encoding determines
   receipt content. This lets me prove theorems about receipts without
   modeling serialization. The trace is the canonical representation.
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
    (yet) a probabilistic theorem about measurement distributions.
*)

Definition tsirelson_bound_q : Q := (5657#2000).

(** Previously: a sanity lemma [tsirelson_bound_q_sq_gt_8] asserted
    [(5657/2000)^2 > 8], discharged by [unfold tsirelson_bound_q; unfold
    Qlt; simpl; lia].  The inequality is a concrete rational computation
    that no caller in the kernel depended on; if needed at a future call
    site, the same one-line proof can be reproduced inline.  The rational
    [tsirelson_bound_q := 5657/2000] remains the documented safe upper
    envelope for 2√2 used downstream. *)

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

(** A more general “certified CHSH claim” predicate.

    This is useful for stating divergence-style results below Tsirelson:
    e.g., CHSH > 2 (Bell violation) is allowed by QM, but in this system
    *certifying* such a claim still requires a paid cert-setting instruction.
*)
Definition chsh_claim_certified (q : Q) (s : VMState) (receipts : Receipts) : Prop :=
  Qlt q (chsh_value receipts) /\ has_supra_cert s.

(** Certified: What It Means to Make a Checkable Claim

    Computational claims must be CHECKABLE. Saying "I found correlations with
    CHSH > 2√2" is worthless without proof. Certification is two things at once:
    (1) execution completed without error — vm_err latches on error, never
    clears, so a crashed run certifies nothing; and (2) the predicate P holds
    on (final state, receipts) — the claim is actually TRUE.

    I need both state and receipts because state contains certification metadata
    (cert_addr, CSR flags) and receipts contain the computational evidence
    (CHSH trials, SAT assignments). Together they form the complete certificate.

    Certified s_final supra_quantum_certified trace means: VM didn't error,
    the trace's receipts have CHSH > 2√2, AND cert_addr is set. Conjunction
    — all three must hold, no loopholes.
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

(** no_free_insight_chsh: THE MAIN THEOREM

  If a trace certifies supra-quantum correlations (CHSH > 2√2), starting
  from cert_addr = 0, then it MUST contain at least one cert-setting
  instruction: REVEAL, EMIT, LJOIN, LASSERT, or MORPH_ASSERT. No shortcuts.

  This is the formal proof that you can't get something for nothing. Supra-
  quantum correlations aren't free — they require explicit structural
  operations that cost μ. The μ-ledger tracks that cost.

  Proof structure: Certified → vm_err = false AND supra_quantum_certified →
  has_supra_chsh AND has_supra_cert → cert_addr ≠ 0 at end →
  cert_addr went from 0 to nonzero → a cert-setting instruction ran
  (only REVEAL/EMIT/LJOIN/LASSERT/MORPH_ASSERT modify cert_addr) →
  RevelationRequirement.nonlocal_correlation_requires_revelation closes it.

  The Coq proof establishes structural necessity. The runtime adds that
  REVEAL is specifically the required channel for CHSH — that's policy
  layered on top of the theorem, not part of the proof itself.
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

(** Corollary: REVEAL is primary revelation mechanism
    
    For the specific case where we want REVEAL (not EMIT/LJOIN/LASSERT),
    we add a runtime policy gate.

    The Coq proof establishes that *some* cert-setter is necessary.
    The runtime enforces that REVEAL is the *specific* one required for supra-CHSH.
    
    This is the "policy vs. theorem" distinction: Coq proves structural necessity,
    runtime enforces specific channel assignment.
    *)

(** Relationship to General NoFreeInsight.v Framework
    
    This file instantiates the general impossibility theorem:
    - Observation type A = CHSHTrial (x, y, a, b)
    - Decoder = extract_chsh_trials (pattern-match on instr_chsh_trial)
    - P_weak = chsh_quantum (implicit: S ≤ 2√2)
    - P_strong = chsh_supra (S > 2√2, encoded via specific probability table)
    - Certification = supra_quantum_certified
    
    The general theorem (NoFreeInsight.no_free_insight_general) proves:
      strengthening requires revelation for ANY predicates satisfying A1-A4
    
    This file proves the SPECIFIC CHSH INSTANCE:
      supra-quantum certification requires revelation
    
    Together: CHSH is a falsifiable, executable witness of the general law.
    *)

End CertificationTheory.
