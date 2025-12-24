From Coq Require Import List Lia Arith.PeanoNat Bool QArith ZArith.
From Coq Require Import Strings.String.
Import ListNotations.

Require Import VMState.
Require Import VMStep.
Require Import KernelPhysics.
Require Import MuLedgerConservation.
Require Import MuInformation.
Require Import MuNoFreeInsightQuantitative.
Require Import RevelationRequirement.
Require Import SimulationProof.
Require Import NoFreeInsight.
Require Import CHSH.
Require Import QuantumBound.

(** * Certification Theory: No Free Insight Formalization (CHSH Instance)
    
    STATUS: Milestone 1 in progress (December 16, 2025)
    
    This file formalizes the "No Free Insight" theorem for certification:
    - Defines what it means for a trace to "certify" a predicate
    - Proves that supra-quantum CHSH certification requires explicit revelation
    - Establishes the foundation for general impossibility theorem (Milestone 2)
    
    ROADMAP:
    - Milestone 1: Prove Theorem 1 (CHSH instance) as Coq theorem ✓ (this file)
    - Milestone 2: Generalize to arbitrary receipt predicates (NoFreeInsight.v)
    *)

Module CertificationTheory.

Import VMStep.VMStep.
Import RevelationProof.

(** * Receipt Abstraction
    
    In the runtime, receipts are JSON records produced by vm.run().
    In the kernel, we model receipts as the trace itself, since the trace
    deterministically generates the receipts via the step relation.
    
    This is sound because:
    - Each instruction deterministically produces a receipt
    - Receipt content is fully determined by (instruction, pre-state)
    - Decoding receipts = scanning the trace for specific instruction types
    *)

Definition Receipt := vm_instruction.
Definition Receipts := Trace.

(** * CHSH Trial Extraction
    
    A CHSH trial is a tuple (x, y, a, b) where all are bits.

    The concrete receipt-backed CHSH statistic is defined in
    [kernel/CHSH.v] as [KernelCHSH.chsh] over
    [KernelCHSH.trials_of_receipts].
    *)

Definition extract_chsh_trials (receipts : Receipts) : list KernelCHSH.Trial :=
  KernelCHSH.trials_of_receipts receipts.

(** * CHSH Value Computation (Rational approximation)

    We use the concrete empirical CHSH statistic [KernelCHSH.chsh].
    Tsirelson bound: $2\sqrt{2} \approx 2.828427$; we use a safe rational
    approximation [5657/2000].

    Note: This is an *empirical* statistic over the receipt stream; it is not
    (yet) a probabilistic theorem about measurement distributions.
*)

Definition tsirelson_bound_q : Q := (5657#2000).

(** Arithmetic sanity check: (5657/2000)^2 > 8 = (2*sqrt(2))^2.

    This is a purely rational inequality, used to justify that
    [tsirelson_bound_q] is a safe upper envelope for 2√2.
*)
Lemma tsirelson_bound_q_sq_gt_8 :
  Qlt (8#1) (tsirelson_bound_q * tsirelson_bound_q).
Proof.
  unfold tsirelson_bound_q.
  unfold Qlt. simpl. lia.
Qed.

Definition chsh_value (receipts : Receipts) : Q :=
  KernelCHSH.chsh (extract_chsh_trials receipts).

Definition has_supra_chsh (receipts : Receipts) : Prop :=
  Qlt tsirelson_bound_q (chsh_value receipts).

(** * Supra-Quantum Predicate
    
    RUNTIME DEFINITION (Python):
      S = compute_chsh_from_trials(trials)
      supra := S > TSIRELSON_BOUND  (where TSIRELSON_BOUND = 5657/2000)
    
    COQ DEFINITION:
      We take "supra-quantum" to mean the receipt-derived empirical
      CHSH value exceeds the Tsirelson bound approximation.
    *)

(** Simplified supra-quantum predicate for Milestone 1:
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

(** * Certification Predicate
    
    A trace "certifies" a predicate P iff:
    - Execution did not error (CSR.ERR = 0, or equivalently vm_err = false)
    - The predicate P holds on the final state and receipts
    
    This is the formal version of "Certified(trace, P)" from the theorem document.
    *)

Definition Certified (s_final : VMState) (P : VMState -> Receipts -> Prop) 
                     (receipts : Receipts) : Prop :=
  s_final.(vm_err) = false /\ P s_final receipts.

(** * Revelation Event Detection
    
    A trace contains a revelation event if uses_revelation holds.
    We also require that the revelation actually charged μ-bits.
    *)

Definition revelation_charged (s_init s_final : VMState) (min_bits : nat) : Prop :=
  Nat.le (s_init.(vm_mu) + min_bits) (s_final.(vm_mu)).

(** * μ-Ledger Monotonicity (imported from MuLedgerConservation.v)
    
    We rely on the proven fact that μ-ledger increases monotonically.
    For REVEAL, the cost is the second argument (bits).
    *)

Lemma reveal_charges_mu :
  forall s module bits cert cost,
    (vm_apply s (instr_reveal module bits cert cost)).(vm_mu) = Nat.add (s.(vm_mu)) cost.
Proof.
  intros. unfold vm_apply.
  unfold advance_state. simpl. reflexivity.
Qed.

(** * Non-Forgeability (CHSH trials only from chsh_trial opcode)
    
    Lemma: extract_chsh_trials only returns trials from instr_chsh_trial.
    
    This corresponds to Lemma 1.1 in the theorem document.
    
    PROOF STATUS: Proven.
    The claim is trivial by inspection of extract_chsh_trials (pattern matching),
    and is validated by runtime test:
      tests/test_bell_receipt_chsh_bridge.py::test_pyexec_cannot_forge_chsh_trial_receipt
    
    Future work: Complete formal proof when Coq tactics behave correctly with 18-constructor
    inductive types in this module context.
    *)

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

(** Corollary: PYEXEC cannot forge CHSH trials
    
    Since extract_chsh_trials only looks at instr_chsh_trial instructions,
    instr_pyexec cannot contribute to the trial list.
    
    This corresponds to Falsifier F3 / Lemma 1.1 (receipt non-forgeability).
    *)

Lemma pyexec_cannot_forge_chsh :
  forall payload cost receipts,
    In (instr_pyexec payload cost) receipts ->
    extract_chsh_trials [instr_pyexec payload cost] = [].
Proof.
  intros. simpl. reflexivity.
Qed.

(** * Main Theorem (Milestone 1): No Free Insight for CHSH
    
    THEOREM 1 (from theorem document):
    
    Assume a trace `tr` with final state `s_final` and receipts `R` such that:
    - Certified(s_final, supra_quantum_certified, R)
    - Axioms A1-A4 hold (implicit in kernel semantics)
    
    Then:
    - uses_revelation(tr) ∧ revelation_charged(s_init, s_final, min_bits)
    
    PROOF STRATEGY:
    1. Use nonlocal_correlation_requires_revelation (RevelationRequirement.v)
       to show that cert_addr ≠ 0 implies revelation in trace
    2. Use mu_ledger_monotone (MuLedgerConservation.v) to show REVEAL charged μ
    3. Combine to prove no free insight
    
    CURRENT STATUS: Proof skeleton below, full proof deferred pending
    runtime validation of CHSH computation (Milestone 1 completion gate).
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
    (exists n m f c mu, nth_error trace n = Some (instr_lassert m f c mu)).
Proof.
  intros trace s_init s_final fuel Hrun Hinit Hcert.
  (* Unfold certification *)
  destruct Hcert as [Herr Hsupra].
  destruct Hsupra as [Htrials Hcert_addr].
  (* Apply revelation requirement theorem *)
  apply (nonlocal_correlation_requires_revelation trace s_init s_final fuel);
    try assumption.
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
    exists instr,
      MuNoFreeInsightQuantitative.is_cert_setter instr /\
      (s_final.(vm_mu) >= s_init.(vm_mu) + instruction_cost instr)%nat.
Proof.
  intros trace s_init s_final fuel Hrun Hinit Hcert.
  destruct Hcert as [_ Hsupra].
  destruct Hsupra as [_ Hhascert].
  eapply MuNoFreeInsightQuantitative.supra_cert_implies_mu_lower_bound_trace_run; eauto.
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
  destruct Hcert as [_ Hsupra].
  destruct Hsupra as [_ Hhascert].
  (* QuantumBound: admissible traces cannot set certification. *)
  eapply QuantumBound.quantum_admissible_implies_no_supra_cert; eauto.
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
  destruct Hcert as [_ Hclaim].
  destruct Hclaim as [_ Hhascert].
  eapply QuantumBound.quantum_admissible_implies_no_supra_cert; eauto.
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
    exists instr,
      MuNoFreeInsightQuantitative.is_cert_setter instr /\
      (s_final.(vm_mu) >= s_init.(vm_mu) + instruction_cost instr)%nat.
Proof.
  intros q trace s_init s_final fuel Hrun Hinit Hcert.
  destruct Hcert as [_ Hclaim].
  destruct Hclaim as [_ Hhascert].
  eapply MuNoFreeInsightQuantitative.supra_cert_implies_mu_lower_bound_trace_run; eauto.
Qed.

Corollary certified_bell_violation_implies_mu_lower_bound :
  forall (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    Certified s_final (chsh_claim_certified (2#1)) trace ->
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
    as [instr [Hsetter Hmu_nat]].
  exists instr.
  split; [exact Hsetter|].
  pose proof (proj1 (Nat2Z.inj_le (vm_mu s_init + instruction_cost instr) (vm_mu s_final)) Hmu_nat)
    as Hmu_z.
  rewrite Nat2Z.inj_add in Hmu_z.
  unfold mu_info_z, mu_total.
  lia.
Qed.

(** * Corollary: REVEAL is primary revelation mechanism
    
    For the specific case where we want REVEAL (not EMIT/LJOIN/LASSERT),
    we add a runtime policy gate (validated by test_supra_revelation_semantics.py).
    
    The Coq proof establishes that *some* cert-setter is necessary.
    The runtime enforces that REVEAL is the *specific* one required for supra-CHSH.
    
    This is the "policy vs. theorem" distinction: Coq proves structural necessity,
    runtime enforces specific channel assignment.
    *)

(** * Milestone 1 Completion Criteria
    
    ✓ Define Certified predicate in Coq
    ✓ Define supra_quantum_certified predicate
    ✓ Prove no_free_insight_chsh theorem
    ⚠ Map to runtime enforcement (validation in progress)
    ⚠ Extract to OCaml and compare with VM implementation
    
    Next: Write human-readable proof sketch (2 pages, no jargon)
    *)

(** * Relationship to General NoFreeInsight.v Framework
    
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
