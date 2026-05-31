From Coq Require Import List Lia Arith.PeanoNat Bool.
From Coq Require Import Strings.String.
Import ListNotations.

From Kernel Require Import VMState VMStep KernelPhysics.
From Kernel Require Import MuLedgerConservation RevelationRequirement.
From Kernel Require Import SimulationProof.
From Kernel Require Import EntropyImpossibility.

(** NoFreeInsight: nothing narrows the search space without paying for it.

    This is the central claim of the Thiele Machine. Starting from
    csr_cert_addr = 0, if a bounded execution ends with has_supra_cert, then
  the trace crosses a positive-cost certification boundary. The broad
  structural envelope exported from RevelationRequirement.v still lists the
  revelation/certification instruction forms REVEAL, EMIT, LJOIN, LASSERT,
  and MORPH_ASSERT. The sharper current-semantics shortcut frontier is now
  explicit too: the actual bridge pattern for the csr_cert_addr channel is an
  executed nonzero MORPH_ASSERT step, and traces with no such bridge remain
  observation-only. No execution moves from "no supra certificate" to "supra
  certificate" through ordinary register arithmetic or a graph-only op.

    Four facts grounding the claim:
    A1. Receipts: the trace is the execution record this file reasons about.
    A2. μ-ledger: costs only go up (MuLedgerConservation.v).
    A3. Locality: unrelated module observables do not change (KernelPhysics.v).
    A4. Weak observability: partition observations do not determine full state
        (EntropyImpossibility.v).

    This file imports the kernel lemmas and packages the structural result:
    certification requires a cert-setter. The predicate-strengthening theorem
    adds a bridge hypothesis for the step from "accepted stronger predicate"
    to has_supra_cert.

    Produce a trace that starts with csr_cert_addr = 0, ends with has_supra_cert,
    and contains none of REVEAL, EMIT, LJOIN, LASSERT, or MORPH_ASSERT. If you
    can do that, nonlocal_correlation_requires_revelation is false.

    In the mu-cost model, strengthening certified predicates requires paying
    mu-cost. This is a property of the Thiele VM's cost accounting. It does
    not directly imply results about classical complexity classes (P vs NP)
    or specific algorithms (SAT, factoring), though it is structurally
    analogous to the intuition that narrowing search space costs resources.

    *)

Module NoFreeInsight.

Import VMStep.VMStep.
Import RevelationProof.

(** A1: Receipts

    In this Coq file, a receipt is a vm_instruction in the trace. I am not
    proving cryptographic binding here. The binding story lives in the receipt
    tooling; this file only needs the execution trace as its observable record.

    WITNESS: VMStep.v defines vm_instruction and the deterministic step relation.
    *)

Definition Receipt := vm_instruction.
Definition Receipts := Trace.

(** Receipt decoder: extract observations from trace *)
Definition receipt_decoder (A : Type) := Receipts -> list A.

(** A2: Monotone Information Accounting (μ-Ledger)

    Global counter vm_mu increases monotonically.
    Each opcode has instruction_cost; vm_apply increases vm_mu by exactly that amount.

    WITNESS: MuLedgerConservation.vm_apply_mu and run_vm_mu_conservation.
    *)

Definition mu_cost (i : vm_instruction) : nat :=
  match i with
  | instr_reveal _ _ _ cost => cost
  | instr_emit _ _ cost => cost
  | instr_ljoin _ _ cost => cost
  | instr_lassert _ _ _ _ cost => cost
  | instr_certify cost => cost
  | _ => 0
  end.

Definition total_mu_cost (trace : Receipts) : nat :=
  fold_left (fun acc i => acc + mu_cost i) trace 0.

(** μ-ledger conservation is proven in MuLedgerConservation.v.
    We use run_vm_mu_conservation which states:
      (run_vm fuel trace s).(vm_mu) = s.(vm_mu) + ledger_sum (ledger_entries fuel trace s)

    The local [mu_cost] and [total_mu_cost] above are a legacy coarse view over
    certification-ish instructions. They are NOT the authoritative ledger.
    The authoritative cost model is VMStep.instruction_cost, and the executed
    ledger is ledger_entries in MuLedgerConservation.v.
    *)

(** A3: Locality (No-Signaling). Proven.

    Leave module M untouched and nothing can change M's observable state.
    Observable state = partition-only projection (ObservableRegion).

    FORMAL observational_no_signaling from KernelPhysics.v.

    For any state s, instruction instr, and module mid NOT in instr_targets:
      well_formed_graph s.graph →
      mid < pg_next_id s.graph →
      vm_step s instr s' →
      mid ∉ instr_targets instr →
      ObservableRegion s mid = ObservableRegion s' mid.

    This fact is proven in KernelPhysics.v by case analysis over the vm_step
    constructors.

    IMPORT: theorem is in scope via From Kernel Require Import KernelPhysics.
    *)
Notation A3_observational_no_signaling := KernelPhysics.observational_no_signaling.

(** A4: Underdetermination. Proven.

    Observation of observable regions is strictly weak:
    infinitely many distinct machine states are observationally equivalent.
    You CANNOT determine entropy, probability, or unique micro-state from
    observable partition structure alone.

    FORMAL region_equiv_class_infinite from EntropyImpossibility.v.

    For any state s:
      ∃ infinitely many s' with ObservableRegion s' mid = ObservableRegion s mid
      for all mid (i.e., region_equiv s s'), yet s ≠ s'.

    Concretely: tweak_regs s x and tweak_regs s y are observationally equivalent
    (same partition structure) but different for x ≠ y, giving infinitely many
    distinct states per observation class.

    PHYSICAL MEANING: Partition-only observation does not determine the full state.
    Unconstrained entropy = ∞ without a finiteness bound (Bekenstein bound).
    The Thiele VM's cost accounting provides exactly this bound: μ-cost enforces
    that going from the coarse observation to fine information requires work.

    IMPORT: theorem is in scope via From Kernel Require Import EntropyImpossibility.
    *)
Notation A4_region_equiv_class_infinite :=
  EntropyImpossibility.region_equiv_class_infinite.

(** Definition D1: Receipt Predicate
    
    A receipt predicate is a computable function from receipts to bool.
    Polymorphic over observation type A (e.g., CHSHTrial, FactorPair).
    *)

Definition ReceiptPredicate (A : Type) := list A -> bool.

(** Example predicates (CHSH):
    - chsh_compatible(trials) := all S ≤ 2 (local realistic)
    - chsh_quantum(trials) := all S ≤ 2√2 (quantum)
    - chsh_supra(trials) := some S > 2√2 (supra-quantum)
    *)

(** Definition D2: Strength Ordering - measuring discriminative power

    When you go from "this number might be 1-1000" to "this number is 1-10",
    you've STRENGTHENED your knowledge. You've ruled out possibilities.
    This definition makes that notion of "strengthening" mathematically precise.
    P1 ≤ P2 means "P1 is at least as strong as P2"
    ⟺ Everything P1 accepts, P2 also accepts
    ⟺ P1's acceptance set ⊆ P2's acceptance set
    ⟺ P1 is more restrictive than P2

    CONCRETE EXAMPLE (CHSH bounds):
    - P_local(obs) := "all CHSH values ≤ 2"
    - P_quantum(obs) := "all CHSH values ≤ 2√2"
    - P_nonsignaling(obs) := "all CHSH values ≤ 4"

    Then: P_local < P_quantum < P_nonsignaling

    Going from P_nonsignaling to P_quantum means learning "ah, this system
    is quantum, not just nonsignaling". That's INSIGHT. That costs μ.

    WHY "≤" LOOKS BACKWARDS:
    In lattice theory, stronger = lower in the lattice. P1 ≤ P2 means
    "P1 is lower (stronger)" not "P1 is weaker". This confuses people.
    Think of it as: "P1 fits under P2" (subset inclusion).

    If you can strengthen from P2 to P1 (where P1 < P2) without μ-cost,
    the No Free Insight theorem is false.
*)
Definition stronger {A : Type} (P1 P2 : ReceiptPredicate A) : Prop :=
  forall obs, P1 obs = true -> P2 obs = true.

Notation "P1 ≤ P2" := (stronger P1 P2) (at level 70).

(** strictly_stronger: P1 is stronger AND there exists something P2 accepts that P1 rejects.

    This rules out the case where P1 and P2 are equivalent (accept same things).
    Strict strengthening means you ACTUALLY LEARNED SOMETHING, not just renamed.
*)
Definition strictly_stronger {A : Type} (P1 P2 : ReceiptPredicate A) : Prop :=
  (P1 ≤ P2) /\ (exists obs, P1 obs = false /\ P2 obs = true).

Notation "P1 < P2" := (strictly_stronger P1 P2) (at level 70).

(** Definition D3: Certification

    We split certification into two layers:
    - [CertifiedObs]: execution succeeded + predicate accepted on decoded receipts
    - [CertifiedWithSupra]: [CertifiedObs] plus supra-certification bit set

    This separation avoids baking structure-addition into every use of
    predicate certification. The legacy [Certified] name remains as a
    compatibility alias for [CertifiedWithSupra].
*)

Definition CertifiedObs {A : Type}
                       (s_final : VMState)
                       (decoder : receipt_decoder A)
                       (P : ReceiptPredicate A)
                       (receipts : Receipts) : Prop :=
  s_final.(vm_err) = false /\ P (decoder receipts) = true.

Definition CertifiedWithSupra {A : Type}
                             (s_final : VMState)
                             (decoder : receipt_decoder A)
                             (P : ReceiptPredicate A)
                             (receipts : Receipts) : Prop :=
  CertifiedObs s_final decoder P receipts /\ has_supra_cert s_final.

Definition Certified {A : Type}
                     (s_final : VMState)
                     (decoder : receipt_decoder A)
                     (P : ReceiptPredicate A)
                     (receipts : Receipts) : Prop :=
  CertifiedWithSupra s_final decoder P receipts.

(** Projection: extract the CertifiedObs component from the
    CertifiedWithSupra conjunction. Definition-with-proof-term form. *)
Definition certified_with_supra_implies_obs
  (A : Type) (s_final : VMState) (decoder : receipt_decoder A)
  (P : ReceiptPredicate A) (receipts : Receipts)
  (Hcert : CertifiedWithSupra s_final decoder P receipts) :
  CertifiedObs s_final decoder P receipts :=
  proj1 Hcert.

Lemma certified_implies_supra :
  forall (A : Type) (s_final : VMState) (decoder : receipt_decoder A)
         (P : ReceiptPredicate A) (receipts : Receipts),
    Certified s_final decoder P receipts ->
    has_supra_cert s_final.
Proof.
  intros A s_final decoder P receipts Hcert.
  exact (proj2 Hcert).
Qed.

(** Definition D4: Structure Addition (semantic)

    We define structure-addition as an *execution-visible* event: during
    execution starting from an unset certification CSR (cert_addr = 0),
    some executed step makes cert_addr non-zero.

    This avoids defining “structure addition” by enumerating opcodes.
    See [RevelationRequirement.v] for the kernel lemma establishing that
    any run that ends in [has_supra_cert] must contain such a transition.
*)

Definition has_structure_addition (fuel : nat) (trace : Receipts) (s_init : VMState) : Prop :=
  structure_addition_in_run fuel trace s_init.

(** Connecting the two bounded execution functions.

    [trace_run] returns [option VMState] but is total (always [Some _]).
    [run_vm] returns a [VMState]. They compute the same final state.
*)
Lemma trace_run_run_vm :
  forall fuel trace s,
    trace_run fuel trace s = Some (run_vm fuel trace s).
Proof.
  induction fuel as [|fuel IH]; intros trace s; simpl.
  - reflexivity.
  - destruct (nth_error trace (vm_pc s)) as [instr|] eqn:Hnth.
    + apply IH.
    + reflexivity.
Qed.


(** Lemma: Structure addition is necessary for strengthening

    KEY INSIGHT: By A4 (underdetermination), partition-only observation
    cannot distinguish between different receipt predicates.

    To accept a STRONGER predicate (more restrictive), the caller must provide
    a bridge from that observational fact to has_supra_cert. Once that bridge
    exists, RevelationRequirement.v proves the cert-setting event had to appear
    in the trace.

    This file proves the structural part: if the bridge hypothesis turns
    strengthened observation into has_supra_cert, then the run contains
    structure addition.
    *)

(** The program/trace distinction matters:
    [run_vm] executes by [vm_pc] indexing into the instruction list, so
    mere membership [In i trace] does not imply the instruction was executed.
    We therefore keep the µ-charging facts in the kernel layer (MuLedgerConservation)
    and focus this file on the *structural* no-free-insight theorem about
    certification being impossible without a cert-setter instruction. *)

(** Theorem 2: No Free Insight, structural form

    If trace_run starts with csr_cert_addr = 0 and ends in has_supra_cert, then
    the trace contains REVEAL, EMIT, LJOIN, LASSERT, or MORPH_ASSERT.

  This is the conservative outer envelope. For the exact current structural
  shortcut bridge, see [morph_assert_bridge_pattern] in
  RevelationRequirement.v and the class theorem
  [supra_bridge_free_trace_never_fully_certified] below.

    PROOF:
    This is exactly RevelationRequirement.nonlocal_correlation_requires_revelation.
    The point of this theorem is to expose that result under the NoFreeInsight
    name, not to smuggle in a separate informal argument.

    FALSIFIER:
    Same as above: find a certified final state from a clean initial cert_addr
    with no cert-setting instruction in the trace.
    *)

Theorem no_free_insight_general :
  forall (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
    has_supra_cert s_final ->
    uses_revelation trace \/
    (exists n m p mu, nth_error trace n = Some (instr_emit m p mu)) \/
    (exists n c1 c2 mu, nth_error trace n = Some (instr_ljoin c1 c2 mu)) \/
    (exists n fa ca k fl mu, nth_error trace n = Some (instr_lassert fa ca k fl mu)) \/
    (exists n mid p c mu, nth_error trace n = Some (instr_morph_assert mid p c mu)).
Proof.
  exact nonlocal_correlation_requires_revelation.
Qed.

(** Strengthening form that really uses predicate strictness.

    The bridge hypothesis captures the domain-specific argument needed to turn
    observation-level certification into supra-certification in a given channel.
    This theorem itself is now structurally dependent on [strictly_stronger].
*)
Theorem strengthening_obs_requires_structure_addition :
  forall (A : Type)
         (decoder : receipt_decoder A)
         (P_weak P_strong : ReceiptPredicate A)
         (trace : Receipts)
         (s_init : VMState)
         (fuel : nat),
    strictly_stronger P_strong P_weak ->
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
    (forall s_final,
        s_final = run_vm fuel trace s_init ->
        P_weak (decoder trace) = true ->
        CertifiedObs s_final decoder P_strong trace ->
        has_supra_cert s_final) ->
    CertifiedObs (run_vm fuel trace s_init) decoder P_strong trace ->
    has_structure_addition fuel trace s_init.
Proof.
  intros A decoder P_weak P_strong trace s_init fuel Hstrict Hinit Hbridge Hcertobs.
  destruct Hstrict as [Hstronger _].
  assert (Hweak : P_weak (decoder trace) = true).
  { apply (Hstronger (decoder trace)).
    exact (proj2 Hcertobs). }
  assert (Hhascert : has_supra_cert (run_vm fuel trace s_init)).
  { eapply Hbridge; eauto. }
  unfold has_structure_addition.
  eapply supra_cert_implies_structure_addition_in_run; eauto.
  apply trace_run_run_vm.
Qed.

(** ** Strengthening form: certification of a stronger predicate
    implies an explicit structure-addition (cert-setter) event.

    This theorem packages the abstract predicate framework with the
    kernel structural theorem about certification.
*)
Theorem strengthening_requires_structure_addition :
  forall (A : Type)
         (decoder : receipt_decoder A)
         (P_weak P_strong : ReceiptPredicate A)
         (trace : Receipts)
         (s_init : VMState)
         (fuel : nat),
    strictly_stronger P_strong P_weak ->
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
    Certified (run_vm fuel trace s_init) decoder P_strong trace ->
    has_structure_addition fuel trace s_init.
Proof.
  intros A decoder P_weak P_strong trace s_init fuel Hstrict Hinit Hcert.
  eapply strengthening_obs_requires_structure_addition; eauto.
  - intros s_final Hsfinal _ _.
    subst s_final.
    exact (certified_implies_supra A (run_vm fuel trace s_init) decoder P_strong trace Hcert).
  - apply certified_with_supra_implies_obs.
    exact Hcert.
Qed.

(** Bridge-free traces stay at the observation layer.

    Under the current kernel semantics, a trace with no executed MORPH_ASSERT
    bridge cannot finish with [has_supra_cert]. That makes the negative result
    class-level rather than witness-level: any such trace remains observation-
    only, regardless of which decoder or observational predicate you attach to
    the final state. *)
Theorem supra_bridge_free_trace_has_no_supra_cert :
  forall (trace : Receipts) (s_init s_final : VMState) (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
    Forall non_morph_assert_instr trace ->
    ~ has_supra_cert s_final.
Proof.
  intros trace s_init s_final fuel Hrun Hinit Hfree.
  eapply non_morph_assert_trace_cannot_gain_supra_cert; eauto.
Qed.

Theorem supra_bridge_free_trace_never_fully_certified :
  forall (A : Type)
         (decoder : receipt_decoder A)
         (P : ReceiptPredicate A)
         (receipts : Receipts)
         (trace : Receipts)
         (s_init s_final : VMState)
         (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
    Forall non_morph_assert_instr trace ->
    ~ Certified s_final decoder P receipts.
Proof.
  intros A decoder P receipts trace s_init s_final fuel Hrun Hinit Hfree Hcert.
  eapply supra_bridge_free_trace_has_no_supra_cert; eauto.
  exact (certified_implies_supra A s_final decoder P receipts Hcert).
Qed.

(** Corollary: CHSH Supra-Quantum as Instance

    The CHSH theorem from Certification.v is meant to be a concrete instance:
    - A = CHSHTrial
    - P_weak = chsh_quantum (S ≤ 2√2)
    - P_strong = chsh_supra (S > 2√2)
    - decoder = extract_chsh_trials

    This file does not instantiate those definitions directly. It provides the
    generic shape the CHSH channel can plug into.
    *)

(** Proven Results

    - Abstract receipt predicate framework
    - Strength ordering (≤, <)
    - Generalized Certified predicate
    - General no-free-insight theorem (cert requires cert-setter)
    - Pointer for the CHSH channel shape (see CHSHExtraction.v)
    *)

End NoFreeInsight.
