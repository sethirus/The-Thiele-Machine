(**
    MuChaitin: certificate payload bounds from mu accounting.

    This file proves a kernel-level accounting statement inspired by Chaitin-style
    "no free certification" language. It does not formalize Kolmogorov
    complexity or Chaitin's incompleteness theorem. It proves that, for traces
    that turn the certification CSR from zero to nonzero, the imported trace
    theorem supplies a cert-setting instruction whose cost is bounded by the
    total mu increase.

    If a trace achieves supra-certification (cert CSR becomes nonzero), there
    exists a cert-setting instruction whose μ-cost bounds the certified payload.
    Main theorem: supra_cert_implies_mu_bounds_cert_payload.

    cert_payload_size: syntactic bit measure of certification payload (REVEAL
    bits, EMIT payload bits, READ_PORT bits, LASSERT formula bits, and explicit
    certify deltas).
    supra_cert_implies_mu_info_nat_lower_bound: certification requires μ-cost ≥
    instruction_cost of cert-setter.
    supra_cert_implies_mu_bounds_cert_payload: under pricing policy (cost ≥
    payload size), μ-information ≥ certified payload size.

    The pricing policy (cert_priced) is a policy, not derived: it assumes
    instruction_cost ≥ cert_payload_size for cert-setters. Given that policy,
    the bound follows from μ-monotonicity (MuNoFreeInsightQuantitative.v).

    To falsify: find a trace that achieves supra-certification starting from
    cert=0 but has μ_final - μ_initial < cert_payload_size of the cert-setter.

    Alternatively, choose a VM pricing rule where cert-setting instructions cost
    less than cert_payload_size; that rejects the policy premise rather than the
    proved implication.

    The pricing policy is not hidden here; it is an explicit theorem premise.

    *)

From Coq Require Import List Lia Arith.PeanoNat Strings.String.
Import ListNotations.

From Kernel Require Import VMState VMStep.
From Kernel Require Import MuInformation MuNoFreeInsightQuantitative.
From Kernel Require Import RevelationRequirement.

Module MuChaitin.

Import VMStep.VMStep.
Import RevelationProof.

(** cert_payload_size: Syntactic bit measure of certification payload

    WHAT IT COUNTS: The "size" of information being certified by an instruction,
    measured in bits.

    SPECIFIC RULES:
    - REVEAL: explicit bits parameter (how many bits of state revealed)
    - EMIT: concrete payload bits, eight Boolean bits per Coq ascii byte
    - READ_PORT: explicit bits parameter (how many bits are read)
    - LJOIN: 0 here because certificate sizes are not statically available
    - LASSERT: encoded formula units converted to concrete bits
    - MORPH_ASSERT: concrete bits in the property and certificate payloads
    - CERTIFY: explicit delta_mu argument
    - All other instructions: 0 (no certification)

    WHY SYNTACTIC: This is a local size measure, not a semantic information
    theorem. The pricing policy below decides whether instruction_cost must
    cover this syntactic measure.

    To falsify: Show an instruction that certifies N bits of information
    but has cert_payload_size < N. This would mean our syntactic measure
    underestimates the intended payload; the theorem remains about this measure.
*)
Definition cert_payload_size (i : vm_instruction) : nat :=
  match i with
  | instr_reveal _ bits _ _ => bits
  | instr_emit _ payload _ => payload_bit_length payload
  | instr_read_port _ _ _ bits _ => bits
  | instr_ljoin _ _ _ => 0  (* cert size not statically known; address in memory *)
  | instr_lassert _ _ _ flen _ => flen * 8
  | instr_morph_assert _ property cert _ =>
      payload_bit_length property + payload_bit_length cert
  | instr_certify delta_mu => delta_mu
  | instr_and _ _ _ _ => 0
  | instr_or _ _ _ _ => 0
  | instr_shl _ _ _ _ => 0
  | instr_shr _ _ _ _ => 0
  | instr_mul _ _ _ _ => 0
  | instr_lui _ _ _ => 0
  | _ => 0
  end.

(** cert_priced: Pricing policy for certification instructions

    POLICY instruction_cost ≥ cert_payload_size for cert-setters.

    WHY A POLICY: This is a VM pricing choice, not a theorem. The VM could price
    cert-setters differently, but under this policy:
    1. Certification costs proportional to certified payload
    2. No "free certification" relative to the cert_payload_size measure
    3. The later theorem can chain cost paid to payload size

    To reject this premise: choose an instruction pricing table where some
    cert-setter has instruction_cost < cert_payload_size.
*)
Definition cert_priced (i : vm_instruction) : Prop :=
  MuNoFreeInsightQuantitative.is_cert_setter i -> cert_payload_size i <= instruction_cost i.

(** mu_info_nat_ge_from_mu_total: Information from total μ-cost

    CLAIM: If final μ ≥ initial μ + k, then μ-information ≥ k.

    PROOF: Direct from definitions. μ-information = μ_final - μ_initial.
    If μ_final ≥ μ_initial + k, then μ_final - μ_initial ≥ k. QED.

    WHY THIS MATTERS: Converts total μ-cost bound into information bound.
    The μ-ledger directly measures accumulated information (structural cost).

    To falsify: Find states where μ_final - μ_initial ≠ accumulated cost
    (violating μ-ledger conservation).
*)
Lemma mu_info_nat_ge_from_mu_total :
  forall (s_init s_final : VMState) (k : nat),
    s_final.(vm_mu) >= s_init.(vm_mu) + k ->
    mu_info_nat s_init s_final >= k.
Proof.
  intros s_init s_final k H.
  unfold mu_info_nat, mu_total.
  lia.
Qed.

(** supra_cert_implies_mu_info_nat_lower_bound: accounting lower bound

    If a trace achieves supra-certification (cert CSR goes from 0 to nonzero),
    then there exists a cert-setting instruction whose cost was paid, and
    μ-information ≥ that cost.

    CLAIM: Certifying without paying never happens. Certification is not free.

    1. Invoke supra_cert_implies_mu_lower_bound_trace_run from MuNoFreeInsightQuantitative
    2. That theorem guarantees existence of cert-setter with μ-cost paid
    3. Convert μ-cost bound to μ-information bound via mu_info_nat_ge_from_mu_total
    4. Therefore: μ-information ≥ instruction_cost(cert-setter). QED.

    Chaitin-style reading: certification in this VM is tied to a paid
    cert-setting instruction. This file does not formalize Gödel, Chaitin, or
    Kolmogorov complexity.

    To falsify: Find a trace where:
    - Initial cert CSR = 0
    - Final cert CSR > 0 (supra-certification achieved)
    - But μ_final - μ_initial < instruction_cost(any cert-setter in trace)
    This would mean "free certification" (information created from nothing).
*)
Theorem supra_cert_implies_mu_info_nat_lower_bound :
  forall fuel trace s_init s_final,
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    has_supra_cert s_final ->
    exists instr,
      MuNoFreeInsightQuantitative.is_cert_setter instr /\
      mu_info_nat s_init s_final >= instruction_cost instr.
Proof.
  intros fuel trace s_init s_final Hrun Hinit Hsupra.
  destruct (
    MuNoFreeInsightQuantitative.supra_cert_implies_mu_lower_bound_trace_run
      fuel trace s_init s_final Hrun Hinit Hsupra
  ) as [instr [Hsetter Hmu]].
  exists instr.
  split.
  - exact Hsetter.
  - apply mu_info_nat_ge_from_mu_total.
    exact Hmu.
Qed.

(** supra_cert_implies_mu_bounds_cert_payload: payload lower bound under policy

    Under pricing policy (cert_priced), successful certification requires
    μ-information ≥ cert_payload_size of the cert-setter.

    CLAIM: You must pay at least as much μ as the size of the certificate.

    1. Invoke supra_cert_implies_mu_info_nat_lower_bound (previous theorem)
    2. That gives: μ-information ≥ instruction_cost(instr)
    3. Pricing policy gives: instruction_cost(instr) ≥ cert_payload_size(instr)
    4. Chain inequalities: μ-information ≥ cert_payload_size(instr). QED.

    Chaitin-style reading: if the VM prices certificate payloads by size, then
    certification cannot outrun the paid mu ledger. This is a policy-conditioned
    accounting theorem, not a physical Landauer derivation.

    To falsify: find a trace satisfying supra-certification with μ-information
    below payload size while the cert_priced premise still holds.
*)
Theorem supra_cert_implies_mu_bounds_cert_payload :
  forall fuel trace s_init s_final,
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    has_supra_cert s_final ->
    (forall instr, cert_priced instr) ->
    exists instr,
      MuNoFreeInsightQuantitative.is_cert_setter instr /\
      mu_info_nat s_init s_final >= cert_payload_size instr.
Proof.
  intros fuel trace s_init s_final Hrun Hinit Hsupra Hpriced.
  destruct (supra_cert_implies_mu_info_nat_lower_bound fuel trace s_init s_final Hrun Hinit Hsupra)
    as [instr [Hsetter Hmu]].
  exists instr.
  split.
  - exact Hsetter.
  - specialize (Hpriced instr).
    unfold cert_priced in Hpriced.
    specialize (Hpriced Hsetter).
    (* cost is paid; payload is priced by cost *)
    eapply Nat.le_trans.
    + exact Hpriced.
    + exact Hmu.
Qed.

End MuChaitin.
