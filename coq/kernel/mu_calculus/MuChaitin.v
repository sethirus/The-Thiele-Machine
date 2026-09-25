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

    *)

From Coq Require Import List Lia Arith.PeanoNat Strings.String.
Import ListNotations.

From Kernel Require Import VMState VMStep.
From Kernel Require Import MuInformation MuNoFreeInsightQuantitative.
From Kernel Require Import RevelationRequirement.

Module MuChaitin.

Import VMStep.VMStep.
Import RevelationProof.

(** [cert_payload_size] is the instruction-local syntactic bit measure used by
    the pricing policy. It counts the explicit payload fields for receipt and
    assertion instructions and returns zero for constructors without a payload
    component in this measure. It is not a semantic information measure. *)
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

(** [cert_priced] is an explicit VM pricing premise: every cert-setter's
    scheduled cost is at least its [cert_payload_size]. The later payload bound
    is conditional on this policy; changing the schedule changes the premise,
    not the arithmetic proof. *)
Definition cert_priced (i : vm_instruction) : Prop :=
  MuNoFreeInsightQuantitative.is_cert_setter i -> cert_payload_size i <= instruction_cost i.

(** [mu_info_nat_ge_from_mu_total] converts the supplied ledger inequality into
    the natural-number difference used by this module's information notation.
    The statement is arithmetic over [vm_mu]; it does not calibrate that
    difference as physical information. *)
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

    The conclusion is conditional on the supplied trace, initial CSR, and
    final supra-certification hypotheses. It is a VM accounting statement, not
    a claim that the ledger is a universal information measure.
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

    The payload conclusion remains conditional on [cert_priced]. A different
    pricing schedule is a different instance of the policy.
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
