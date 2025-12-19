From Coq Require Import List Lia Arith.PeanoNat Strings.String.
Import ListNotations.

Require Import VMState.
Require Import VMStep.
Require Import MuInformation.
Require Import MuNoFreeInsightQuantitative.
Require Import RevelationRequirement.

(** * μ–Chaitin (kernel-level quantitative incompleteness)

    This file packages a “Chaitin-style” quantitative limitation in the *kernel* currency μ.

    It does **not** attempt to formalize computably axiomatizable theories in full generality.
    Instead it proves the kernel-native statement that drives such results in this repo:

      Any successful certification event must include a cert-setting instruction, and the
      μ-information injected by the run lower-bounds (at least) the declared cost of that
      cert-setting step.

    By adding a *pricing policy* (a pure inequality relating declared costs to the size of the
    certified payload), this yields a mechanically checkable resource bound:

      “You cannot certify more payload-information than your μ budget.”

    This is the direct analog of Chaitin’s phenomenon (“no theory of bounded description
    can certify arbitrarily high complexity facts”), but expressed in the Thiele kernel’s
    executable accounting.
*)

Module MuChaitin.

Import VMStep.VMStep.
Import RevelationProof.

(** A small “payload size” measure for cert-setting instructions.

    This is intentionally conservative and purely syntactic:
    - REVEAL contributes its explicit [bits] parameter.
    - EMIT contributes the byte-length of the payload string.
    - LJOIN contributes the sum of the two certificate string lengths.
    - LASSERT contributes the length of the formula string.

    All other instructions contribute 0.
*)
Definition cert_payload_size (i : vm_instruction) : nat :=
  match i with
  | instr_reveal _ bits _ _ => bits
  | instr_emit _ payload _ => String.length payload
  | instr_ljoin c1 c2 _ => String.length c1 + String.length c2
  | instr_lassert _ formula _ _ => String.length formula
  | _ => 0
  end.

(** Pricing policy (the only additional assumption needed to turn the structural
    no-free-insight theorem into a quantitative “bits ≤ μ” statement).

    Read this as: “declared μ-cost is at least the size of the certified payload”.
*)
Definition cert_priced (i : vm_instruction) : Prop :=
  MuNoFreeInsightQuantitative.is_cert_setter i -> cert_payload_size i <= instruction_cost i.

Lemma mu_info_nat_ge_from_mu_total :
  forall (s_init s_final : VMState) (k : nat),
    s_final.(vm_mu) >= s_init.(vm_mu) + k ->
    mu_info_nat s_init s_final >= k.
Proof.
  intros s_init s_final k H.
  unfold mu_info_nat, mu_total.
  lia.
Qed.

(** Core quantitative certificate bound:

    If a bounded trace-run ends in supra-certification (cert CSR becomes nonzero), then
    there exists a cert-setting instruction whose cost is paid by the run.

    This is the kernel-native “quantitative incompleteness” statement: certification cannot
    happen “for free”.
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

(** “Chaitin-style” corollary under a pricing policy:

    Under [cert_priced], any successful certification injects at least as much μ-information
    as the size (in our [cert_payload_size] measure) of the cert-setting instruction.
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
