From Coq Require Import Lia Arith.PeanoNat Strings.String.

Require Import NoFI.MuChaitinTheory_Interface.

Require Import Kernel.VMState.
Require Import Kernel.MuInformation.
Require Import Kernel.MuChaitin.
Require Import Kernel.MuNoFreeInsightQuantitative.
Require Import Kernel.RevelationRequirement.

(** * μ–Chaitin Theory Theorem (functor)

    This is the “theory layer” quantitative incompleteness theorem.

    It is deliberately minimal: it does not depend on any particular notion of
    syntax, proof rules, or halting encoding. Those are provided by an
    instantiation of [MU_CHAITIN_THEORY_SYSTEM].

    The only kernel facts used are:
    - μ-information is the difference of μ-ledgers (MuInformation.mu_info_nat)
    - μ-information upper-bounds by any stated μ-budget

    The heavy kernel work (certification → paid μ-information) remains in
    [Kernel.MuChaitin]; an instantiation may choose to derive the witness
    obligation from that theorem.
*)

Module MuChaitinTheory (X : MU_CHAITIN_THEORY_SYSTEM).

  (** Reduction lemma (kernel → μ-information):

      Any concrete kernel run that ends in supra-certification yields a
      cert-setting instruction whose payload-size is paid for by μ-information,
      assuming the pricing policy [X.priced].

      This is a direct wrapper around [Kernel.MuChaitin].
  *)
  Lemma supra_cert_run_implies_paid_payload :
    forall fuel trace s_final,
      RevelationProof.trace_run fuel trace X.s_init = Some s_final ->
      X.s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
      RevelationProof.has_supra_cert s_final ->
      exists instr,
        MuNoFreeInsightQuantitative.is_cert_setter instr /\
        mu_info_nat X.s_init s_final >= MuChaitin.cert_payload_size instr.
  Proof.
    intros fuel trace s_final Hrun Hinit Hsupra.
    eapply MuChaitin.supra_cert_implies_mu_bounds_cert_payload; eauto.
    exact X.priced.
  Qed.

  (** [mu_info_nat_le_from_mu_budget]: formal specification. *)
  Lemma mu_info_nat_le_from_mu_budget :
    forall (s_init s_final : VMState) (k : nat),
      s_final.(vm_mu) <= s_init.(vm_mu) + k ->
      mu_info_nat s_init s_final <= k.
  Proof.
    intros s_init s_final k H.
    unfold mu_info_nat, mu_total.
    lia.
  Qed.

  (** Main theorem: Chaitin-style bound in μ currency.

      If the theory can certify/prove ≥ k bits (in the sense of the interface
      witness), then k is bounded by the description size plus fixed overhead.
  *)
  Theorem proves_bits_bounded_by_description :
    forall k,
      X.proves_bits k ->
      k <= String.length X.theory_desc + X.overhead.
  Proof.
    intros k Hprove.
    destruct (X.proves_bits_witness k Hprove)
      as [s_final [instr [Hrun [Hsupra [Hsetter [Hmu_ge [Hpayload_ge Hbudget]]]]]]].

    assert (Hbudget' :
              s_final.(vm_mu) <=
              X.s_init.(vm_mu) + (String.length X.theory_desc + X.overhead))
      by lia.

    (* Convert the μ budget on [vm_mu] into a bound on [mu_info_nat]. *)
    pose proof (mu_info_nat_le_from_mu_budget X.s_init s_final
                  (String.length X.theory_desc + X.overhead) Hbudget')
      as Hmu_le.

    (* Chain: k <= payload <= mu_info <= budget. *)
    lia.
  Qed.

End MuChaitinTheory.
