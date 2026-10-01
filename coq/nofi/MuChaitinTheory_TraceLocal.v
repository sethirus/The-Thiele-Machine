From Coq Require Import List Lia Arith.PeanoNat Strings.String.
Import ListNotations.
Set Warnings "-declaration-outside-section,-local-declaration".
Require Import Kernel.VMState.
Require Import Kernel.VMStep.
Require Import Kernel.SimulationProof.
Require Import Kernel.MuLedgerConservation.
Require Import Kernel.MuInformation.
Require Import Kernel.MuNoFreeInsightQuantitative.
Require Import Kernel.MuChaitin.
Require Import Kernel.RevelationRequirement.
Require Import Kernel.NecessityAbstract.
Import RevelationProof.

(** μ–Chaitin theory layer with trace-local pricing.

    [MuChaitinTheory_Interface] requires [priced : forall instr,
    cert_priced instr]. The VM's cost schedule does not meet that
    ([EventGenericAudit.current_schedule_not_globally_cert_priced]), so that
    functor has no instance on the VM. Its main theorem also receives the μ
    payment inside the witness, so the bound follows by arithmetic on the
    interface's own fields.

    Here only the instructions on the theory's own traces must be priced, and
    the witness carries no μ payment: the payment is derived from the
    kernel's certification theorem. A concrete VM run instantiates the
    interface. *)

(** * Kernel facts *)

(** The certifying instruction found along a run is an instruction of the
    trace, and the run pays at least its cost. *)
Lemma supra_cert_setter_in_trace :
  forall fuel trace s_init s_final,
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    has_supra_cert s_final ->
    exists instr,
      In instr trace /\
      MuNoFreeInsightQuantitative.is_cert_setter instr /\
      s_final.(vm_mu) >= s_init.(vm_mu) + instruction_cost instr.
Proof.
  induction fuel as [| fuel IH]; intros trace s_init s_final Hrun Hinit Hsupra.
  - simpl in Hrun. inversion Hrun; subst.
    unfold has_supra_cert in Hsupra. rewrite Hinit in Hsupra. contradiction.
  - simpl in Hrun.
    destruct (nth_error trace (vm_pc s_init)) as [instr |] eqn:Hnth.
    + destruct (MuNoFreeInsightQuantitative.is_cert_setterb instr) eqn:Hsetterb.
      * exists instr. split; [exact (nth_error_In _ _ Hnth) |]. split.
        -- unfold MuNoFreeInsightQuantitative.is_cert_setter. exact Hsetterb.
        -- pose proof (MuNoFreeInsightQuantitative.trace_run_mu_monotone
                         fuel trace (vm_apply s_init instr) s_final Hrun) as Htail.
           rewrite (vm_apply_mu s_init instr) in Htail. lia.
      * assert (Hinit' : (vm_apply s_init instr).(vm_csrs).(csr_cert_addr) = 0%nat).
        { rewrite (MuNoFreeInsightQuantitative.cert_preserved_if_not_cert_setterb
                     s_init instr Hsetterb). exact Hinit. }
        destruct (IH trace (vm_apply s_init instr) s_final Hrun Hinit' Hsupra)
          as [instr' [Hin [Hsetter Hmu]]].
        exists instr'. split; [exact Hin |]. split; [exact Hsetter |].
        assert (Hprefix : s_init.(vm_mu) <= (vm_apply s_init instr).(vm_mu)).
        { rewrite (vm_apply_mu s_init instr). lia. }
        lia.
    + inversion Hrun; subst.
      unfold has_supra_cert in Hsupra. rewrite Hinit in Hsupra. contradiction.
Qed.

(** If every instruction of the trace is priced, the μ-information of a
    certifying run is at least the payload of an instruction of the trace
    that certifies. *)
Theorem supra_cert_paid_payload_trace_local :
  forall fuel trace s_init s_final,
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    has_supra_cert s_final ->
    (forall instr, In instr trace -> MuChaitin.cert_priced instr) ->
    exists instr,
      In instr trace /\
      MuNoFreeInsightQuantitative.is_cert_setter instr /\
      mu_info_nat s_init s_final >= MuChaitin.cert_payload_size instr.
Proof.
  intros fuel trace s_init s_final Hrun Hinit Hsupra Hpriced.
  destruct (supra_cert_setter_in_trace fuel trace s_init s_final Hrun Hinit Hsupra)
    as [instr [Hin [Hsetter Hmu]]].
  exists instr. split; [exact Hin |]. split; [exact Hsetter |].
  pose proof (Hpriced instr Hin Hsetter) as Hcost.
  pose proof (MuChaitin.mu_info_nat_ge_from_mu_total s_init s_final
                (instruction_cost instr) Hmu) as Hinfo.
  lia.
Qed.

(** * Interface *)

#[warnings="-declaration-outside-section"]
Module Type MU_CHAITIN_TRACE_SYSTEM.
  Variable theory_desc : string.
  Variable overhead : nat.
  Variable proves_bits : nat -> Prop.
  Variable trace_for : nat -> Trace.
  Variable fuel_for : nat -> nat.
  Variable s_init : VMState.

  Variable clean_start : s_init.(vm_csrs).(csr_cert_addr) = 0%nat.

  (** Only the instructions the theory actually runs must be priced. *)
  Variable priced_on_traces :
    forall k instr, In instr (trace_for k) -> MuChaitin.cert_priced instr.

  (** A theory that proves [k] bits has a run that certifies, whose
      certifying instructions each carry at least [k] payload bits, and whose
      μ ledger stays within the description size plus overhead. No μ payment
      is assumed here. *)
  Variable proves_bits_witness :
    forall k,
      proves_bits k ->
      exists s_final,
        trace_run (fuel_for k) (trace_for k) s_init = Some s_final /\
        has_supra_cert s_final /\
        (forall instr, In instr (trace_for k) ->
           MuNoFreeInsightQuantitative.is_cert_setter instr ->
           MuChaitin.cert_payload_size instr >= k) /\
        s_final.(vm_mu) <= s_init.(vm_mu) + payload_bit_length theory_desc + overhead.
End MU_CHAITIN_TRACE_SYSTEM.

(** * Theorem *)

Module MuChaitinTraceLocal (X : MU_CHAITIN_TRACE_SYSTEM).

  (** Chaitin-style bound in μ currency, with the payment derived from the
      kernel: a theory proves no more bits than its description size plus
      overhead. *)
  Theorem proves_bits_bounded_by_description_trace_local :
    forall k,
      X.proves_bits k ->
      k <= payload_bit_length X.theory_desc + X.overhead.
  Proof.
    intros k Hprove.
    destruct (X.proves_bits_witness k Hprove)
      as [s_final [Hrun [Hsupra [Hpayload Hbudget]]]].
    destruct (supra_cert_paid_payload_trace_local _ _ _ _ Hrun X.clean_start Hsupra
                (X.priced_on_traces k))
      as [instr [Hin [Hsetter Hinfo]]].
    pose proof (Hpayload instr Hin Hsetter) as Hk.
    unfold mu_info_nat, mu_total in Hinfo.
    lia.
  Qed.

End MuChaitinTraceLocal.

(** * A VM instance *)

(** Create a module, add its identity morphism, and assert a property of it.
    MORPH_ASSERT writes the property's checksum into [csr_cert_addr]; its
    cost covers its eight-bit payload. *)
Module KernelTraceInstance <: MU_CHAITIN_TRACE_SYSTEM.
  Definition theory_desc : string := ""%string.
  Definition overhead : nat := 9.
  Definition proves_bits (k : nat) : Prop := k <= 8.
  Definition morph_trace : Trace :=
    [instr_pnew [0] 0; instr_morph_id 0 0 0; instr_morph_assert 0 "p"%string ""%string 8].
  Definition trace_for (_ : nat) : Trace := morph_trace.
  Definition fuel_for (_ : nat) : nat := 3.
  Definition s_init : VMState := abs_zero.

  Lemma clean_start : s_init.(vm_csrs).(csr_cert_addr) = 0%nat.
  Proof. reflexivity. Qed.

  Lemma priced_on_traces :
    forall k instr, In instr (trace_for k) -> MuChaitin.cert_priced instr.
  Proof.
    intros k instr Hin Hsetter.
    unfold trace_for, morph_trace in Hin. simpl in Hin.
    destruct Hin as [<- | [<- | [<- | []]]];
      try (unfold MuNoFreeInsightQuantitative.is_cert_setter in Hsetter;
           simpl in Hsetter; discriminate).
    vm_compute. lia.
  Qed.

  Lemma morph_run :
    trace_run 3 morph_trace abs_zero =
      Some (match trace_run 3 morph_trace abs_zero with Some s => s | None => abs_zero end).
  Proof. vm_compute. reflexivity. Qed.

  Lemma proves_bits_witness :
    forall k,
      proves_bits k ->
      exists s_final,
        trace_run (fuel_for k) (trace_for k) s_init = Some s_final /\
        has_supra_cert s_final /\
        (forall instr, In instr (trace_for k) ->
           MuNoFreeInsightQuantitative.is_cert_setter instr ->
           MuChaitin.cert_payload_size instr >= k) /\
        s_final.(vm_mu) <= s_init.(vm_mu) + payload_bit_length theory_desc + overhead.
  Proof.
    intros k Hk.
    exists (match trace_run 3 morph_trace abs_zero with Some s => s | None => abs_zero end).
    split; [exact morph_run |].
    split; [unfold has_supra_cert; vm_compute; discriminate |].
    split.
    - intros instr Hin Hsetter.
      unfold trace_for, morph_trace in Hin. simpl in Hin.
      destruct Hin as [<- | [<- | [<- | []]]];
        try (unfold MuNoFreeInsightQuantitative.is_cert_setter in Hsetter;
             simpl in Hsetter; discriminate).
      unfold proves_bits in Hk. vm_compute. lia.
    - vm_compute. lia.
  Qed.
End KernelTraceInstance.

Module KernelTraceBound := MuChaitinTraceLocal KernelTraceInstance.

(** On the VM run above, the theory proves at most nine bits. *)
Theorem kernel_trace_instance_bound :
  forall k, KernelTraceInstance.proves_bits k -> k <= 9.
Proof.
  intros k Hk.
  exact (KernelTraceBound.proves_bits_bounded_by_description_trace_local k Hk).
Qed.

(** The instance is inhabited: eight bits are proved. *)
Theorem kernel_trace_instance_inhabited : KernelTraceInstance.proves_bits 8.
Proof. unfold KernelTraceInstance.proves_bits. lia. Qed.

Print Assumptions supra_cert_setter_in_trace.
Print Assumptions supra_cert_paid_payload_trace_local.
Print Assumptions kernel_trace_instance_bound.
Print Assumptions kernel_trace_instance_inhabited.
