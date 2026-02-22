From Coq Require Import List Lia Arith.PeanoNat.
Import ListNotations.

Require Import VMState.
Require Import VMStep.
Require Import SimulationProof.
Require Import MuLedgerConservation.
Require Import RevelationRequirement.

Require Import NoFI.NoFreeInsight_Interface.
Require Import NoFI.NoFreeInsight_Theorem.

Module KernelNoFI <: NO_FREE_INSIGHT_SYSTEM.
  Definition S := VMState.
  Definition Trace := list vm_instruction.
  Definition Obs := nat.
  (** A simple, nontrivial “strength” domain: threshold on cert_addr.

      Intuition: stronger claims require a higher cert_addr threshold.
      This is a minimal instance that makes [strictly_stronger] nontrivial.
  *)
  Definition Strength := nat.

  (* Deterministic bounded execution: fuel = S (length trace) is sufficient
     for the kernel encoding used throughout the repo. *)
  Definition run (tr : Trace) (s0 : S) : option S :=
    RevelationProof.trace_run (Nat.succ (length tr)) tr s0.

  Definition ok (s : S) : Prop := s.(vm_err) = false.

  Definition mu (s : S) : nat := s.(vm_mu).

  (* Minimal observable: the certification address. *)
  Definition observe (s : S) : Obs := s.(vm_csrs).(csr_cert_addr).

  (* A “certification strength” witness is uninterpreted here; the kernel
     instance uses only the existence of a non-zero cert_addr. *)
  Definition certifies (s : S) (strength : Strength) : Prop :=
    strength <> 0 /\ strength <= observe s /\ RevelationProof.has_supra_cert s.

  Definition Certified (tr : Trace) (s0 : S) (strength : Strength) : Prop :=
    exists s1, run tr s0 = Some s1 /\ ok s1 /\ certifies s1 strength.

  (** [Certified_spec]: formal specification. *)
  Lemma Certified_spec :
    forall tr s0 strength,
      Certified tr s0 strength <->
      exists s1, run tr s0 = Some s1 /\ ok s1 /\ certifies s1 strength.
  Proof.
    intros tr s0 strength. unfold Certified. tauto.
  Qed.

  Definition strictly_stronger (a b : Strength) : Prop := b < a.

  (* Structure event (semantic): cert_addr transitions 0 -> nonzero during execution. *)
  Definition structure_event (tr : Trace) (s0 : S) : Prop :=
    RevelationProof.structure_addition_in_run (Nat.succ (length tr)) tr s0.

  Definition clean_start (s : S) : Prop :=
    s.(vm_csrs).(csr_cert_addr) = 0.

  (** [trace_run_mu_monotone]: formal specification. *)
  Lemma trace_run_mu_monotone :
    forall fuel tr s0 s1,
      RevelationProof.trace_run fuel tr s0 = Some s1 ->
      vm_mu s0 <= vm_mu s1.
  Proof.
    induction fuel as [|fuel IH]; intros tr s0 s1 Hrun.
    - simpl in Hrun. inversion Hrun; subst. lia.
    - simpl in Hrun.
      destruct (nth_error tr (vm_pc s0)) as [instr|] eqn:Hnth.
      + eapply (Nat.le_trans _ (vm_mu (vm_apply s0 instr)) _).
        * rewrite (vm_apply_mu s0 instr). lia.
        * eapply IH. exact Hrun.
      + inversion Hrun; subst. lia.
  Qed.

  (** [mu_monotone]: formal specification. *)
  Lemma mu_monotone :
    forall tr s0 s1,
      run tr s0 = Some s1 ->
      mu s0 <= mu s1.
  Proof.
    unfold run, mu.
    intros tr s0 s1 Hrun.
    eapply trace_run_mu_monotone.
    exact Hrun.
  Qed.

  (** [no_free_insight_contract]: formal specification. *)
  Theorem no_free_insight_contract :
    forall tr s0 s1 strength weak,
      clean_start s0 ->
      run tr s0 = Some s1 ->
      strictly_stronger strength weak ->
      certifies s1 strength ->
      structure_event tr s0.
  Proof.
    unfold clean_start, run, certifies, structure_event.
    intros tr s0 s1 strength weak Hclean Hrun Hstrict Hcert.
    destruct Hcert as [_ [_ Hhas]].
    eapply RevelationProof.supra_cert_implies_structure_addition_in_run; eauto.
  Qed.
End KernelNoFI.

Module KernelNoFI_Theorem := NoFreeInsight_Theorem.NoFreeInsight(KernelNoFI).
