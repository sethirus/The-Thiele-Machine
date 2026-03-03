(** =========================================================================
    NO-FREE-INSIGHT LOAD-BEARING DEPENDENCY GUARD
    =========================================================================

    This file ensures downstream proofs can depend on the strengthened
    NoFreeInsight theorem in a nontrivial way.

    Unlike a mere symbol-presence check, this proof applies
    [NoFreeInsight.strengthening_obs_requires_structure_addition] directly.
    ========================================================================= *)

From Kernel Require Import VMState SimulationProof RevelationRequirement NoFreeInsight.

Import RevelationProof.

Lemma nofi_strengthening_bridge_guard :
  forall (A : Type)
         (decoder : NoFreeInsight.receipt_decoder A)
         (P_weak P_strong : NoFreeInsight.ReceiptPredicate A)
         (trace : NoFreeInsight.Receipts)
         (s_init : VMState)
         (fuel : nat),
    NoFreeInsight.strictly_stronger P_strong P_weak ->
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
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

Print Assumptions nofi_strengthening_bridge_guard.
