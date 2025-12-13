(** * Hardware/VM alignment helpers

    This optional module packages a faithful-implementation witness built from
    an RTL-style stepper and exposes µ/irreversibility corollaries so Verilog
    traces can be compared directly against the VM ledger accounting.  It sits
    on top of the generic [FaithfulImplementation] contract from
    [ThieleManifoldBridge].
*)

From Coq Require Import List NArith Lia.
From Kernel Require Import VMState VMStep MuLedgerConservation SimulationProof.
From ThieleMachine Require Import HardwareBridge.
From ThieleManifold Require Import ThieleManifoldBridge.

Import ListNotations.
Local Open Scope nat_scope.

(** ** Totalising the RTL stepper

    The RTL micro-semantics in [HardwareBridge] is partial (halting returns
    [None]).  For the faithful-implementation contract we need a total step
    function, so we conservatively stay in place when the RTL fetch fails. *)
Definition rtl_step_total (s : HardwareBridge.RTLState) : HardwareBridge.RTLState :=
  match HardwareBridge.rtl_step s with
  | Some (s', _) => s'
  | None => s
  end.

(** ** Packaging a faithful implementation from an RTL refinement hypothesis *)
Section WithRefinement.
  Variable vm_trace   : list vm_instruction.
  Variable decode_vm  : HardwareBridge.RTLState -> VMState.
  Variable rtl_refines_vm : forall fuel s,
    decode_vm (impl_iter rtl_step_total fuel s) =
      run_vm fuel vm_trace (decode_vm s).

  Definition rtl_faithful_impl : FaithfulImplementation :=
    {| hw_state := HardwareBridge.RTLState;
       hw_step := rtl_step_total;
       hw_decode := decode_vm;
       hw_trace := vm_trace;
       hw_refines_vm := rtl_refines_vm |}.

  Lemma rtl_mu_conservation :
    forall fuel s,
      (decode_vm (impl_iter rtl_step_total fuel s)).(vm_mu) =
        (decode_vm s).(vm_mu) +
        ledger_sum (ledger_entries fuel vm_trace (decode_vm s)).
  Proof.
    apply (faithful_impl_mu_conservation rtl_faithful_impl).
  Qed.

  Lemma rtl_irreversibility_lower_bound :
    forall fuel s,
      irreversible_count fuel vm_trace (decode_vm s) <=
        (decode_vm (impl_iter rtl_step_total fuel s)).(vm_mu) -
        (decode_vm s).(vm_mu).
  Proof.
    apply (faithful_impl_irreversibility_lower_bound rtl_faithful_impl).
  Qed.

End WithRefinement.
