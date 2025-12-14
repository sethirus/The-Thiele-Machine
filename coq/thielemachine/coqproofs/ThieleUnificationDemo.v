(**
  THIELE UNIFICATION DEMO (kernel semantics, executable in Coq)

  This file constructs a small kernel VM trace and proves:
    - μ ledger conservation for the run
    - a no-signaling instance: PDISCOVER on module 1 leaves module 2 unchanged
*)

From Coq Require Import List Lia.
From Coq Require Import Strings.String.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.
From ThieleMachine Require Import ThieleUnificationProtocol.

Open Scope nat_scope.
Open Scope string_scope.

Module Demo.

  Definition init_csrs : VMState.CSRState :=
    {| VMState.csr_cert_addr := 0;
       VMState.csr_status := 0;
       VMState.csr_err := 0 |}.

  Definition init_vm : VMState.VMState :=
    {| VMState.vm_graph := VMState.empty_graph;
       VMState.vm_csrs := init_csrs;
       VMState.vm_regs := repeat 0 VMState.REG_COUNT;
       VMState.vm_mem := repeat 0 VMState.MEM_SIZE;
       VMState.vm_pc := 0;
       VMState.vm_mu := 0;
       VMState.vm_err := false |}.

  Definition trace : list VMStep.vm_instruction :=
    [ VMStep.instr_pnew [1] 1;
      VMStep.instr_pnew [2] 1;
      VMStep.instr_pdiscover 1 ["E1"] 1;
      VMStep.instr_halt 0
    ].

  (* Executable sanity checks (printed by coqc) *)
  Compute (VMState.vm_mu (SimulationProof.run_vm 3 trace init_vm)).
  Compute (VMState.graph_lookup (VMState.vm_graph (SimulationProof.run_vm 3 trace init_vm)) 2).

  (* No-signaling instance: module 2's graph payload unaffected by PDISCOVER on module 1. *)
  Example demo_no_signaling_module2 :
    VMState.graph_lookup (VMState.vm_graph (SimulationProof.run_vm 3 trace init_vm)) 2 =
    VMState.graph_lookup (VMState.vm_graph (SimulationProof.run_vm 2 trace init_vm)) 2.
  Proof.
    (* Reduce to a single-step no-signaling theorem at the PDISCOVER point. *)
    unfold SimulationProof.run_vm.
    (* step 0: pnew [1] *)
    simpl.
    (* step 1: pnew [2] *)
    simpl.
    (* Now the next instruction is pdiscover on module 1. *)
    simpl.
    (* Apply locality lemma from the protocol file. *)
    apply (ThieleUnificationProtocol.no_signaling_pdiscover_graph
             (SimulationProof.vm_apply (SimulationProof.vm_apply init_vm (VMStep.instr_pnew [1] 1))
                                       (VMStep.instr_pnew [2] 1))
             1 ["E1"] 1 2).
    discriminate.
  Qed.

  (* μ ledger conservation specialized to this run: μ = 3 (three cost=1 steps). *)
  Example demo_mu_total :
    VMState.vm_mu (SimulationProof.run_vm 3 trace init_vm) = 3.
  Proof.
    vm_compute.
    reflexivity.
  Qed.

End Demo.
