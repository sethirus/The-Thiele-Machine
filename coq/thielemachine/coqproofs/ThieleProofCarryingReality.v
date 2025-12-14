(**
  THIELE PROOF-CARRYING REALITY (Concrete receipts replay)

  This file provides an explicit, checkable proof that a nontrivial concrete
  program trace has a receipt stream accepted by the executable replay checker.

  The intent is Task 12 style: a run artifact + a verifier that accepts it.
*)

From Coq Require Import List.
Import ListNotations.

From ThieleMachine Require Import ThieleMachineConcrete.
From ThieleMachine Require Import BellInequality.

Module ThieleProofCarryingReality.

  Module TM := ThieleMachineConcrete.

  Lemma concrete_exec_trace_of :
    forall prog s,
      TM.ConcreteExec prog s (TM.concrete_trace_of s prog).
  Proof.
    induction prog as [|instr tl IH]; intro s; simpl.
    - constructor.
    - destruct (TM.concrete_step instr s) as [post obs] eqn:Hstep.
      econstructor.
      + (* concrete_step equality *)
        exact Hstep.
      + (* tail execution *)
        apply IH.
  Qed.

  Theorem supra_quantum_receipts_replay_ok :
    TM.concrete_replay_ok
      BellInequality.supra_quantum_start
      BellInequality.supra_quantum_receipts
    = true.
  Proof.
    unfold BellInequality.supra_quantum_receipts.
    (* derive replay_ok from the execution relation and the generic receipts checker lemma *)
    eapply TM.concrete_exec_receipts_ok.
    apply concrete_exec_trace_of.
  Qed.

End ThieleProofCarryingReality.
