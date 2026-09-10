From Coq Require Import List Lia Arith.PeanoNat.
Import ListNotations.
From Kernel Require Import VMState VMStep SimulationProof.
From KamiHW Require Import Abstraction FullAbstraction GraphReconstructionBridge
  VerilogSemantics ShadowDeviceTrace ThieleCanonicality.

Definition review_snapshot : KamiSnapshot.
Proof.
  refine {| snap_rich_state := empty_rich_snapshot_state;
            snap_pt_next_id := 1 |};
    first [exact 0 | exact false | exact (fun _ => 0) |
           exact (fun _ _ => 0)].
Defined.

(* The old universal premise was impossible, even on this ordinary snapshot. *)
Theorem old_universal_precondition_impossible :
  ~ (forall ks i, WFDrivenPrecondition ks i).
Proof.
  intro H. specialize (H review_snapshot (instr_pnew [] 0)).
  destruct H as [Hlen _]. change (1 <= 0) in Hlen. inversion Hlen.
Qed.

Definition valid_program := [instr_pnew [1] 0; instr_certify 0].

(* Includes PNEW, a conditional opcode; it is not just an empty run. *)
Theorem valid_program_meets_run_contract :
  WFDrivenRun 2 valid_program review_snapshot.
Proof. vm_compute. repeat split; intros; reflexivity. Qed.

Theorem valid_program_full_state_commutes :
  abs_full_snapshot (full_snapshot_of_snapshot
    (kami_run_driven 2 valid_program review_snapshot)) =
  run_vm 2 valid_program
    (abs_full_snapshot (full_snapshot_of_snapshot review_snapshot)).
Proof. apply driven_trace_commutes, valid_program_meets_run_contract. Qed.

Theorem valid_program_actually_certifies :
  snap_certified (kami_run_driven 2 valid_program review_snapshot) = true /\
  snap_mu (kami_run_driven 2 valid_program review_snapshot) = 1.
Proof. vm_compute. split; reflexivity. Qed.

Theorem visited_invalid_pnew_rejected :
  ~ WFDrivenRun 1 [instr_pnew [] 0] review_snapshot.
Proof.
  intros [[Hlen _] _]. change (1 <= 0) in Hlen. inversion Hlen.
Qed.

Theorem unvisited_invalid_pnew_allowed :
  WFDrivenRun 2 [instr_jump 2 0; instr_pnew [] 0; instr_certify 0] review_snapshot.
Proof. vm_compute. repeat split. Qed.

Theorem invalid_pnew_beyond_fuel_allowed :
  WFDrivenRun 1 [instr_certify 0; instr_pnew [] 0] review_snapshot.
Proof. vm_compute. repeat split. Qed.

Print Assumptions valid_program_full_state_commutes.
Print Assumptions old_universal_precondition_impossible.
