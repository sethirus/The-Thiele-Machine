From Coq Require Import List Arith.PeanoNat Lia.
Require Import Kernel.VMState.
Require Import Kernel.VMStep.
Require Import Kernel.SimulationProof.
Require Import Kernel.MuLedgerConservation.

(* Probe the proof state at the remember/destruct site. *)

Lemma tmp_probe : True.
Proof.
  (* copy the beginning of bounded_ledger_conservation proof *)
  intros fuel trace s.
  induction fuel as [|fuel IH]; simpl.
  - constructor.
  - remember (nth_error trace (vm_pc s)) as maybe_instr eqn:Hfetch.
    Check maybe_instr.
Abort.
