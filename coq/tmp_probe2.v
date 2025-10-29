From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.
Require Import Kernel.VMState.
Require Import Kernel.VMStep.
Require Import Kernel.SimulationProof.

Goal True.
intros fuel trace s.
induction fuel as [|fuel IH]; simpl.
- exact I.
- remember (nth_error trace (vm_pc s)) as maybe_instr eqn:Hfetch.
  destruct maybe_instr as [instr|]; simpl.
  Check instr.
  Check maybe_instr.
  Check (nth_error trace (vm_pc s)).
Abort.