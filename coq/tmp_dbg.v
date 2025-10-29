From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.
Require Import Kernel.VMState.
Require Import Kernel.VMStep.
Require Import Kernel.SimulationProof.

Goal forall fuel trace s,
  ledger_conserved (bounded_run fuel trace s)
                   (ledger_entries fuel trace s).
Proof.
  intros fuel trace s.
  induction fuel as [|fuel IH]; simpl.
  - constructor.
  - remember (nth_error trace (vm_pc s)) as maybe_instr eqn:Hfetch.
    destruct maybe_instr as [instr|]; simpl.
    + Check maybe_instr.
    + constructor.
Abort.