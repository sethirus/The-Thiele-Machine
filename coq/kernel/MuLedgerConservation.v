From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.

Require Import Kernel.VMState.
Require Import Kernel.VMStep.
Require Import Kernel.SimulationProof.

(** * Bounded-model µ-ledger conservation *)

(** The virtual machine executes a bounded trace using [run_vm],
    accumulating µ-costs in the [vm_mu] field of the state.  The ledger
    associated to a bounded execution records, for each realised
    instruction, the µ-delta charged by the specification.  This module
    constructs that ledger and proves that every bounded execution
    preserves the conservation law: the µ-accumulator equals the
    initial µ plus the sum of the recorded deltas, and each consecutive
    pair of states differs exactly by the corresponding ledger entry. *)

(** Ledger extraction from bounded executions. *)

Fixpoint ledger_entries (fuel : nat) (trace : list vm_instruction)
  (s : VMState) : list nat :=
  match fuel with
  | 0 => []
  | S fuel' =>
      match nth_error trace s.(vm_pc) with
      | Some instr =>
          instruction_cost instr ::
          ledger_entries fuel' trace (vm_apply s instr)
      | None => []
      end
  end.

Fixpoint bounded_run (fuel : nat) (trace : list vm_instruction)
  (s : VMState) : list VMState :=
  match fuel with
  | 0 => [s]
  | S fuel' =>
      match nth_error trace s.(vm_pc) with
      | Some instr =>
          s :: bounded_run fuel' trace (vm_apply s instr)
      | None => [s]
      end
  end.

Lemma vm_apply_mu :
  forall s instr,
    (vm_apply s instr).(vm_mu) = s.(vm_mu) + instruction_cost instr.
Proof.
  intros s instr.
  destruct instr; simpl; reflexivity.
Qed.

Fixpoint ledger_conserved (states : list VMState) (entries : list nat)
  : Prop :=
  match states, entries with
  | s :: s' :: rest, delta :: entries' =>
      s'.(vm_mu) = s.(vm_mu) + delta /\
      ledger_conserved (s' :: rest) entries'
  | [_], [] => True
  | _, _ => False
  end.

Lemma ledger_conserved_tail :
  forall s states entries,
    ledger_conserved (s :: states) entries ->
    match states, entries with
    | s' :: rest_states, delta :: rest_entries =>
        s'.(vm_mu) = s.(vm_mu) + delta /\
        ledger_conserved (s' :: rest_states) rest_entries
    | [], [] => True
    | _, _ => False
    end.
Proof.
  intros s states entries H.
  destruct states as [|s' rest]; destruct entries as [|delta rest_entries]; simpl in *; auto.
  destruct H as [Hstep Hrest]. split; auto.
Qed.

Lemma bounded_ledger_conservation :
  forall fuel trace s,
    ledger_conserved (bounded_run fuel trace s)
                     (ledger_entries fuel trace s).
Proof.
  induction fuel; intros trace s; simpl.
  - constructor.
  - destruct (nth_error trace (vm_pc s)) as [instr|] eqn:Hfetch; simpl.
    + split.
      * apply vm_apply_mu.
      * apply IHfuel.
    + constructor.
Qed.

Fixpoint ledger_sum (entries : list nat) : nat :=
  match entries with
  | [] => 0
  | delta :: rest => delta + ledger_sum rest
  end.

Lemma run_vm_mu_conservation :
  forall fuel trace s,
    (run_vm fuel trace s).(vm_mu) =
    s.(vm_mu) + ledger_sum (ledger_entries fuel trace s).
Proof.
  induction fuel; intros trace s; simpl.
  - reflexivity.
  - destruct (nth_error trace (vm_pc s)) as [instr|] eqn:Hfetch; simpl.
    + rewrite IHfuel.
      rewrite vm_apply_mu.
      lia.
    + reflexivity.
Qed.

(** Final conservation theorem combining both the cumulative and
    per-step statements. *)

Theorem bounded_model_mu_ledger_conservation :
  forall fuel trace s,
    ledger_conserved (bounded_run fuel trace s)
                     (ledger_entries fuel trace s) /\
    (run_vm fuel trace s).(vm_mu) =
      s.(vm_mu) + ledger_sum (ledger_entries fuel trace s).
Proof.
  intros fuel trace s.
  split.
  - apply bounded_ledger_conservation.
  - apply run_vm_mu_conservation.
Qed.
