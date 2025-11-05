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

Lemma bounded_run_head :
  forall fuel trace s,
    exists rest, bounded_run fuel trace s = s :: rest.
Proof.
  induction fuel as [|fuel IH]; intros trace s; simpl.
  - exists []. reflexivity.
  - destruct (nth_error trace s.(vm_pc)) as [instr|] eqn:Hlookup.
    + exists (bounded_run fuel trace (vm_apply s instr)). reflexivity.
    + exists []. reflexivity.
Qed.

Lemma vm_apply_mu :
  forall s instr,
    (vm_apply s instr).(vm_mu) = s.(vm_mu) + instruction_cost instr.
Proof.
  intros s instr.
  destruct instr; simpl;
    try reflexivity;
    try (destruct (graph_pnew _ _) as [graph' mid] eqn:?; simpl; reflexivity);
    try (destruct (graph_psplit _ _ _ _) as [[[graph' left_id] right_id]|] eqn:?; simpl; reflexivity);
    try (destruct (graph_pmerge _ _ _) as [[graph' merged_id]|] eqn:?; simpl; reflexivity);
    try (destruct (String.eqb _ _) eqn:?; simpl; reflexivity);
    try (destruct cert;
         simpl;
         try (destruct (check_model _ _) eqn:?; simpl; reflexivity);
         try (destruct (check_lrat _ _) eqn:?; simpl; reflexivity)).
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
  destruct states as [|s' rest].
  - destruct entries as [|delta rest_entries]; simpl in *.
    + exact I.
    + now destruct H.
  - destruct entries as [|delta rest_entries]; simpl in *.
    + now destruct H.
    + destruct H as [Hstep Hrest]. split; auto.
Qed.

Fixpoint ledger_sum (entries : list nat) : nat :=
  match entries with
  | [] => 0
  | delta :: rest => delta + ledger_sum rest
  end.

(** Final conservation theorem combining both the cumulative and
    per-step statements. *)

Theorem bounded_model_mu_ledger_conservation :
  forall fuel trace s,
    ledger_conserved (bounded_run fuel trace s)
                     (ledger_entries fuel trace s) /\
  (run_vm fuel trace s).(vm_mu) =
    s.(vm_mu) + ledger_sum (ledger_entries fuel trace s).
Proof.
  induction fuel as [|fuel IH]; intros trace s; simpl.
  - split; [exact I | rewrite Nat.add_0_r; reflexivity].
  - destruct (nth_error trace s.(vm_pc)) as [instr|] eqn:Hlookup; simpl.
    + destruct (IH trace (vm_apply s instr)) as [IH_ledger IH_run].
      destruct (bounded_run_head fuel trace (vm_apply s instr)) as [rest Hrun].
      simpl.
      rewrite Hrun in IH_ledger.
      rewrite Hrun.
      split; [split; [apply vm_apply_mu | exact IH_ledger]
            | rewrite IH_run; rewrite vm_apply_mu; lia].
    + split; [exact I | rewrite Nat.add_0_r; reflexivity].
Qed.

Corollary bounded_ledger_conservation :
  forall fuel trace s,
    ledger_conserved (bounded_run fuel trace s)
                     (ledger_entries fuel trace s).
Proof.
  intros fuel trace s.
  apply (proj1 (bounded_model_mu_ledger_conservation fuel trace s)).
Qed.

Corollary run_vm_mu_conservation :
  forall fuel trace s,
    (run_vm fuel trace s).(vm_mu) =
    s.(vm_mu) + ledger_sum (ledger_entries fuel trace s).
Proof.
  intros fuel trace s.
  apply (proj2 (bounded_model_mu_ledger_conservation fuel trace s)).
Qed.
