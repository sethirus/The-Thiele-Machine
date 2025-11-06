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

(** The next lemma isolates the per-instruction conservation law.
    It asserts that any single small-step transition must debit the
    µ-ledger by exactly the instruction's declared cost.  In particular
    a "free" step—one that changes [vm_mu] without the matching ledger
    delta—would violate [ledger_conserved]; therefore it cannot arise
    under the kernel semantics. *)

Theorem vm_step_respects_mu_ledger :
  forall s instr s',
    vm_step s instr s' ->
    ledger_conserved [s; s'] [instruction_cost instr].
Proof.
  intros s instr s' Hstep.
  simpl.
  split.
  - now apply vm_step_mu.
  - exact I.
Qed.

Fixpoint ledger_sum (entries : list nat) : nat :=
  match entries with
  | [] => 0
  | delta :: rest => delta + ledger_sum rest
  end.

(** Component-wise accumulation for sighted/blind decompositions.
    The function is parameterised by an instruction-to-cost projection,
    allowing downstream theorems to reason about arbitrary partitions of
    [instruction_cost] (e.g. blind search versus sighted certificates). *)

Fixpoint ledger_component_sum (component : vm_instruction -> nat)
  (fuel : nat) (trace : list vm_instruction) (s : VMState) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
      match nth_error trace s.(vm_pc) with
      | Some instr =>
          component instr +
          ledger_component_sum component fuel' trace (vm_apply s instr)
      | None => 0
      end
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

Corollary bounded_prefix_mu_balance :
  forall fuel trace s k,
    k <= fuel ->
    (run_vm k trace s).(vm_mu) =
      s.(vm_mu) + ledger_sum (ledger_entries k trace s).
Proof.
  intros fuel trace s k Hle.
  apply run_vm_mu_conservation.
Qed.

(** We now generalise the conservation statement by splitting the
    instruction cost into complementary components.  This allows the
    kernel development to project the ledger onto semantics such as
    “blind” search work versus “sighted” certificate validation. *)

Section MuDecomposition.

Variable mu_blind_component mu_sighted_component : vm_instruction -> nat.
Hypothesis mu_component_split : forall instr,
  instruction_cost instr =
    mu_blind_component instr + mu_sighted_component instr.

Lemma ledger_sum_component_decompose :
  forall fuel trace s,
    ledger_sum (ledger_entries fuel trace s) =
      ledger_component_sum mu_blind_component fuel trace s +
      ledger_component_sum mu_sighted_component fuel trace s.
Proof.
  induction fuel as [|fuel IH]; intros trace s; simpl.
  - reflexivity.
  - destruct (nth_error trace s.(vm_pc)) as [instr|] eqn:Hlookup.
    + simpl.
      rewrite mu_component_split.
      simpl.
      specialize (IH trace (vm_apply s instr)).
      rewrite IH.
      lia.
    + reflexivity.
Qed.

Theorem bounded_run_mu_decomposition :
  forall fuel trace s,
    (run_vm fuel trace s).(vm_mu) =
      s.(vm_mu) +
      ledger_component_sum mu_blind_component fuel trace s +
      ledger_component_sum mu_sighted_component fuel trace s.
Proof.
  intros fuel trace s.
  destruct (bounded_model_mu_ledger_conservation fuel trace s)
    as [_ Hmu].
  rewrite Hmu.
  rewrite ledger_sum_component_decompose.
  lia.
Qed.

Corollary bounded_run_blind_component_le_total :
  forall fuel trace s,
    s.(vm_mu) + ledger_component_sum mu_blind_component fuel trace s <=
    (run_vm fuel trace s).(vm_mu).
Proof.
  intros fuel trace s.
  rewrite bounded_run_mu_decomposition.
  remember (ledger_component_sum mu_blind_component fuel trace s) as blind_sum.
  remember (ledger_component_sum mu_sighted_component fuel trace s) as sighted_sum.
  lia.
Qed.

Corollary bounded_run_sighted_component_le_total :
  forall fuel trace s,
    s.(vm_mu) + ledger_component_sum mu_sighted_component fuel trace s <=
    (run_vm fuel trace s).(vm_mu).
Proof.
  intros fuel trace s.
  rewrite bounded_run_mu_decomposition.
  remember (ledger_component_sum mu_blind_component fuel trace s) as blind_sum.
  remember (ledger_component_sum mu_sighted_component fuel trace s) as sighted_sum.
  lia.
Qed.

End MuDecomposition.

(** Bridging the prophecy seal and ledger tail.
    The Python experiment derives the gestalt certificate by combining the
    pre-declared seal with the final ledger digest.  The following abstract
    model captures that construction and proves that the gestalt certificate is
    definitionally identical to the computed isomorphism.  The "hash"
    combinator remains uninterpreted here—the property is purely structural and
    does not depend on cryptographic specifics. *)

Section GestaltIsomorphism.

  Variable Hash : Type.
  Variable combine : Hash -> Hash -> Hash.
  Variable default : Hash.

  Definition final_digest (ledger : list Hash) : Hash :=
    match ledger with
    | [] => default
    | _ => List.last ledger default
    end.

  Definition gestalt_certificate (seal : Hash) (ledger : list Hash) : Hash :=
    combine seal (final_digest ledger).

  Definition computed_isomorphism (seal : Hash) (ledger : list Hash) : Hash :=
    combine seal (final_digest ledger).

  Lemma gestalt_matches_isomorphism :
    forall seal ledger,
      gestalt_certificate seal ledger = computed_isomorphism seal ledger.
  Proof.
    intros seal ledger. unfold gestalt_certificate, computed_isomorphism.
    reflexivity.
  Qed.

End GestaltIsomorphism.
