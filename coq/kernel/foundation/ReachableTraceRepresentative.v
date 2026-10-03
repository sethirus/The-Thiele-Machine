(** ReachableTraceRepresentative: a trace for every reachable state.

    [generalized_reachable_simulation_exists] (EventGeneralizationTargets.v)
    takes a premise: a function [representative] from VM states to traces
    with [vm_trace_eval (representative (vm_trace_eval t)) = vm_trace_eval t]
    for every trace [t]. EventGeneralization.v proves the proposition for
    any such function. This file builds one, so the premise has an
    inhabitant and the iff holds outright
    ([generalized_reachable_simulation_holds]).

    The construction searches. [nat_to_program] (VMInstructionEncoding.v)
    reaches every trace, since [nat_to_program (program_to_nat t) = t]. For a
    state [s], the representative is the first trace in that enumeration
    that evaluates to [s], or the empty trace when none does.

    VM states have decidable equality ([vm_state_eq_dec],
    VMBoundedDecidability.v), so each number can be checked. The search
    over all numbers is unbounded; the representative uses the choice
    principle that comes with Coq's real numbers,
    [ClassicalDedekindReals.sig_forall_dec], one of the five
    standard-library assumptions the rest of the corpus already rests on. So
    the premise has an inhabitant in Coq with that assumption. The file does
    not give a program that rebuilds a trace from a state. *)

From Coq Require Import List.
(* SAFE: the Reals choice principle sig_forall_dec is the only assumption; it
   is in the standard-library set the corpus already uses. *)
From Coq Require Import Reals.ClassicalDedekindReals.
Import ListNotations.

From Kernel Require Import VMState VMStep VMInstructionEncoding VMBoundedDecidability.
From Kernel Require Import TraceStateDescent EventGeneralizationTargets
                           EventGeneralization.

(** [misses s n]: the trace numbered [n] does not evaluate to [s]. *)
Definition misses (s : VMState) (n : nat) : Prop :=
  vm_trace_eval (nat_to_program n) <> s.

Definition misses_dec (s : VMState) (n : nat) : {misses s n} + {~ misses s n}.
Proof.
  unfold misses.
  destruct (vm_state_eq_dec (vm_trace_eval (nat_to_program n)) s) as [Heq | Hne].
  - right. intro H. exact (H Heq).
  - left. exact Hne.
Defined.

(** The first numbered trace that reaches [s], or the empty trace. *)
Definition reachable_trace_representative (s : VMState) : list vm_instruction :=
  match sig_forall_dec (misses s) (misses_dec s) with
  | inleft (exist _ n _) => nat_to_program n
  | inright _ => []
  end.

Theorem reachable_trace_representative_correct : forall t,
  vm_trace_eval (reachable_trace_representative (vm_trace_eval t)) = vm_trace_eval t.
Proof.
  intro t. unfold reachable_trace_representative.
  destruct (sig_forall_dec (misses (vm_trace_eval t)) (misses_dec (vm_trace_eval t)))
    as [[n Hn] | Hall].
  - unfold misses in Hn.
    destruct (vm_state_eq_dec (vm_trace_eval (nat_to_program n)) (vm_trace_eval t))
      as [Heq | Hne]; [exact Heq | contradiction].
  - exfalso. apply (Hall (program_to_nat t)). unfold misses.
    rewrite nat_to_program_program_to_nat. reflexivity.
Qed.

(** The premise of [generalized_reachable_simulation_exists] is inhabited:
    some function picks, for every reachable state, a trace that reaches
    it. *)
Corollary reachable_representative_exists :
  exists representative : VMState -> list vm_instruction,
    forall t, vm_trace_eval (representative (vm_trace_eval t)) = vm_trace_eval t.
Proof.
  exists reachable_trace_representative.
  exact reachable_trace_representative_correct.
Qed.

(** generalized_reachable_simulation_holds. For every reading [E],
    certification-cost machine [M] and base state, a reachable event
    simulation of the VM into [M] exists exactly when two traces with the
    same VM endpoint have the same target endpoint, and the reading of every
    trace's VM endpoint equals the certification flag of its target
    endpoint. *)
Theorem generalized_reachable_simulation_holds : forall E M base,
  inhabited (ReachableEventSimulation E M base) <->
  trace_fiber_compatible M base /\ event_trace_compatible E M base.
Proof.
  exact (eg_proves_generalized_reachable_simulation_exists
           reachable_trace_representative reachable_trace_representative_correct).
Qed.
