(** StructuralCore: record-carrying machines, adequacy, and core equivalence.

    Three definitions, stated over an arbitrary deterministic machine: what a
    record-carrying machine is, when one is adequate, and when two cores are
    the same. The definitions are given in their weak form. Instances live in
    the files that use them.

    - A record-carrying machine is a deterministic machine with a set of
      starting states, a yes/no record reading, a ledger carried in the
      state, and a halting observation.
    - It is adequate when the ledger never goes down, a step that switches
      the reading on raises the ledger by at least one (A2), some run from a
      starting state reaches a certified state (it carries a record at all),
      and every two-counter halting instance has some starting state whose
      observed halt agrees with that instance. This last clause is only
      existential halting-problem coverage. It supplies neither a uniform
      effective input encoding nor a reverse simulation, and is not a claim
      of Turing equivalence.
    - Two machines have equivalent cores when some relation between their
      states relates every starting state of each to a starting state of the
      other, and related states agree on the reading, price their next step
      the same, and step to related states. This is bisimulation
      up to the reading and the ledger's increments. The relation need not be
      a function, so extra state one machine keeps, such as its history, is
      quotiented out. *)

From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.
From Undecidability.MinskyMachines Require Import MM2.

(** * Definitions *)

Record RCM : Type := {
  rc_state : Type;
  rc_next : rc_state -> rc_state;
  rc_init : rc_state -> Prop;
  rc_cert : rc_state -> bool;
  rc_mu : rc_state -> nat;
  rc_halted : rc_state -> Prop
}.

Definition rc_run (M : RCM) (n : nat) (s : rc_state M) : rc_state M :=
  Nat.iter n (rc_next M) s.

Definition step_cost (M : RCM) (s : rc_state M) : nat :=
  rc_mu M (rc_next M s) - rc_mu M s.

Definition ledger_carried (M : RCM) : Prop :=
  forall s, rc_mu M s <= rc_mu M (rc_next M s).

Definition rc_a2 (M : RCM) : Prop :=
  forall s, rc_cert M s = false -> rc_cert M (rc_next M s) = true -> step_cost M s >= 1.

Definition carries_record (M : RCM) : Prop :=
  exists s n, rc_init M s /\ rc_cert M (rc_run M n s) = true.

(** Weak, per-instance halting coverage. The existential start state may
    depend on the MM2 problem without being supplied by a uniform effective
    encoder; no simulation in either direction is part of this definition. *)
Definition halting_problem_coverage (M : RCM) : Prop :=
  forall P : MM2_PROBLEM,
    exists s0, rc_init M s0 /\ (MM2_HALTING P <-> exists n, rc_halted M (rc_run M n s0)).

Definition Adequate (M : RCM) : Prop :=
  ledger_carried M /\ rc_a2 M /\ carries_record M /\ halting_problem_coverage M.

Definition core_bisim (M N : RCM) (R : rc_state M -> rc_state N -> Prop) : Prop :=
  (forall m, rc_init M m -> exists n, rc_init N n /\ R m n) /\
  (forall n, rc_init N n -> exists m, rc_init M m /\ R m n) /\
  (forall m n, R m n ->
     rc_cert M m = rc_cert N n /\
     step_cost M m = step_cost N n /\
     R (rc_next M m) (rc_next N n)).

Definition core_equiv (M N : RCM) : Prop := exists R, core_bisim M N R.
