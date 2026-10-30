(** StructuralCore: record-carrying machines and core equivalence.

    Two definitions, stated over an arbitrary deterministic machine: what a
    record-carrying machine is, and when two cores are the same. The definitions are given in their weak form. Instances live in
    the files that use them.

    - A record-carrying machine is a deterministic machine with a set of
      starting states, a yes/no record reading, a ledger carried in the
      state, and a halting observation.
    - It carries its ledger when the ledger never goes down, obeys A2 when a
      step that switches the reading on raises the ledger by at least one,
      and carries a record when some run from a starting state reaches a
      certified state.
    - Two machines have equivalent cores when some relation between their
      states relates every starting state of each to a starting state of the
      other, and related states agree on the reading, price their next step
      the same, and step to related states. This is bisimulation
      up to the reading and the ledger's increments. The relation need not be
      a function, so extra state one machine keeps, such as its history, is
      quotiented out. *)

From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.

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

Definition core_bisim (M N : RCM) (R : rc_state M -> rc_state N -> Prop) : Prop :=
  (forall m, rc_init M m -> exists n, rc_init N n /\ R m n) /\
  (forall n, rc_init N n -> exists m, rc_init M m /\ R m n) /\
  (forall m n, R m n ->
     rc_cert M m = rc_cert N n /\
     step_cost M m = step_cost N n /\
     R (rc_next M m) (rc_next N n)).

Definition core_equiv (M N : RCM) : Prop := exists R, core_bisim M N R.
