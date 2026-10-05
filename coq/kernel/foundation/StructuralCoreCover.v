(** StructuralCoreCover: computational covers and record observations.

    The strong form of the definitions in [StructuralCore].

    A cover of one machine by another projects every source step to one
    reference step, preserves halting, and covers all reference starting
    states. This states both directions of the computational comparison
    with an explicit projection. It does not identify arbitrary machines
    with Turing machines by a one-way halting reduction.

    A record is permanent when a raised reading stays raised, and it is
    reachably written when some run from a starting state takes the reading
    from false to true. Initial certification alone does not count as a
    write. The record may be implemented with additional state. No physical
    cost calibration is assumed.

    The observed core keeps the certification reading, ledger balance,
    step cost, and halting observation. Bisimulation may discard retained
    history. Ledger units and the starting balance are part of the
    observation; no rescaling or stuttering is implicit. *)

From Coq Require Import Arith.PeanoNat.
From Kernel Require Import StructuralCore.

Record ComputationalCover (M N : RCM) : Type := {
  cover_state : rc_state M -> rc_state N;
  cover_initial : forall s, rc_init M s -> rc_init N (cover_state s);
  cover_surjective_initial : forall t, rc_init N t ->
    exists s, rc_init M s /\ cover_state s = t;
  cover_step : forall s,
    cover_state (rc_next M s) = rc_next N (cover_state s);
  cover_halted : forall s, rc_halted M s <-> rc_halted N (cover_state s)
}.

Definition record_permanent (M : RCM) : Prop :=
  forall s, rc_cert M s = true -> rc_cert M (rc_next M s) = true.

Definition reachable_record_write (M : RCM) : Prop :=
  exists s n, rc_init M s /\
    rc_cert M (rc_run M n s) = false /\
    rc_cert M (rc_next M (rc_run M n s)) = true.

Definition observed_core_bisim (M N : RCM)
    (R : rc_state M -> rc_state N -> Prop) : Prop :=
  (forall m, rc_init M m -> exists n, rc_init N n /\ R m n) /\
  (forall n, rc_init N n -> exists m, rc_init M m /\ R m n) /\
  (forall m n, R m n ->
     rc_cert M m = rc_cert N n /\
     rc_mu M m = rc_mu N n /\
     (rc_halted M m <-> rc_halted N n) /\
     step_cost M m = step_cost N n /\
     R (rc_next M m) (rc_next N n)).

Definition observed_core_equiv (M N : RCM) : Prop :=
  exists R, observed_core_bisim M N R.
