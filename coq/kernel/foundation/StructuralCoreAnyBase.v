(** StructuralCoreAnyBase: the record axis over any base.

    [StructuralCoreCover] compares machines through a cover of one
    reference machine. This file fixes none. A base is any deterministic,
    record-free machine: a Turing machine, a RAM, a reversible machine, L. Machines on
    different bases are not compared; a machine that multiplies unbounded
    numbers in one step and a Turing machine differ in cost, not in records.

    An extension of a base B is any record-carrying machine M with a map
    down to B that commutes with every step, preserves halting, and reaches
    every starting state of B. M may carry any hidden state beyond B. It is
    honest when its ledger is monotone, A2 holds, the record never switches
    off, some reachable step writes it, and the record is driven by the
    computation: its next value is a function of the base state and its own
    current value. A record run by a hidden clock is not driven by the
    computation.

    The conjecture is a factorization. For every honest extension there is
    one event h of the base such that the base state and the record evolve
    exactly as a latch of h: the record switches on at the first base state
    where h holds and never switches off. Everything else M carries shows up
    only in its ledger.

    A pair of permanent records is stated the same way: the pair evolves as
    two latches, each of whose events may read the other record. *)

From Kernel Require Import StructuralCore StructuralCoreCover.

(** * Bases and extensions *)

Record BaseMachine : Type := {
  b_state : Type;
  b_next : b_state -> b_state;
  b_init : b_state -> Prop;
  b_halted : b_state -> Prop
}.

Record BaseCover (M : RCM) (B : BaseMachine) : Type := {
  base_state : rc_state M -> b_state B;
  base_initial : forall m, rc_init M m -> b_init B (base_state m);
  base_surjective_initial : forall b, b_init B b ->
    exists m, rc_init M m /\ base_state m = b;
  base_step : forall m, base_state (rc_next M m) = b_next B (base_state m);
  base_halted : forall m, rc_halted M m <-> b_halted B (base_state m)
}.

(** The record's next value depends only on the base state and itself. *)
Definition computation_driven (M : RCM) (B : BaseMachine) (C : BaseCover M B)
  : Prop :=
  exists f : b_state B -> bool -> bool,
    forall m, rc_cert M (rc_next M m) = f (base_state M B C m) (rc_cert M m).

Definition HonestBaseExtension (M : RCM) (B : BaseMachine) (C : BaseCover M B)
  : Prop :=
  computation_driven M B C /\ ledger_carried M /\ rc_a2 M /\
  record_permanent M /\ reachable_record_write M.

(** * The latch *)

Definition latch_next (B : BaseMachine) (h : b_state B -> bool)
    (x : b_state B * bool) : b_state B * bool :=
  (b_next B (fst x), orb (snd x) (h (fst x))).

(** The base state and the record of M evolve exactly as the latch of h. *)
Definition latch_factorization (M : RCM) (B : BaseMachine) (C : BaseCover M B)
    (h : b_state B -> bool) : Prop :=
  forall m,
    (base_state M B C (rc_next M m), rc_cert M (rc_next M m)) =
    latch_next B h (base_state M B C m, rc_cert M m).

Definition record_axis_is_latch : Prop :=
  forall M B C, HonestBaseExtension M B C ->
    exists h, latch_factorization M B C h.

(** * Two records *)

Definition pair_permanent (M : RCM) (c : rc_state M -> bool) : Prop :=
  forall m, c m = true -> c (rc_next M m) = true.

(** A step that switches either record on costs at least one. *)
Definition pair_a2 (M : RCM) (c1 c2 : rc_state M -> bool) : Prop :=
  forall m,
    (c1 m = false /\ c1 (rc_next M m) = true) \/
    (c2 m = false /\ c2 (rc_next M m) = true) ->
    step_cost M m >= 1.

Definition pair_computation_driven (M : RCM) (B : BaseMachine) (C : BaseCover M B)
    (c1 c2 : rc_state M -> bool) : Prop :=
  exists f : b_state B -> bool -> bool -> bool * bool,
    forall m, (c1 (rc_next M m), c2 (rc_next M m)) =
              f (base_state M B C m) (c1 m) (c2 m).

Definition HonestBasePairExtension (M : RCM) (B : BaseMachine) (C : BaseCover M B)
    (c1 c2 : rc_state M -> bool) : Prop :=
  pair_computation_driven M B C c1 c2 /\ ledger_carried M /\ pair_a2 M c1 c2 /\
  pair_permanent M c1 /\ pair_permanent M c2.

(** Two latches, each of whose events may read the other record. *)
Definition pair_latch_factorization (M : RCM) (B : BaseMachine) (C : BaseCover M B)
    (c1 c2 : rc_state M -> bool) (h1 h2 : b_state B -> bool -> bool) : Prop :=
  forall m,
    c1 (rc_next M m) = orb (c1 m) (h1 (base_state M B C m) (c2 m)) /\
    c2 (rc_next M m) = orb (c2 m) (h2 (base_state M B C m) (c1 m)).

Definition record_pair_is_two_latches : Prop :=
  forall M B C c1 c2, HonestBasePairExtension M B C c1 c2 ->
    exists h1 h2, pair_latch_factorization M B C c1 c2 h1 h2.
