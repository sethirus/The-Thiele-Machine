(** Exact finite-weight targets for probabilistic record machines. *)

(* SCOPE NOTE: standalone proof scope. This finite-weight countermodel is
   substrate-independent and intentionally imports no machine semantics. *)

From Coq Require Import List Bool Arith.PeanoNat.
Import ListNotations.

Definition weighted_kernel := bool -> list (nat * bool).
Definition branch_charge := bool -> bool -> nat.

Definition positive_kernel (k : weighted_kernel) : Prop :=
  forall b w b', In (w, b') (k b) -> w > 0.

Definition total_kernel (k : weighted_kernel) : Prop :=
  forall b, k b <> [].

Definition monotone_kernel (k : weighted_kernel) : Prop :=
  forall w b', In (w, b') (k true) -> b' = true.

Definition kernel_writes_priced (k : weighted_kernel) (c : branch_charge) : Prop :=
  forall w, In (w, true) (k false) -> c false true >= 1.

Definition honest_probabilistic_record
    (k : weighted_kernel) (c : branch_charge) : Prop :=
  positive_kernel k /\ total_kernel k /\ monotone_kernel k /\
  kernel_writes_priced k c.

(** A deterministic latch cannot in general explain both branches from the
    same current observation. *)
Definition deterministic_latch_handles_branching : Prop :=
  forall k c, honest_probabilistic_record k c ->
    exists h : bool -> bool,
      forall b w b', In (w, b') (k b) -> b' = orb b (h b).

Definition kernel_support (k : weighted_kernel) (b b' : bool) : Prop :=
  exists w, In (w, b') (k b).

(** “Up to schedule” deliberately forgets branch weights. *)
Definition same_probabilistic_schedule
    (k1 k2 : weighted_kernel) (c1 c2 : branch_charge) : Prop :=
  (forall b b', kernel_support k1 b b' <-> kernel_support k2 b b') /\
  (forall b b', c1 b b' = c2 b b').

Definition probability_preserving_equivalence
    (k1 k2 : weighted_kernel) (c1 c2 : branch_charge) : Prop :=
  (forall b, k1 b = k2 b) /\ (forall b b', c1 b b' = c2 b b').

Definition schedule_determines_probabilities : Prop :=
  forall k1 k2 c1 c2,
    honest_probabilistic_record k1 c1 ->
    honest_probabilistic_record k2 c2 ->
    same_probabilistic_schedule k1 k2 c1 c2 ->
    probability_preserving_equivalence k1 k2 c1 c2.

Definition probability_preserving_equivalence_reflexive : Prop :=
  forall k c, probability_preserving_equivalence k k c c.
