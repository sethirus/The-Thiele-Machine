(** EventSwapCore: the VM's main results, with certification replaced by
    another reading of the VM state.

    A reading is a Boolean function of VM states. It is permanent when no
    step switches it off, written when some step switches it on, and
    latchable when both hold. Certification is one latchable reading.

    For a reading [E], five of the VM's main results are stated with [E] in
    place of certification:

    - [priced]: every step that switches [E] on costs at least one;
    - [hidden_from_forget]: no function of the [forget] window returns [E];
    - [hidden_from_bare]: no function of [bare_observable] returns [E];
    - [bare_price_inexact] and [forget_price_inexact]: no price read off the
      window meets the floor for [E] and never overcharges.

    [swap_preserves_main_results] says all five hold for every latchable
    reading. [certification_main_results] says they hold for certification.
    The last five definitions generalize each result on its own. This file
    only states them. *)

From Coq Require Import List Bool Arith.PeanoNat.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.
From Kernel Require Import BlindnessRepresentation ProjectionNonExistence.
From Kernel Require Import ShadowPricing.

Definition Reading : Type := VMState -> bool.

Definition permanent_reading (E : Reading) : Prop :=
  forall s i, E s = true -> E (vm_apply s i) = true.

Definition written (E : Reading) : Prop :=
  exists s i, E s = false /\ E (vm_apply s i) = true.

Definition latchable (E : Reading) : Prop := permanent_reading E /\ written E.

Definition priced (E : Reading) : Prop :=
  forall s i, E s = false -> E (vm_apply s i) = true -> instruction_cost i >= 1.

Definition hidden_from_forget (E : Reading) : Prop :=
  ~ exists f : TMSnapshot -> bool, forall s, f (forget s) = E s.

Definition hidden_from_bare (E : Reading) : Prop :=
  ~ exists f : BareTMObservable -> bool, forall s, f (bare_observable s) = E s.

Definition bare_price_inexact (E : Reading) : Prop :=
  forall price : BareTMObservable -> BareTMObservable -> nat,
    ~ (meets_floor vm_apply E
         (shadow_cost vm_apply bare_observable price) /\
       never_overcharges vm_apply E
         (shadow_cost vm_apply bare_observable price)).

Definition forget_price_inexact (E : Reading) : Prop :=
  forall price : TMSnapshot -> TMSnapshot -> nat,
    ~ (meets_floor vm_apply E
         (shadow_cost vm_apply forget price) /\
       never_overcharges vm_apply E
         (shadow_cost vm_apply forget price)).

Definition main_results (E : Reading) : Prop :=
  priced E /\ hidden_from_forget E /\ hidden_from_bare E /\
  bare_price_inexact E /\ forget_price_inexact E.

Definition swap_preserves_main_results : Prop :=
  forall E, latchable E -> main_results E.

Definition certification_reading : Reading := fun s => vm_certified s.

Definition certification_main_results : Prop :=
  latchable certification_reading /\ main_results certification_reading.

(** The five results, each generalized on its own to every latchable
    reading. *)

Definition pricing_generalizes : Prop := forall E, latchable E -> priced E.

Definition forget_hiding_generalizes : Prop :=
  forall E, latchable E -> hidden_from_forget E.

Definition bare_hiding_generalizes : Prop :=
  forall E, latchable E -> hidden_from_bare E.

Definition bare_inexactness_generalizes : Prop :=
  forall E, latchable E -> bare_price_inexact E.

Definition forget_inexactness_generalizes : Prop :=
  forall E, latchable E -> forget_price_inexact E.
