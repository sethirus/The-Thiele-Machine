(** Cross-base equivalence that permits instruction stuttering. *)

From Coq Require Import List Arith.PeanoNat.
From Kernel Require Import StructuralCoreAnyBase Kernel KernelTM.

Definition base_run (B : BaseMachine) (n : nat) (s : b_state B) : b_state B :=
  Nat.iter n (b_next B) s.

Definition weak_base_equiv
    (B1 B2 : BaseMachine) (O : Type)
    (obs1 : b_state B1 -> O) (obs2 : b_state B2 -> O) : Prop :=
  exists R : b_state B1 -> b_state B2 -> Prop,
    (forall x, b_init B1 x -> exists y, b_init B2 y /\ R x y) /\
    (forall y, b_init B2 y -> exists x, b_init B1 x /\ R x y) /\
    forall x y, R x y ->
      obs1 x = obs2 y /\
      (b_halted B1 x <-> b_halted B2 y) /\
      (exists n, R (b_next B1 x) (base_run B2 n y)) /\
      (exists n, R (base_run B1 n x) (b_next B2 y)).

Definition record_axis_is_latch_on (B : BaseMachine) : Prop :=
  forall (M : StructuralCore.RCM) (C : BaseCover M B),
    HonestBaseExtension M B C -> exists h, latch_factorization M B C h.

Definition weak_base_equiv_refl : Prop :=
  forall (B : BaseMachine) (O : Type) (obs : b_state B -> O),
    weak_base_equiv B B O obs obs.

Definition weak_base_equiv_sym : Prop :=
  forall (B1 B2 : BaseMachine) (O : Type)
         (obs1 : b_state B1 -> O) (obs2 : b_state B2 -> O),
    weak_base_equiv B1 B2 O obs1 obs2 ->
    weak_base_equiv B2 B1 O obs2 obs1.

(** The record axis property is parametric in the base, so the equivalence
    premise is not needed to establish the property on either side. *)
Definition weak_equiv_preserves_record_latch : Prop :=
  forall (B1 B2 : BaseMachine) (O : Type)
         (obs1 : b_state B1 -> O) (obs2 : b_state B2 -> O),
    weak_base_equiv B1 B2 O obs1 obs2 ->
    (record_axis_is_latch_on B1 <-> record_axis_is_latch_on B2).

(** The Turing-machine kernel as a base. *)
Definition tm_base (p : program) : BaseMachine := {|
  b_state := state;
  b_next := step_tm p;
  b_init := fun _ => True;
  b_halted := fun s => fetch p s = T_Halt
|}.

Definition record_axis_is_latch_on_tm : Prop :=
  forall p, record_axis_is_latch_on (tm_base p).
