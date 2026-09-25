(** This file defines the abstract trace-weight interface used by the
    corresponding theorems. The interface is not tied to the VM's [vm_mu]
    field or to [instruction_cost]. A theorem that needs one of these laws
    receives it as an explicit premise. *)

From Coq Require Import List Lia.

From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import KernelPhysics.

Import ListNotations.

Definition Trace := list vm_instruction.
Definition Weight := Trace -> nat.

(** The trace is a list of VM instructions and a weight is a natural-number
    function on traces. [weight_empty] fixes the empty trace, [weight_sequential]
    fixes concatenation, and [weight_disjoint_commutes] fixes the order of
    traces with mutually disjoint causal cones. These definitions do not give
    the weight physical units or a spacetime interpretation. *)

Definition weight_empty (w : Weight) : Prop :=
  w [] = 0.

Definition weight_sequential (w : Weight) : Prop :=
  forall t1 t2, w (t1 ++ t2) = w t1 + w t2.

Definition disjoint_list {A : Type} (xs ys : list A) : Prop :=
  forall x, In x xs -> ~ In x ys.

Definition trace_disjoint (t1 t2 : Trace) : Prop :=
  disjoint_list (causal_cone t1) (causal_cone t2) /\
  disjoint_list (causal_cone t2) (causal_cone t1).

(** This commutation law is an optional extension. The bundled [weight_laws]
    record includes it, while results that need only the empty-trace and
    sequential laws can state those two premises directly. [trace_disjoint]
    checks both directions because causal cones need not be symmetric. *)
Definition weight_disjoint_commutes (w : Weight) : Prop :=
  forall t1 t2,
    trace_disjoint t1 t2 ->
    w (t1 ++ t2) = w (t2 ++ t1).

Definition weight_laws (w : Weight) : Prop :=
  weight_empty w /\ weight_sequential w /\ weight_disjoint_commutes w.

(** These are optional algebraic extensions, not premises of No Free Insight.
    [singleton_uniform] gives every singleton trace the same weight. The VM's
    [instruction_cost] does not satisfy that property because several opcodes
    have specialized costs. [unit_normalization] fixes one scale by assigning
    weight one to [instr_halt 0]. Any theorem using either property must name
    it as a premise. *)

(** Singleton-uniformity: all single-step traces have the same weight.
    This is a purely algebraic symmetry/identification principle. *)
Definition singleton_uniform (w : Weight) : Prop :=
  forall i j, w [i] = w [j].

(** Unit normalization: fixes the overall scale by pinning one singleton. *)
Definition unit_normalization (w : Weight) : Prop :=
  w [instr_halt 0] = 1.

(** [finite_region_equiv_class] is an explicit finite-cover premise for the VM's region observation. This file defines the predicate; it does not prove a physical finite-dimensionality claim. *)

Definition region_equiv (s1 s2 : VMState) : Prop :=
  forall mid, ObservableRegion s1 mid = ObservableRegion s2 mid.

Definition finite_region_equiv_class (s : VMState) : Prop :=
  exists l : list VMState,
    NoDup l /\
    forall s', region_equiv s s' -> In s' l.
