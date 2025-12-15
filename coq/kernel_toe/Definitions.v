From Coq Require Import List Lia.

From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import KernelPhysics.

Import ListNotations.

(** * KernelTOE: minimal, explicit interfaces

    This folder is intended to be a sealed dependency cone for the TOE
    “maximal closure + minimal no-go” deliverables.
*)

Definition Trace := list vm_instruction.
Definition Weight := Trace -> nat.

(** ** Explicit minimal laws (no named predicate ambiguity)

    These are the only laws used in the no-go results. *)

Definition weight_empty (w : Weight) : Prop :=
  w [] = 0.

Definition weight_sequential (w : Weight) : Prop :=
  forall t1 t2, w (t1 ++ t2) = w t1 + w t2.

Definition disjoint_list {A : Type} (xs ys : list A) : Prop :=
  forall x, In x xs -> ~ In x ys.

Definition trace_disjoint (t1 t2 : Trace) : Prop :=
  disjoint_list (causal_cone t1) (causal_cone t2) /\
  disjoint_list (causal_cone t2) (causal_cone t1).

(** Optional commutation law (used as an explicit “tensor-like” commutation).
    Note: we only demand commutation for traces whose causal targets are disjoint. *)
Definition weight_disjoint_commutes (w : Weight) : Prop :=
  forall t1 t2,
    trace_disjoint t1 t2 ->
    w (t1 ++ t2) = w (t2 ++ t1).

Definition weight_laws (w : Weight) : Prop :=
  weight_empty w /\ weight_sequential w /\ weight_disjoint_commutes w.

(** ** A menu of minimal extensions (“extra structure”) *)

(** Singleton-uniformity: all single-step traces have the same weight.
    This is a purely algebraic symmetry/identification principle. *)
Definition singleton_uniform (w : Weight) : Prop :=
  forall i j, w [i] = w [j].

(** Unit normalization: fixes the overall scale by pinning one singleton. *)
Definition unit_normalization (w : Weight) : Prop :=
  w [instr_halt 0] = 1.

(** ** Observational finiteness (explicit coarse-graining / finite measurement algebra)

    This is a constructive “finite enumeration” notion: a finite list of distinct
    microstates that covers the region-equivalence class.
*)

Definition region_equiv (s1 s2 : VMState) : Prop :=
  forall mid, ObservableRegion s1 mid = ObservableRegion s2 mid.

Definition finite_region_equiv_class (s : VMState) : Prop :=
  exists l : list VMState,
    NoDup l /\
    forall s', region_equiv s s' -> In s' l.
