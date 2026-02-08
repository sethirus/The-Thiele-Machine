From Coq Require Import List Lia.

From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import KernelPhysics.

Import ListNotations.

(** * KernelTOE: minimal, explicit interfaces

    WHY THIS FILE EXISTS:
    I claim the no-go results (No Free Insight, closure theorems, physical
    constant derivations) hold for ANY weight function satisfying these laws,
    not just the specific μ-cost implementation. This file defines the minimal
    abstract interface.

    By sealing the dependency cone here, I ensure no hidden assumptions leak in.
    Every law used in proofs appears explicitly in this file. No "named predicate
    ambiguity" - if a theorem relies on weight_sequential, it says so.

    FALSIFICATION: Find a weight function satisfying these laws but violating
    No Free Insight. Or show the laws are inconsistent (no such function exists).
    Or prove a no-go result without using any law from this file.

    This folder is intended to be a sealed dependency cone for the TOE
    "maximal closure + minimal no-go" deliverables.
*)

Definition Trace := list vm_instruction.
Definition Weight := Trace -> nat.

(** ** Explicit minimal laws (no named predicate ambiguity)

    These are the only laws used in the no-go results.

    Trace: execution history as list of VM instructions
    Weight: structural information cost function (Trace -> nat)

    I claim these three laws are NECESSARY AND SUFFICIENT for No Free Insight:
    1. weight_empty: w([]) = 0 (no computation = no cost)
    2. weight_sequential: w(t1 ++ t2) = w(t1) + w(t2) (locality in time)
    3. weight_disjoint_commutes: disjoint traces commute (locality in space)

    PHYSICAL INTERPRETATION:
    - Weight counts something physical (μ-bits, structural information)
    - Additivity means cost is conserved (like energy)
    - Disjoint commutation means spacelike-separated operations are independent

    FALSIFICATION: Find executions where w(t1 ++ t2) ≠ w(t1) + w(t2), or where
    disjoint traces have w(t1 ++ t2) ≠ w(t2 ++ t1). Or prove No Free Insight
    without using these laws (showing they're not necessary).
*)

Definition weight_empty (w : Weight) : Prop :=
  w [] = 0.

Definition weight_sequential (w : Weight) : Prop :=
  forall t1 t2, w (t1 ++ t2) = w t1 + w t2.

Definition disjoint_list {A : Type} (xs ys : list A) : Prop :=
  forall x, In x xs -> ~ In x ys.

Definition trace_disjoint (t1 t2 : Trace) : Prop :=
  disjoint_list (causal_cone t1) (causal_cone t2) /\
  disjoint_list (causal_cone t2) (causal_cone t1).

(** Optional commutation law (used as an explicit "tensor-like" commutation).
    Note: we only demand commutation for traces whose causal targets are disjoint.

    WHY "OPTIONAL": The no-go proofs work without this, but it strengthens
    the result. If even with this extra structure we can't get free insight,
    certainly we can't without it.

    WHAT IT MEANS: If t1 and t2 touch disjoint parts of the causal graph
    (disjoint causal cones), then their cost is order-independent. This is
    the algebraic form of Einstein locality.

    trace_disjoint checks BOTH directions (mutual disjointness) because
    causal_cone is typically not symmetric for general traces.

    FALSIFICATION: Find two traces with disjoint causal cones where
    w(t1 ++ t2) ≠ w(t2 ++ t1). This would indicate nonlocal hidden correlations
    in the weight function.
*)
Definition weight_disjoint_commutes (w : Weight) : Prop :=
  forall t1 t2,
    trace_disjoint t1 t2 ->
    w (t1 ++ t2) = w (t2 ++ t1).

Definition weight_laws (w : Weight) : Prop :=
  weight_empty w /\ weight_sequential w /\ weight_disjoint_commutes w.

(** ** A menu of minimal extensions ("extra structure")

    These laws are NOT required for No Free Insight, but they appear in
    specific applications (like deriving physical constants).

    singleton_uniform: All single-step traces cost the same.
    CLAIM: This is a symmetry principle. If different instructions had
    different intrinsic costs, the VM would break instruction-level symmetry.
    The actual μ-cost implementation satisfies this (every instruction costs 1μ).

    unit_normalization: Fixes the scale by setting w([halt 0]) = 1.
    CLAIM: Without this, weight is defined only up to overall scale.
    This is like choosing units (meters vs feet). The specific instruction
    "halt 0" is arbitrary - any single instruction would work.

    FALSIFICATION for singleton_uniform: Find two single instructions with
    different measured costs. For unit_normalization: show the choice of
    scale leads to contradictions in derived physical constants.
*)

(** Singleton-uniformity: all single-step traces have the same weight.
    This is a purely algebraic symmetry/identification principle. *)
Definition singleton_uniform (w : Weight) : Prop :=
  forall i j, w [i] = w [j].

(** Unit normalization: fixes the overall scale by pinning one singleton. *)
Definition unit_normalization (w : Weight) : Prop :=
  w [instr_halt 0] = 1.

(** ** Observational finiteness (explicit coarse-graining / finite measurement algebra)

    This is a constructive "finite enumeration" notion: a finite list of distinct
    microstates that covers the region-equivalence class.

    WHY THIS MATTERS:
    I claim quantum mechanics requires finite-dimensional Hilbert spaces per
    observable region. Infinite-dimensional spaces (like continuous position)
    are idealizations - actual measurements bin into finite outcomes.

    region_equiv: Two states are equivalent if they produce the same observable
    values in every memory region. This is the operational definition of
    "same state as far as measurements can tell."

    finite_region_equiv_class: For any state s, there exists a finite list
    of all states operationally equivalent to s.

    PHYSICAL CLAIM: The universe has finite information density per region.
    You cannot pack infinite distinguishable states into a finite volume.
    This is related to the Bekenstein bound but stated algebraically.

    FALSIFICATION: Exhibit a VMState with infinite operationally-distinct
    microstates in the same equivalence class. Or show continuous observables
    (like exact position) are necessary for quantum mechanics, contradicting
    finite measurement algebras.
*)

Definition region_equiv (s1 s2 : VMState) : Prop :=
  forall mid, ObservableRegion s1 mid = ObservableRegion s2 mid.

Definition finite_region_equiv_class (s : VMState) : Prop :=
  exists l : list VMState,
    NoDup l /\
    forall s', region_equiv s s' -> In s' l.
