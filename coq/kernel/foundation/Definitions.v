(** Definitions: Minimal explicit interfaces for kernel TOE

    I claim the no-go results (No Free Insight, closure theorems, physical
    constant derivations) hold for ANY weight function satisfying these laws,
    not just the specific μ-cost implementation. This file only defines the
    abstract interface. The theorem files have to earn the claim.

    By sealing the dependency cone here, I make hidden assumptions visible.
    Every law used in proofs appears explicitly in this file. No "named predicate
    ambiguity": if a theorem relies on weight_sequential, it says so.

    Three laws (weight_empty, weight_sequential, weight_disjoint_commutes) are
    the minimal laws I want to test for No Free Insight. This file does not prove
    necessity or sufficiency by itself. It gives the rest of the kernel a contract
    to prove against.

    To falsify: Find a weight function satisfying these laws but violating
    No Free Insight. Or show the laws are inconsistent (no such function exists).
    Or prove a no-go result without using any law from this file.

    This file is the sealed dependency cone for the TOE "maximal closure +
    minimal no-go" deliverables.
*)

From Coq Require Import List Lia.

From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import KernelPhysics.

Import ListNotations.

Definition Trace := list vm_instruction.
Definition Weight := Trace -> nat.

(** ** Explicit minimal laws (no named predicate ambiguity)

    These are the only laws used in the no-go results.

    Trace: execution history as list of VM instructions
    Weight: structural information cost function (Trace -> nat)

    I claim these three laws are the right minimal interface for No Free Insight:
    1. weight_empty: w([]) = 0 (no computation = no cost)
    2. weight_sequential: w(t1 ++ t2) = w(t1) + w(t2) (locality in time)
    3. weight_disjoint_commutes: disjoint traces commute (locality in space)

    IMPORTANT: this file only defines the laws. If a later theorem says they are
    sufficient, that theorem has to import these definitions and prove it.

    - Weight counts something physical (μ-bits, structural information)
    - Additivity means cost is conserved (like energy)
    - Disjoint commutation means spacelike-separated operations are independent

    To falsify: Find executions where w(t1 ++ t2) ≠ w(t1) + w(t2), or where
    disjoint traces have w(t1 ++ t2) ≠ w(t2 ++ t1). Or prove No Free Insight
    without using these laws. That would show this interface is not minimal.
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
    I only demand commutation for traces whose causal targets are disjoint.

    WHY "OPTIONAL": Some theorems only need weight_empty and weight_sequential.
    The full weight_laws bundle below includes this third law, so any theorem
    that asks for weight_laws is explicitly opting into disjoint commutation.

    WHAT IT MEANS: If t1 and t2 touch disjoint parts of the causal graph
    (disjoint causal cones), then their cost is order-independent. This is
    the algebraic form of Einstein locality.

    trace_disjoint checks BOTH directions (mutual disjointness) because
    causal_cone is typically not symmetric for general traces.

    To falsify: Find two traces with disjoint causal cones where
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
    CLAIM: This is a symmetry principle for unit-normalized models. The current
    instruction_cost in VMStep.v does NOT satisfy this in general: LASSERT,
    READ_PORT, CERTIFY, and MORPH_ASSERT have special costs.

    unit_normalization: Fixes the scale by setting w([halt 0]) = 1.
    CLAIM: Without this, weight is defined only up to overall scale.
    This is like choosing units (meters vs feet). The specific instruction
    "halt 0" is the chosen pin. Under singleton_uniform, any singleton would do.

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

    I use this as the finite-measurement assumption: observable regions have
    finitely many distinguishable outcomes. Infinite-dimensional spaces (like
    continuous position) may be useful idealizations, but the VM interface here
    talks about finite measurement bins.

    region_equiv: Two states are equivalent if they produce the same observable
    values in every memory region. This is the operational definition of
    "same state as far as measurements can tell."

    finite_region_equiv_class: For any state s, there exists a finite list
    of all states operationally equivalent to s.

    finite information density per region. This file does not
    prove the physics. It states the algebraic predicate later files can assume,
    prove from another model, or try to refute.

    To falsify: Exhibit a VMState with infinite operationally-distinct
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
