(** This file exposes three properties of the VM transition relation.
    The first property preserves [ObservableRegion] outside an instruction's
    explicit target list.
    The second property makes the [vm_mu] field nondecreasing across a step.
    The third property preserves an observable region outside the supplied
    [causal_cone] across a trace.
    The word [causal] names the dependency relation defined by this project.
    These theorems do not identify that relation with physical spacetime or a
    physical locality law.
    The proofs are supplied by [Physics_Closure]. *)

From Coq Require Import List.

From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import KernelPhysics.
From Kernel Require Import PhysicsClosure.
From Kernel Require Import SpacetimeEmergence.

Import ListNotations.


(** [KernelMaximalClosureP] packages the three stated VM properties.
    Instruction locality quantifies over a well-formed graph, a valid module
    identifier, a successful step, and a module outside [instr_targets].
    Ledger monotonicity says that a successful step does not decrease [vm_mu].
    Trace locality quantifies over a well-formed initial graph, a valid module
    identifier, a supplied trace, and a module outside [causal_cone trace].
    The predicate is an operational contract over this VM model.
    It is not a physical law, an entropy theorem, or a claim about every
    scheduler or implementation. *)
Definition KernelMaximalClosureP : Prop :=
  (forall s s' instr mid,
      well_formed_graph s.(vm_graph) ->
      mid < pg_next_id s.(vm_graph) ->
      vm_step s instr s' ->
      ~ In mid (instr_targets instr) ->
      ObservableRegion s mid = ObservableRegion s' mid)
  /\
  (forall s s' instr,
      vm_step s instr s' ->
      s'.(vm_mu) >= s.(vm_mu))
  /\
  (forall s trace s' mid,
      exec_trace s trace s' ->
      well_formed_graph s.(vm_graph) ->
      mid < pg_next_id s.(vm_graph) ->
      ~ In mid (causal_cone trace) ->
      ObservableRegion s mid = ObservableRegion s' mid).


(** [KernelMaximalClosure] exposes [Physics_Closure] under the historical
    public name used by downstream files.
    The theorem proves the stated preservation properties for this transition
    relation under their explicit premises.

    The name [Maximal] is retained for compatibility; it does not claim that
    the cone is globally minimal or that the properties are physically
    necessary.
*)
(* SCOPE NOTE: alias for [Physics_Closure]; retained for compatibility. *)
Theorem KernelMaximalClosure : KernelMaximalClosureP.
Proof.
  exact Physics_Closure.
Qed.
