(** * TOEDecision: Final decision on Theory of Everything completeness

    WHY THIS FILE EXISTS:
    The kernel proves closure (locality, mu-monotonicity, trace causality)
    but also proves a NO-GO: the full TOE plan cannot be completed from
    the kernel layer alone. Specifically, uniqueness of probability law
    (Born-rule-like uniqueness) is not forced by compositionality, and
    observational equivalence classes are infinite (blocking log-cardinality
    entropy without a finiteness/coarse-graining axiom).

    THE CORE CLAIM:
    KernelTOE_FinalOutcome packages the forced closure + minimal no-go
    into a single theorem: the kernel achieves maximal closure AND the
    remaining gaps are precisely characterized.

    FALSIFICATION:
    Derive a unique probability law from the kernel weight laws alone
    (without singleton_uniform or unit_normalization). This would contradict
    the no-go witness (CompositionalWeightFamily_Infinite) which exhibits
    infinitely many valid weight functions.
*)

From Coq Require Import List.

From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import KernelPhysics.
From Kernel Require Import PhysicsClosure.
From Kernel Require Import SpacetimeEmergence.
From Kernel Require Import ProbabilityImpossibility.
From Kernel Require Import EntropyImpossibility.
From Kernel Require Import LorentzNotForced.

From Kernel Require Import NoGo.
From Kernel Require Import Closure.
From Kernel Require Import TOE.

(** [KernelNoGoForTOE_Decision]: formal specification. *)
(* INQUISITOR NOTE: alias for KernelNoGoForTOE - summary module re-export *)
Theorem KernelNoGoForTOE_Decision :
  KernelNoGoForTOE_P.
Proof.
  exact KernelNoGoForTOE.
Qed.

(* Backward-compatible name, but sharpened: the gaps are now stated using
   explicit laws and an explicit finiteness notion. *)
(* INQUISITOR NOTE: alias for KernelNoGoForTOE - summary module re-export *)
(** [Physics_Requires_Extra_Structure]: formal specification. *)
Theorem Physics_Requires_Extra_Structure :
  KernelNoGoForTOE_P.
Proof.
  exact KernelNoGoForTOE.
Qed.

(* The best available closure theorem inside the kernel layer:
   locality/no-signaling + mu monotonicity + multi-step cone locality.
*)
(** [Kernel_Physics_Closure]: formal specification. *)
Theorem Kernel_Physics_Closure :
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
Proof.
  exact Physics_Closure.
Qed.

(* Final packaged outcome: forced closure + minimal no-go. *)
(* INQUISITOR NOTE: alias for KernelTOE_FinalOutcome - summary module re-export *)
(** [Kernel_TOE_FinalOutcome]: formal specification. *)
Theorem Kernel_TOE_FinalOutcome :
  KernelMaximalClosureP /\ KernelNoGoForTOE_P.
Proof.
  exact KernelTOE_FinalOutcome.
Qed.
