From Coq Require Import List.

From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import KernelPhysics.
From Kernel Require Import PhysicsClosure.
From Kernel Require Import SpacetimeEmergence.
From Kernel Require Import ProbabilityImpossibility.
From Kernel Require Import EntropyImpossibility.
From Kernel Require Import LorentzNotForced.

From KernelTOE Require Import Closure.
From KernelTOE Require Import NoGo.
From KernelTOE Require Import TOE.

(* This file provides the required single “final outcome” as a theorem:
   The full TOE plan cannot be completed from the kernel layer as-is,
   because multiple requested derived objects require additional structure.

   We package that as an impossibility witness: at least one key step of
   the plan (uniqueness of a probability law / Born-rule-like uniqueness)
   is not forced by compositionality alone, and observational equivalence
   classes are infinite (blocking log-cardinality entropy without a
   finiteness/coarse-graining axiom/definition).
*)

Theorem KernelNoGoForTOE_Decision :
  KernelNoGoForTOE_P.
Proof.
  exact KernelNoGoForTOE.
Qed.

(* Backward-compatible name, but sharpened: the gaps are now stated using
   explicit laws and an explicit finiteness notion. *)
Theorem Physics_Requires_Extra_Structure :
  KernelNoGoForTOE_P.
Proof.
  exact KernelNoGoForTOE.
Qed.

(* The best available closure theorem inside the kernel layer:
   locality/no-signaling + mu monotonicity + multi-step cone locality.
*)
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
Theorem Kernel_TOE_FinalOutcome :
  KernelMaximalClosureP /\ KernelNoGoForTOE_P.
Proof.
  exact KernelTOE_FinalOutcome.
Qed.
