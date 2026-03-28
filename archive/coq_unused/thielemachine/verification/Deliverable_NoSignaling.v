From Coq Require Import List Lia.
Import ListNotations.

(* Kernel-level observational no-signaling theorems *)
Require Import KernelPhysics.
Require Import SpacetimeEmergence.
Require Import PhysicsClosure.

(** Deliverable: Partition-native no-signaling / locality as an observational theorem.

    This is the "can’t be stated without partitions" core statement:
    if a module id is outside the instruction targets (or outside the causal cone
    of a trace), its observable region cannot change.

    This module is intentionally thin: it re-exports the already-proven kernel
    theorems as a stable entrypoint.
*)

Module DeliverableNoSignaling.

Definition step_observational_no_signaling := observational_no_signaling.

Definition trace_no_signaling_outside_cone := exec_trace_no_signaling_outside_cone.

Definition physics_closure_bundle := Physics_Closure.

End DeliverableNoSignaling.
