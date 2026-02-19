From Coq Require Import List Lia Arith.PeanoNat.
Import ListNotations.

From Kernel Require Import VMState.
From Kernel Require Import KernelPhysics.
From Kernel Require Import SpacetimeEmergence.

(** Deliverable: Signaling requires entering the causal cone.

    This is a partition-native lower bound: if a module’s observable region
    changes across an execution trace, that module id must appear in the trace’s
    causal cone (i.e., be targeted by some instruction).

    Stated differently: *no signaling without targeting*.
*)

Module DeliverableSignalingLowerBound.

(** [observable_change_implies_in_cone]: formal specification. *)
Theorem observable_change_implies_in_cone :
  forall s trace s' mid,
    exec_trace s trace s' ->
    well_formed_graph s.(vm_graph) ->
    mid < pg_next_id s.(vm_graph) ->
    ObservableRegion s mid <> ObservableRegion s' mid ->
    In mid (causal_cone trace).
Proof.
  intros s trace s' mid Hexec Hwf Hmid Hneq.
  destruct (in_dec Nat.eq_dec mid (causal_cone trace)) as [Hin|Hnot].
  - exact Hin.
  - exfalso.
    apply Hneq.
    apply (exec_trace_no_signaling_outside_cone s trace s' mid); auto.
Qed.

End DeliverableSignalingLowerBound.
