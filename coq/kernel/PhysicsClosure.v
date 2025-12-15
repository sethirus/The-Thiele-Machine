From Coq Require Import List Lia.

From Kernel Require Import VMState VMStep KernelPhysics.
From Kernel Require Import SpacetimeEmergence.

Import ListNotations.

Theorem Physics_Closure :
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
  split.
  - exact observational_no_signaling.
  - split.
    + exact mu_conservation_kernel.
    + exact exec_trace_no_signaling_outside_cone.
Qed.
