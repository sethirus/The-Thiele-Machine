(** PhysicsClosure: package the locality, conservation, and causality lemmas.

   This file does not derive all of physics. It packages three operational
   properties already proved elsewhere in the kernel: locality for single
   steps, monotonicity of μ, and no-signaling outside the causal cone for
   traces. Physics_Closure is therefore a packaging theorem over existing VM
   semantics, not a new foundational derivation from scratch.

   The value of the file is that those three properties can be cited together
   as one kernel-level closure statement. If any one of the imported lemmas
   failed, the package theorem would fail with it.
*)

From Coq Require Import List Lia.

From Kernel Require Import VMState VMStep KernelPhysics.
From Kernel Require Import SpacetimeEmergence.

Import ListNotations.

(** [Physics_Closure] packages three imported operational properties:
    single-step locality for the selected observable region, non-decrease of
    the [vm_mu] field, and trace non-signaling outside the named causal cone.
    The proof is a conjunction of those imported theorems. The labels
    “locality,” “conservation,” and “causality” describe their formal shape;
    they do not identify the VM with a relativistic or thermodynamic physical
    theory. Such an interpretation would require additional calibration and
    implementation premises. *)
Theorem Physics_Closure :
  (* Part 1: Locality - single step doesn't affect non-targets *)
  (forall s s' instr mid,
      well_formed_graph s.(vm_graph) ->
      mid < pg_next_id s.(vm_graph) ->
      vm_step s instr s' ->
      ~ In mid (instr_targets instr) ->
      ObservableRegion s mid = ObservableRegion s' mid)
  /\
  (* Part 2: Conservation - μ never decreases *)
  (forall s s' instr,
      vm_step s instr s' ->
      s'.(vm_mu) >= s.(vm_mu))
  /\
  (* Part 3: Causality - effects constrained by causal cone *)
  (forall s trace s' mid,
      exec_trace s trace s' ->
      well_formed_graph s.(vm_graph) ->
      mid < pg_next_id s.(vm_graph) ->
      ~ In mid (causal_cone trace) ->
      ObservableRegion s mid = ObservableRegion s' mid).
Proof.
  split.
  - (* Locality: from KernelPhysics.v *)
    exact observational_no_signaling.
  - split.
    + (* Conservation: from KernelPhysics.v *)
      exact mu_conservation_kernel.
    + (* Causality: from SpacetimeEmergence.v *)
      exact exec_trace_no_signaling_outside_cone.
Qed.

(**
    CLOSURE INTERPRETATION

    This theorem establishes that the kernel is "closed" under physical
    law derivation in the following sense:

    DERIVED LAWS:
    - Locality (no signaling)
    - Conservation (μ-monotonicity)
    - Causality (causal cone constraint)

    NOT DERIVED (require additional structure):
    - Lorentz invariance (see LorentzNotForced.v)
    - Specific metrics (gauge choice)
    - Coupling constants (empirical input)

    The kernel derives the STRUCTURE of physical law (locality, conservation,
    causality) but leaves PARAMETERS (metric, couplings) underdetermined.

    This is the correct division: computation determines structure, experiment
    determines parameters.

    *)
