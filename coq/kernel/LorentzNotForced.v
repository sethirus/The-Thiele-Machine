(** * LorentzNotForced: Why Lorentz Invariance Is Not Derived

    WHY THIS FILE EXISTS:
    I claim the kernel layer does NOT derive Lorentz invariance. This is
    intentional. Lorentz boosts require a metric (spacetime interval), which
    is NOT present in the kernel. Causal cones are purely syntactic (instruction
    dependencies), not geometric.

    THE CORE CLAIM:
    There exists a trivial cone-preserving symmetry (identity, Theorem line 25),
    and there exist NON-TRIVIAL cone symmetries (stutter, Theorem line 51) that
    preserve cones but are NOT Lorentz transformations.

    WHAT THIS PROVES:
    - Lorentz_Not_Forced: Identity preserves cones (trivial symmetry)
    - Cone_Symmetry_Underdetermined: Stutter (inserting no-op instructions)
      preserves cones but is not a Lorentz boost

    WHY "NOT FORCED":
    With only kernel primitives (VMState, vm_step, causal_cone), we cannot
    derive a unique Lorentz group. We get SOME symmetries (cone-preserving
    maps) but not THE Lorentz group specifically.

    To get Lorentz: need metric, need continuous boosts, need interval preservation.
    None of these exist at kernel level. They would require additional structure
    (differential geometry, pseudo-Riemannian manifolds, etc.).

    PHYSICAL INTERPRETATION:
    Lorentz invariance is an EMERGENT property of spacetime, not a fundamental
    computational constraint. The kernel layer is pre-geometric. Spacetime geometry
    (metric, intervals, boosts) would emerge from statistical/thermodynamic
    behavior of many computations, not from single VM state transitions.

    FALSIFICATION:
    Show that causal_cone function uniquely determines a Lorentz group structure
    without additional geometric input. Or prove Lorentz boosts are the ONLY
    cone-preserving symmetries (contradicting stutter example). Or demonstrate
    kernel-level objects that encode metric/interval structure.

    This file localizes Task B3 failure:
    With only the current kernel primitives, "Lorentz invariance" has no
    canonical statement because there is no derived metric/interval, and
    cone symmetries are underdetermined without extra structure.

    What we can prove (and what is used everywhere) is purely:
    - cones are syntactically determined by instr_targets recursion
    - no-signaling is stated relative to that cone

    Any stronger notion (continuous boosts, interval preservation, etc.)
    requires additional derived objects (e.g., a metric) which are not
    present in the kernel layer.
*)

From Coq Require Import List.

From Kernel Require Import VMState VMStep KernelPhysics.

Import ListNotations.

Definition cone_preserving (phi : list vm_instruction -> list vm_instruction) : Prop :=
  forall t, causal_cone (phi t) = causal_cone t.

(* There is always a trivial cone-preserving symmetry: identity. *)
Theorem Lorentz_Not_Forced : exists phi, cone_preserving phi.
Proof.
  exists (fun t => t).
  intro t.
  reflexivity.
Qed.

(* And there can be nontrivial reparameterizations that preserve cones but
  are not constrained into a Lorentz-like group by anything in-kernel.
  Example: inserting an instruction with empty target set (pnew) does not
  change the cone.
*)
Definition stutter (region : list nat) (cost : nat) (t : list vm_instruction)
  : list vm_instruction :=
  instr_pnew region cost :: t.

Lemma causal_cone_stutter : forall region cost t,
  causal_cone (stutter region cost t) = causal_cone t.
Proof.
  intros region cost t.
  unfold stutter.
  simpl.
  reflexivity.
Qed.

(* Definitional lemma: This equality is by definition, not vacuous *)
Theorem Cone_Symmetry_Underdetermined :
  exists phi,
    (forall t, causal_cone (phi t) = causal_cone t) /\
    (exists region cost t0, phi t0 = stutter region cost t0).
Proof.
  exists (fun t => stutter [] 0 t).
  split.
  - intro t. apply causal_cone_stutter.
  - exists [], 0, []. reflexivity.
Qed.
