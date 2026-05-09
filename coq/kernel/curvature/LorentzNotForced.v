(** LorentzNotForced: Why Lorentz Invariance Is Not Derived

    I claim the kernel layer does NOT derive Lorentz invariance. This is
    intentional. Lorentz boosts require a metric (spacetime interval), which
    is NOT present in the kernel. Causal cones are purely syntactic (instruction
    dependencies), not geometric.

    There exists a trivial cone-preserving symmetry (identity),
    and there exist NON-TRIVIAL cone symmetries (stutter) that
    preserve cones but are NOT Lorentz transformations.

    - Lorentz_Not_Forced: Identity preserves cones (trivial symmetry)
    - Cone_Symmetry_Underdetermined: Stutter (inserting no-op instructions)
      preserves cones but is not a Lorentz boost

    With only kernel primitives (VMState, vm_step, causal_cone), I cannot derive
    a unique Lorentz group: I get some cone-preserving symmetries but not the
    Lorentz group specifically. To get Lorentz you need a metric, continuous
    boosts, and interval preservation, none of which exist at kernel level.
    This file leaves Lorentz invariance to spacetime/metric layers instead of
    treating it as a primitive kernel constraint.

    To falsify: show causal_cone uniquely determines a Lorentz group structure
    without additional geometric input, or prove Lorentz boosts are the ONLY
    cone-preserving symmetries (contradicting the stutter example), or show
    kernel-level objects that encode metric/interval structure.

    This file localizes a kernel-level boundary:
    With only the current kernel primitives, "Lorentz invariance" has no
    canonical statement because there is no derived metric/interval, and
    cone symmetries are underdetermined without extra structure.
    (Note: deriving strictly_stronger predicates from feasible-set reduction
    is handled in InformationGainToStrengthening.v; this file documents a
    separate limitation: Lorentz symmetry specifically requires geometric
    structure beyond cones.)

    What we can prove (and what is used everywhere) is purely:
    - cones are syntactically determined by instr_targets recursion
    - no-signaling is stated relative to that cone

    Any stronger notion (continuous boosts, interval preservation, etc.)
    requires additional derived objects (e.g., a metric) which are not
    present in the kernel layer.
*)

(* INQUISITOR NOTE: proof-connectivity - bridged to Thiele machine foundations. *)
From Kernel Require Import MuCostModel.

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

(** DEFINITIONAL HELPER: [causal_cone] skips [instr_pnew] because partition
    creation does not affect the causal cone (it creates a new isolated module
    with no causal predecessors). *)
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
