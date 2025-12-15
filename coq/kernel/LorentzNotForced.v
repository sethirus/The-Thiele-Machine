From Coq Require Import List.

From Kernel Require Import VMState VMStep KernelPhysics.

Import ListNotations.

(* This file localizes Task B3 failure:
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
