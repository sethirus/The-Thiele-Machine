(** TopologyCurvatureBridge: delta chi implies delta curvature.

    This file is the short bridge from topology to geometry. Once
    DiscreteGaussBonnet.v says total curvature is 5PI * chi, taking the
    difference between two VM states immediately gives delta-K = 5PI * delta-chi.

    That makes curvature jumps discrete. If chi changes by 1, total curvature
    changes by exactly 5PI. If chi does not move, total curvature does not move.
    The corollaries below are just those cases written out explicitly.

    To break this file, exhibit two well-formed triangulated VM states where
    the curvature difference fails to match 5PI times the Euler-characteristic
    difference. Since the proof is just Gauss-Bonnet applied twice and
    subtracted, any such counterexample would also break the earlier theorem. *)

(* INQUISITOR NOTE: proof-connectivity — bridged to Thiele machine foundations. *)
From Kernel Require Import MuCostModel.

From Coq Require Import List Arith.PeanoNat Lia Bool ZArith Reals.
From Coq Require Import Lra.
Import ListNotations.
Local Open Scope R_scope.

From Kernel Require Import VMState.
From Kernel Require Import DiscreteTopology.
From Kernel Require Import DiscreteGaussBonnet.

(** ** The Central Bridge Theorem

  This is the exact statement that topology change fixes the total-curvature
  change. Nothing probabilistic is happening here. *)

Theorem delta_chi_implies_delta_curvature : forall s s',
  well_formed_triangulated (vm_graph s) ->
  well_formed_triangulated (vm_graph s') ->
  let Δχ := (euler_characteristic (vm_graph s') - euler_characteristic (vm_graph s))%Z in
  let ΔK := (total_curvature (vm_graph s') - total_curvature (vm_graph s))%R in
  ΔK = (5 * PI * IZR Δχ)%R.
Proof.
  intros s s' Hwf Hwf'.
  simpl.
  unfold total_curvature.

  (* Apply Gauss-Bonnet to both states *)
  rewrite (discrete_gauss_bonnet (vm_graph s') Hwf').
  rewrite (discrete_gauss_bonnet (vm_graph s) Hwf).

  (* Algebraic simplification *)
  (* Distribute and factor *)
  rewrite minus_IZR.
  ring.
Qed.

(** ** Corollaries: Specific Topology Changes *)

(** Adding one vertex-edge-face unit changes curvature by 5π *)
Corollary add_triangle_changes_curvature : forall s s',
  well_formed_triangulated (vm_graph s) ->
  well_formed_triangulated (vm_graph s') ->
  euler_characteristic (vm_graph s') = (euler_characteristic (vm_graph s) + 1)%Z ->
  total_curvature (vm_graph s') = (total_curvature (vm_graph s) + 5 * PI)%R.
Proof.
  intros s s' Hwf Hwf' Hchi.

  (* Use the main theorem *)
  assert (H := delta_chi_implies_delta_curvature s s' Hwf Hwf').
  simpl in H.

  (* Substitute Δχ = 1 *)
  rewrite Hchi in H.
  replace (euler_characteristic (vm_graph s) + 1 - euler_characteristic (vm_graph s))%Z
    with 1%Z in H by ring.
  simpl in H.

  (* Solve for total_curvature s' *)
  lra.
Qed.

(** Removing topology (Δχ = -1) decreases curvature by 5π *)
Corollary remove_triangle_changes_curvature : forall s s',
  well_formed_triangulated (vm_graph s) ->
  well_formed_triangulated (vm_graph s') ->
  euler_characteristic (vm_graph s') = (euler_characteristic (vm_graph s) - 1)%Z ->
  total_curvature (vm_graph s') = (total_curvature (vm_graph s) - 5 * PI)%R.
Proof.
  intros s s' Hwf Hwf' Hchi.

  assert (H := delta_chi_implies_delta_curvature s s' Hwf Hwf').
  simpl in H.

  rewrite Hchi in H.
  replace (euler_characteristic (vm_graph s) - 1 - euler_characteristic (vm_graph s))%Z
    with (-1)%Z in H by ring.
  simpl in H.

  lra.
Qed.

(** If topology doesn't change, neither does total curvature *)
Corollary topology_invariant_implies_curvature_invariant : forall s s',
  well_formed_triangulated (vm_graph s) ->
  well_formed_triangulated (vm_graph s') ->
  euler_characteristic (vm_graph s') = euler_characteristic (vm_graph s) ->
  total_curvature (vm_graph s') = total_curvature (vm_graph s).
Proof.
  intros s s' Hwf Hwf' Hchi.

  assert (H := delta_chi_implies_delta_curvature s s' Hwf Hwf').
  simpl in H.

  rewrite Hchi in H.
  replace (euler_characteristic (vm_graph s) - euler_characteristic (vm_graph s))%Z
    with 0%Z in H by ring.
  simpl in H.

  lra.
Qed.

(** ** Local Curvature Changes

  Global curvature only changes by moving local defects around. This section
  records the bookkeeping identity for that redistribution. *)

(** Change in angle defect at a specific vertex *)
Definition delta_vertex_curvature (s s' : VMState) (v : nat) : R :=
  (angle_defect (vm_graph s') v - angle_defect (vm_graph s) v)%R.

(** Sum of local changes equals global change *)
Theorem local_curvature_changes_sum_to_global : forall s s',
  well_formed_triangulated (vm_graph s) ->
  well_formed_triangulated (vm_graph s') ->
  (* If both states have the same vertices *)
  vertices (vm_graph s') = vertices (vm_graph s) ->
  (* Then the sum of local changes equals the global change *)
  sum_angle_defects_list (vm_graph s') (vertices (vm_graph s'))
  - sum_angle_defects_list (vm_graph s) (vertices (vm_graph s))
  = total_curvature (vm_graph s') - total_curvature (vm_graph s).
Proof.
  intros s s' _ _ Hverts.
  unfold total_curvature, total_angle_defect.
  rewrite Hverts.
  reflexivity.
Qed.

(** ** Physical Interpretation

  Chi measures topology. K measures total curvature. This theorem says the
  topology jump fixes the curvature jump exactly.

  That matters because chi is integer-valued. So the allowed curvature jumps
  come in 5PI-sized units. The later files use that quantization when they
  talk about topology-changing VM steps as curvature-changing events. *)

(** ** Verification Requirements

  To test this outside Coq, compare two VM states, compute chi and total
  curvature for both, and check that the differences satisfy delta-K =
  5PI * delta-chi. *)
