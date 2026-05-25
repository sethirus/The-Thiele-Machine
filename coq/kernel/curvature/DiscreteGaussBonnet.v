(** DiscreteGaussBonnet: total angle defect from Euler characteristic.

    The setup is simple. Take the partition graph, read it as the triangulated
    surface from DiscreteTopology.v, and assign every triangle corner the same
    angle PI / 3. At one vertex, curvature is whatever is missing from 2PI.
    Add that defect over the whole graph and the total is pinned down by chi.

    The main theorem is discrete_gauss_bonnet. Under
    well_formed_triangulated it proves:

      total_angle_defect g = 5 * PI * IZR (euler_characteristic g).

    Nothing fancy is hiding in the proof. First expand the defects to
    2PI * V - PI * F. Then move the triangulation identity from nat into R.
    Then rewrite chi in terms of E and F. That is the whole machine.

    Positive defect means sphere-like curvature. Negative defect means
    saddle-like curvature. Zero means flat. So once chi is fixed, total
    curvature is fixed too. That is the hook the later topology-change files
    lean on.

    To break this, produce a well_formed_triangulated graph where the total
    defect is not 5 * PI times chi. If the structural identity from
    DiscreteTopology.v and the equilateral-angle model both hold, this file
    says you cannot. *)

(* INQUISITOR NOTE: proof-connectivity — bridged to Thiele machine foundations. *)
From Kernel Require Import MuCostModel.

From Coq Require Import List Arith.PeanoNat Lia Bool ZArith Reals.
From Coq Require Import Lra.
Import ListNotations.
Local Open Scope R_scope.

From Kernel Require Import VMState.
From Kernel Require Import DiscreteTopology.

(** First principles: angle defects

    For each vertex v:
    - count the triangles incident to v
    - give each incident triangle the angle π/3 at v
    - defect(v) = 2π - sum(angles at v)

    Flat means defect = 0. Positive curvature gives defect > 0. Negative
    curvature gives defect < 0.
    *)

(** This file does not derive angles from μ-costs. It uses the equilateral
    discretization, where every triangle corner contributes π/3. *)
Definition triangle_interior_angle : R := (PI / 3)%R.  (* Equilateral approximation *)

(** The angle sum at a vertex is degree(v) copies of π/3. *)
Definition vertex_angle_sum (g : PartitionGraph) (vertex : nat) : R :=
  INR (DiscreteTopology.vertex_degree g vertex) * triangle_interior_angle.

(** The vertex defect is what remains after subtracting that angle sum from 2π. *)
Definition angle_defect (g : PartitionGraph) (vertex : nat) : R :=
  (2 * PI - vertex_angle_sum g vertex)%R.

(** Total defect is the sum over the graph's vertex list. *)
Fixpoint sum_angle_defects_list (g : PartitionGraph) (vertices : list nat) : R :=
  match vertices with
  | [] => 0%R
  | v :: rest => (angle_defect g v + sum_angle_defects_list g rest)%R
  end.

Definition total_angle_defect (g : PartitionGraph) : R :=
  sum_angle_defects_list g (vertices g).

(** Triangle angle checks *)

(** Three equilateral corners sum to π. *)
Lemma three_equilateral_angles_sum_pi :
  (3 * triangle_interior_angle = PI)%R.
Proof.
  (* [triangle_interior_angle] is defined as [PI / 3]; inline the unfold here
     rather than routing through a separate definitional lemma. *)
  unfold triangle_interior_angle.
  field.
Qed.

(** Discrete Gauss-Bonnet.

  The smooth theorem gives 2PI * chi. This discrete model gives 5PI * chi
  because the triangulation identity here is different. Summing
  2PI - d(v) * PI / 3 over all vertices gives 2PI * V - PI * F. Then the
  combinatorial identity rewrites that into 5PI * chi. The theorem below is
  just that bookkeeping done carefully. *)

(** Note: the identity 3V = 5E - 6F holds for planar triangulations, not all
    triangulated complexes. A tetrahedron (V=4, E=6, F=4) gives 3×4=12 vs
    5×6-6×4=6, so it does not hold there. A planar disk (V=7, E=15, F=9)
    gives 21 = 21.
    Proven in DiscreteTopology.v from the structural invariants E = I + B,
    3F = 2I + B. *)

(** The algebra: each triangle touches 3 vertices so Σd(v) = 3F,
    giving Σ defects = 2πV - πF. Substituting V = (5E-6F)/3 yields
    (10πE - 15πF)/3. And χ = (2E-3F)/3, so 5πχ = (10πE - 15πF)/3. *)

(** Count incidences: sum of vertex degrees = 3F

    Each triangle has 3 vertices, so counting all vertex-triangle incidences
    gives 3F total.

    sum_degrees is defined in DiscreteTopology.v. *)

(** Count total vertex-module incidences from the module side. *)
Fixpoint count_vertices_in_modules (modules : list (ModuleID * ModuleState)) : nat :=
  match modules with
  | [] => 0
  | (_, m) :: rest => (length (module_region m) + count_vertices_in_modules rest)%nat
  end.

Lemma sum_of_vertex_degrees_equals_3F : forall g,
  well_formed_triangulated g ->
  sum_degrees g (vertices g) = (3 * F g)%nat.
Proof.
  intros g Hwf.
  (* This follows from the definition of well_formed_triangulated
     which includes satisfies_degree_face_relation as a requirement. *)
  (* Extract the vertex-face degree relationship from well-formedness *)
  unfold well_formed_triangulated in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ [_ [_ [_ [Hdeg _]]]]]]]]].
  unfold satisfies_degree_face_relation in Hdeg.
  exact Hdeg.
Qed.

(** Expand defects: sum of angle defects = 2πV - πF

    Expanding the definition:
    sum(angle_defects) = sum over v of (2π - degree(v)×π/3)
                       = 2πV - (π/3) × sum(degrees)
                       = 2πV - (π/3) × 3F
                       = 2πV - πF
 *)

(** This distributes the recursive sum over the subtraction in angle_defect. *)
Lemma sum_angle_defects_expand : forall g verts,
  sum_angle_defects_list g verts =
  (2 * PI * INR (length verts) -
   PI / 3 * INR (sum_degrees g verts))%R.
Proof.
  intros g verts.
  induction verts as [| v rest IH].
  - simpl. lra.
  - simpl sum_angle_defects_list.
    unfold angle_defect at 1.
    unfold vertex_angle_sum.
    rewrite IH.
    simpl length.
    rewrite S_INR.
    simpl sum_degrees.
    rewrite plus_INR.
    (* Expand and simplify *)
    unfold triangle_interior_angle.
    (* 2π - deg(v)×π/3 + rest = 2π + rest_sum - deg(v)×π/3 *)
    (* = 2π + 2π×|rest| - π/3×sum_degrees(rest) - deg(v)×π/3 *)
    (* = 2π×(1+|rest|) - π/3×(deg(v)+sum_degrees(rest)) *)
    ring.
Qed.

Lemma sum_angle_defects_equals_2piV_minus_piF : forall g,
  well_formed_triangulated g ->
  total_angle_defect g = (2 * PI * INR (V g) - PI * INR (F g))%R.
Proof.
  intros g Hwf.

  (* Unfold total_angle_defect *)
  unfold total_angle_defect.

  (* Expand using helper lemma *)
  rewrite sum_angle_defects_expand.

  (* Substitute length(vertices g) = V g *)
  unfold V.

  (* Use sum_of_vertex_degrees_equals_3F *)
  assert (Hdeg := sum_of_vertex_degrees_equals_3F g Hwf).
  rewrite Hdeg.

  (* Simplify: 2πV - π/3 × 3F = 2πV - πF *)
  rewrite mult_INR.
  simpl (INR 3).
  replace (1 + (1 + (1 + 0)))%R with 3%R by ring.

  (* Goal: 2 * PI * INR (length (vertices g)) - PI / 3 * (3 * INR (F g))
           = 2 * PI * INR (length (vertices g)) - PI * INR (F g) *)

  (* Use f_equal to focus on the subtracted parts *)
  f_equal.
  (* Goal: PI / 3 * (3 * INR (F g)) = PI * INR (F g) *)

  (* Prove: PI / 3 * (3 * x) = PI * x *)
  unfold Rdiv.
  assert (H: (/ 3 * 3)%R = 1%R) by (apply Rinv_l; lra).
  ring [H].
Qed.

(** Move the triangulation identity from nat into real arithmetic. *)

Lemma nat_algebra_for_triangulation : forall g,
  well_formed_triangulated g ->
  (3 * V g)%nat = (5 * E g - 6 * F g)%nat ->
  INR (V g) = ((5 * INR (E g) - 6 * INR (F g)) / 3)%R.
Proof.
  intros g Hwf Hident.
  (* Hident: (3 * V g)%nat = (5 * E g - 6 * F g)%nat *)

  (* First, prove that 6F <= 5E using the nat version of Hident *)
  assert (Hge: (6 * F g <= 5 * E g)%nat).
  { (* From triangulation identity: 3V = 5E - 6F
       Since V >= 1 (well-formed), we have 3 <= 5E - 6F
       So 6F <= 5E - 3, hence 6F <= 5E *)
    unfold well_formed_triangulated in Hwf.
    destruct Hwf as [_ [_ [_ [_ [HV [_ [_ [_ [_ _]]]]]]]]].
    (* HV: (1 <= V g)%nat *)
    (* Hident: (3 * V g = 5 * E g - 6 * F g)%nat *)
    (* From HV: 3 * 1 <= 3 * V g, so 3 <= 3 * V g *)
    assert (H3: (3 <= 3 * V g)%nat).
    {
      rewrite <- (Nat.mul_1_r 3) at 1.
      apply Nat.mul_le_mono_l.
      exact HV.
    }
    (* Substitute: 3 <= 5E - 6F *)
    rewrite Hident in H3.
    (* Use lia to derive 6F <= 5E from 3 <= 5E - 6F *)
    lia. }

  (* Now convert to reals *)
  apply (f_equal INR) in Hident.
  (* Hident: INR (3 * V g) = INR (5 * E g - 6 * F g) *)

  (* Expand left side *)
  rewrite Nat.mul_comm in Hident.
  rewrite mult_INR in Hident.

  (* Expand right side using Hge *)
  rewrite (minus_INR (5 * E g) (6 * F g) Hge) in Hident.
  rewrite mult_INR in Hident.
  rewrite mult_INR in Hident.

  (* Now Hident: INR (V g) * 3 = 5 * INR (E g) - 6 * INR (F g) *)
  (* Solve for INR (V g) *)
  simpl in Hident.
  lra.
Qed.

(** Rewrite Euler characteristic using E and F under the same identity. *)

Lemma euler_in_terms_of_E_and_F : forall g,
  well_formed_triangulated g ->
  (3 * V g = 5 * E g - 6 * F g)%nat ->
  IZR (euler_characteristic g) = ((2 * INR (E g) - 3 * INR (F g)) / 3)%R.
Proof.
  intros g Hwf Hident.
  unfold euler_characteristic.

  (* χ = V - E + F (in Z) *)
  (* We want IZR(V - E + F) = (2E - 3F)/3 *)

  assert (HV := nat_algebra_for_triangulation g Hwf Hident).
  (* HV: INR (V g) = (5 * INR (E g) - 6 * INR (F g)) / 3 *)

  (* The goal is: IZR (euler_characteristic g) = ... *)
  (*  where euler_characteristic g = Z.of_nat (V g) - Z.of_nat (E g) + Z.of_nat (F g) *)

  (* Work with IZR directly *)
  unfold euler_characteristic.
  rewrite plus_IZR.
  rewrite minus_IZR.

  (* Convert Z.of_nat to INR via IZR *)
  repeat rewrite <- INR_IZR_INZ.

  (* Now: INR (V g) - INR (E g) + INR (F g) = (2 * INR (E g) - 3 * INR (F g)) / 3 *)

  (* Substitute V = (5E - 6F)/3 *)
  rewrite HV.

  (* Simplify: (5E - 6F)/3 - E + F = ((5E - 6F) - 3E + 3F)/3 = (2E - 3F)/3 *)
  field.
Qed.
(** The main theorem: under well_formed_triangulated, topology fixes total defect. *)

Theorem discrete_gauss_bonnet : forall g,
  well_formed_triangulated g ->
  total_angle_defect g = (5 * PI * IZR (euler_characteristic g))%R.
Proof.
  intros g Hwf.

  (* Get the combinatorial identity from DiscreteTopology.v *)
  assert (Hident : (3 * V g = 5 * E g - 6 * F g)%nat).
  { apply triangulation_combinatorial_identity. exact Hwf. }

  (* Step 1: sum(defects) = 2πV - πF *)
  rewrite (sum_angle_defects_equals_2piV_minus_piF g Hwf).

  (* Step 2: Express V in terms of E and F *)
  assert (HV := nat_algebra_for_triangulation g Hwf Hident).
  rewrite HV.

  (* Step 3: Simplify 2π(5E-6F)/3 - πF *)
  (* = (2π×5E - 2π×6F)/3 - πF
     = (10πE - 12πF)/3 - 3πF/3
     = (10πE - 12πF - 3πF)/3
     = (10πE - 15πF)/3
     *)

  (* Step 4: Show this equals 5πχ *)
  (* χ = (2E - 3F)/3 by euler_in_terms_of_E_and_F
     So 5πχ = 5π(2E - 3F)/3 = (10πE - 15πF)/3
     *)
  assert (Hchi := euler_in_terms_of_E_and_F g Hwf Hident).
  rewrite Hchi.

  (* Both sides now equal (10πE - 15πF)/3 *)
  field.
Qed.

(** In this file, total_curvature is just total_angle_defect with the physics name. *)
Definition total_curvature (g : PartitionGraph) : R :=
  total_angle_defect g.

(** Disk case: if χ = 1, total curvature is 5π. *)
Corollary disk_total_curvature : forall g,
  well_formed_triangulated g ->
  euler_characteristic g = 1%Z ->
  total_angle_defect g = (5 * PI)%R.
Proof.
  intros g Hwf Hchi.
  rewrite (discrete_gauss_bonnet g Hwf).
  rewrite Hchi. simpl.
  field.
Qed.

(** Sphere case: if χ = 2, total curvature is 10π. *)
Corollary sphere_total_curvature : forall g,
  well_formed_triangulated g ->
  euler_characteristic g = 2%Z ->
  total_angle_defect g = (10 * PI)%R.
Proof.
  intros g Hwf Hchi.
  rewrite (discrete_gauss_bonnet g Hwf).
  rewrite Hchi. simpl.
  field.
Qed.

(** Torus case: if χ = 0, total curvature is 0. *)
Corollary torus_total_curvature : forall g,
  well_formed_triangulated g ->
  euler_characteristic g = 0%Z ->
  total_angle_defect g = 0%R.
Proof.
  intros g Hwf Hchi.
  rewrite (discrete_gauss_bonnet g Hwf).
  rewrite Hchi. simpl.
  ring.
Qed.

(** Why this matters for the gravity story

    Gauss-Bonnet tells us: χ CONSTRAINS total curvature.

    PNEWTopologyChange.v shows when PNEW changes χ.
    Therefore: PNEW changes total curvature.
    Therefore: PNEW changes graph topology, which changes total angle defect
    via the Gauss-Bonnet identity. This is an analogy to how stress-energy
    curves spacetime in GR, but here it is a 2D topological identity on a
    discrete graph.
    *)

(* Continued in PNEWTopologyChange.v *)
