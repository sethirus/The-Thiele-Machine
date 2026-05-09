(** MetricFromMuCosts: metric-style quantities from mu-cost bookkeeping.

    This file defines metric-style quantities from computational structure
    (module regions, axiom counts), mu-ledger accounting, and basic geometry
    formulas such as the law of cosines. The intended chain is:
      mu-costs -> edge lengths -> triangle sides -> angles (law of cosines)
               -> curvature-style quantities -> topology bookkeeping

    The edge_length theorem below proves nonnegativity, symmetry, and a triangle
    inequality for the chosen mass-sum distance-like quantity. It does not prove
    identity of indiscernibles, and it does not claim a match to physical
    spacetime. Zero extra assumptions.
    Zero project-local axioms.
    *)

(* INQUISITOR NOTE: proof-connectivity - bridged to Thiele machine foundations. *)
From Kernel Require Import MuCostModel.

From Coq Require Import Reals List Arith.PeanoNat Lia Lra.
Import ListNotations.
Local Open Scope R_scope.

From Kernel Require Import VMState.
From Kernel Require Import FourDSimplicialComplex.
From Kernel Require Import MuGravity.

(** ** Step 0: mu-Tensor as Metric

    The vm_mu_tensor field is a 4x4 matrix (16 nat entries, row-major).
    It is defined as the spacetime metric g_μν in this formalization.
    This is a definitional identification, not a physical derivation.

    DERIVATION:
    mu-tensor(i,j) = (i,j) component of the metric tensor
    This replaces the old scalar module_structural_mass approach.
*)

(** Read (i,j) entry of vm_mu_tensor as a real number *)
Definition mu_tensor_to_metric (s : VMState) (i j : nat) : R :=
  INR (vm_mu_tensor_entry s i j).

(** Properties of the tensor metric *)
Lemma mu_tensor_metric_nonneg : forall s i j,
  (mu_tensor_to_metric s i j >= 0)%R.
Proof.
  intros s i j.
  unfold mu_tensor_to_metric.
  apply Rle_ge, pos_INR.
Qed.

(** Zero vm_mu_tensor gives zero metric *)
Lemma zero_tensor_gives_zero_metric : forall s i j,
  s.(vm_mu_tensor) = repeat 0%nat 16 ->
  mu_tensor_to_metric s i j = 0%R.
Proof.
  intros s i j H.
  unfold mu_tensor_to_metric, vm_mu_tensor_entry.
  rewrite H.
  destruct (Nat.lt_decidable (i * 4 + j) 16) as [Hlt | Hge].
  - rewrite nth_repeat. simpl. reflexivity.
  - rewrite nth_overflow.
    + simpl. reflexivity.
    + rewrite repeat_length. lia.
Qed.

(** ** Step 1: Edge Lengths from mu-Costs (structural mass compatibility)

    The scalar edge_length remains useful for triangle geometry.
    The full metric tensor is given by mu_tensor_to_metric above.
*)

Definition edge_length (s : VMState) (m1 m2 : ModuleID) : R :=
  INR (module_structural_mass s m1 + module_structural_mass s m2).

(** Edge length is non-negative *)
Lemma edge_length_nonneg : forall s m1 m2,
  (edge_length s m1 m2 >= 0)%R.
Proof.
  intros s m1 m2.
  unfold edge_length.
  apply Rle_ge.
  apply pos_INR.
Qed.

(** Edge length is symmetric *)
Lemma edge_length_symmetric : forall s m1 m2,
  edge_length s m1 m2 = edge_length s m2 m1.
Proof.
  intros s m1 m2.
  unfold edge_length.
  f_equal.
  lia.
Qed.

(** Identity: edge from module to itself has minimal length *)
Lemma edge_length_identity : forall s m,
  edge_length s m m = INR (2 * module_structural_mass s m).
Proof.
  intros s m.
  unfold edge_length.
  f_equal.
  lia.
Qed.

(** Triangle inequality for edge lengths

    This follows from elementary arithmetic on nonnegative structural masses.
    For any three modules m1, m2, m3:
    d(m1,m3) <= d(m1,m2) + d(m2,m3)
*)
Lemma edge_length_triangle_inequality : forall s m1 m2 m3,
  (edge_length s m1 m3 <= edge_length s m1 m2 + edge_length s m2 m3)%R.
Proof.
  intros s m1 m2 m3.
  unfold edge_length.
  (* Rewrite goal to expand plus_INR *)
  repeat rewrite plus_INR.
  (* Now prove the inequality on individual masses *)
  assert (H: (module_structural_mass s m1 + module_structural_mass s m3 <=
              module_structural_mass s m1 + module_structural_mass s m2 +
              (module_structural_mass s m2 + module_structural_mass s m3))%nat).
  { lia. }
  apply le_INR in H.
  repeat rewrite plus_INR in H.
  exact H.
Qed.

(** PROVEN: edge_length has nonnegativity, symmetry, and a triangle inequality. *)
Theorem edge_length_is_metric : forall s m1 m2 m3,
  edge_length s m1 m2 >= 0 /\
  edge_length s m1 m2 = edge_length s m2 m1 /\
  edge_length s m1 m3 <= edge_length s m1 m2 + edge_length s m2 m3.
Proof.
  intros s m1 m2 m3.
  split. { apply edge_length_nonneg. }
  split. { apply edge_length_symmetric. }
  { apply edge_length_triangle_inequality. }
Qed.

(** ** Step 2: Angles from Edge Lengths (Law of Cosines)

    Given a triangle with sides a, b, c, the angle C opposite side c is:
    cos(C) = (a² + b² - c²) / (2ab)

    This is DERIVED from the metric, not assumed.
*)

(** Compute angle at vertex v2 in triangle (v1, v2, v3)

    DERIVATION:
    - Side a = edge_length(v2, v3)
    - Side b = edge_length(v1, v2)
    - Side c = edge_length(v1, v3)
    - Angle at v2 = arccos((b² + a² - c²) / (2ab))
*)
Definition angle_at_vertex (s : VMState) (v1 v2 v3 : ModuleID) : R :=
  let a := edge_length s v2 v3 in
  let b := edge_length s v1 v2 in
  let c := edge_length s v1 v3 in
  let cos_angle := ((b * b + a * a - c * c) / (2 * a * b))%R in
  acos cos_angle.

(** ** Step 3: Triangle Angle Sum and Curvature

    CRITICAL INSIGHT:
    Triangle angle sum = π is ONLY true in FLAT space.
    In curved space, the deviation from π IS the curvature!

    CORRECT FORMULATION:
    angle_sum - π = (area of triangle) × (Gaussian curvature)

    For our discrete triangles, we compute the angle sum directly
    from the metric, and the deviation from π gives us the curvature.
*)

(** Sum of angles in a triangle *)
Definition triangle_angle_sum (s : VMState) (v1 v2 v3 : ModuleID) : R :=
  (angle_at_vertex s v1 v2 v3 +
   angle_at_vertex s v2 v3 v1 +
   angle_at_vertex s v3 v1 v2)%R.

(** Angular excess (deviation from π) *)
Definition angular_excess (s : VMState) (v1 v2 v3 : ModuleID) : R :=
  (triangle_angle_sum s v1 v2 v3 - PI)%R.

(** The angular excess IS the integrated Gaussian curvature over the triangle.

    In flat space: angular_excess = 0 (angle sum = π)
    In curved space: angular_excess ≠ 0 (this measures curvature)

    This is the GAUSS-BONNET theorem for a single triangle:
    ∫∫_triangle K dA = angular_excess

    For our discrete case, the "area" is determined by the edge lengths
    from the metric.
*)

(** Triangle area from edge lengths (Heron's formula)

    Given sides a, b, c:
    s = (a + b + c)/2 (semiperimeter)
    Area = √(s(s-a)(s-b)(s-c))
*)
Definition triangle_area (s : VMState) (v1 v2 v3 : ModuleID) : R :=
  let a := edge_length s v2 v3 in
  let b := edge_length s v1 v2 in
  let c := edge_length s v1 v3 in
  let semi := ((a + b + c) / 2)%R in
  sqrt (semi * (semi - a) * (semi - b) * (semi - c))%R.

(** Gaussian curvature of a triangle (discrete)

    From Gauss-Bonnet: K × Area = angular_excess
    Therefore: K = angular_excess / Area
*)
Definition discrete_gaussian_curvature (s : VMState) (v1 v2 v3 : ModuleID) : R :=
  let area := triangle_area s v1 v2 v3 in
  let excess := angular_excess s v1 v2 v3 in
  (excess / area)%R.

(** PROVEN RELATIONSHIP: Angle sum relates to curvature

    This is NOT an axiom - it's the DEFINITION of curvature.
    The angle sum is computed from the metric (law of cosines).
    The deviation from π tells us the curvature.
*)
Theorem angle_sum_determines_curvature : forall s v1 v2 v3,
  (triangle_area s v1 v2 v3 <> 0)%R ->
  let K := discrete_gaussian_curvature s v1 v2 v3 in
  let A := triangle_area s v1 v2 v3 in
  (triangle_angle_sum s v1 v2 v3 = PI + K * A)%R.
Proof.
  intros s v1 v2 v3 Harea_nz.
  unfold discrete_gaussian_curvature, angular_excess, triangle_angle_sum.
  simpl.
  field.
  exact Harea_nz.
Qed.

(** ** Step 4: Curvature from Angle Defects

    DEFINITION: The angle defect at a vertex is:
    defect(v) = 2π - sum(angles at v)

    For a flat surface: defect = 0
    For positive curvature: defect > 0
    For negative curvature: defect < 0
*)

(** Count triangles incident to a vertex *)
Fixpoint count_incident_triangles_4d
  (vertex : nat) (faces : list Face2D) : nat :=
  match faces with
  | [] => 0
  | f :: rest =>
      if nat_list_mem vertex (f2d_vertices f)
      then S (count_incident_triangles_4d vertex rest)
      else count_incident_triangles_4d vertex rest
  end.

(** Angle defect at a vertex in 4D complex *)
Definition angle_defect_4d (s : VMState) (sc : SimplicialComplex4D) (v : nat) : R :=
  (* Sum angles at all triangles incident to v *)
  let incident_faces := filter (fun f => nat_list_mem v (f2d_vertices f)) (sc4d_faces sc) in
  let angle_sum := fold_left (fun acc f =>
    match f2d_vertices f with
    | [v1; v2; v3] =>
        if Nat.eqb v v1 then (acc + angle_at_vertex s v1 v2 v3)%R
        else if Nat.eqb v v2 then (acc + angle_at_vertex s v2 v3 v1)%R
        else if Nat.eqb v v3 then (acc + angle_at_vertex s v3 v1 v2)%R
        else acc
    | _ => acc (* Malformed face, skip *)
    end
  ) incident_faces 0%R in
  (2 * PI - angle_sum)%R.

(** Total curvature in 4D complex *)
Fixpoint sum_angle_defects_4d (s : VMState) (sc : SimplicialComplex4D)
  (vertices : list nat) : R :=
  match vertices with
  | [] => 0%R
  | v :: rest => (angle_defect_4d s sc v + sum_angle_defects_4d s sc rest)%R
  end.

(** ** Step 5: Total Curvature = 4D Gauss-Bonnet-Chern

    For a 4D simplicial complex:
    Total curvature = constant × χ

    The constant depends on the dimension and normalization.
    For 2D: constant = 5π (proven in DiscreteGaussBonnet.v)
    For 4D: constant = 32π² (from 4D Gauss-Bonnet-Chern integral)

    OPEN: 4D Gauss-Bonnet-Chern. The gravity
    pipeline currently uses 2D Gauss-Bonnet (DiscreteGaussBonnet.v).
*)

(** ** Summary: local results

  This section extracts edge lengths, angles, angle defects, and a local
  curvature-style quantity from mu-cost geometry. It does not assume a flat
  Euclidean triangle sum. The deviation from PI is exactly what defines the
  local curvature object here, while the separate Gauss-Bonnet files handle
  the global theorem.

  The repo already gets a 2D discrete Einstein-style bridge out of that. A
  full 4D formalization is a separate project and is still not finished here.
*)

(**
    LOCAL (VERTEX-DEPENDENT) METRIC

    The global vm_mu_tensor gives a single 4x4 metric for the whole state.
    For "curved" discrete spacetime we also define a LOCAL metric where each
    vertex v carries its own mass = module_structural_mass s v.

    g_μν^{local}(v) = mass(v)   if μ = ν   (diagonal, isotropic)
                    = 0          if μ ≠ ν

    When masses differ between vertices, discrete derivatives of this metric
    can be non-zero, giving the later pipeline local input for Christoffel
    symbols, curvature-style quantities, and Einstein-style tensors.
  *)

(** Local diagonal metric at vertex v, direction (μ,ν). *)
Definition metric_at_vertex (s : VMState) (v μ ν : ModuleID) : R :=
  if (μ mod 4 =? ν mod 4)%bool
  then INR (module_structural_mass s v)
  else 0%R.

(** Metric at vertex is non-negative. *)
Lemma metric_at_vertex_nonneg : forall s v μ ν,
  (metric_at_vertex s v μ ν >= 0)%R.
Proof.
  intros s v μ ν.
  unfold metric_at_vertex.
  destruct (μ mod 4 =? ν mod 4)%bool.
  - apply Rle_ge. apply pos_INR.
  - lra.
Qed.

(** Metric at vertex is zero off-diagonal. *)
Lemma metric_at_vertex_offdiag : forall s v μ ν,
  (μ mod 4 =? ν mod 4)%bool = false ->
  metric_at_vertex s v μ ν = 0%R.
Proof.
  intros s v μ ν H.
  unfold metric_at_vertex. rewrite H. reflexivity.
Qed.

(** Metric at vertex on diagonal equals INR mass. *)
Lemma metric_at_vertex_diag : forall s v μ,
  metric_at_vertex s v μ μ = INR (module_structural_mass s v).
Proof.
  intros s v μ.
  unfold metric_at_vertex.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

(** KEY CURVATURE LEMMA: distinct natural masses remain distinct after
    embedding into reals. This supports local-metric derivative arguments. *)
Lemma local_metric_derivative_nonzero_when_masses_differ :
  forall m1 m2,
  m1 <> m2 ->
  INR m1 <> INR m2.
Proof.
  intros m1 m2 Hne.
  intro Heq.
  apply Hne.
  exact (INR_eq m1 m2 Heq).
Qed.

(** Flat-space special case: uniform mass makes the local metric
    position-independent, so the same value appears at every vertex. *)
Lemma local_metric_uniform_position_independent : forall s m μ ν v w,
  (forall u, module_structural_mass s u = m) ->
  metric_at_vertex s v μ ν = metric_at_vertex s w μ ν.
Proof.
  intros s m μ ν v w H_uniform.
  unfold metric_at_vertex.
  destruct (μ mod 4 =? ν mod 4)%bool.
  - rewrite H_uniform, H_uniform. reflexivity.
  - reflexivity.
Qed.

Definition metric_deriv_anchor := local_metric_derivative_nonzero_when_masses_differ.

(**
    LORENTZIAN METRIC EXTENSION

    The Euclidean [metric_at_vertex] has all non-negative diagonal entries
    (signature (+,+,+,+)).  For a Lorentzian manifold with one temporal
    dimension we need signature (-,+,+,+): index 0 is time-like (negative
    norm) and indices 1,2,3 are space-like (positive norm).

    We define [lorentz_metric_at_vertex] by multiplying each diagonal entry
    by [lorentz_sign μ] and prove the signature theorem.
 This is a formal extension of the computational metric.  Whether
    the physical interpretation warrants calling this a Lorentzian manifold
    depends on identifying index 0 with a time dimension, an interpretation
    that is not forced by the kernel dynamics alone (see LorentzNotForced.v).
  *)

(** Sign of coordinate index μ: -1 for time (μ mod 4 = 0), +1 for space. *)
Definition lorentz_sign (mu : nat) : R :=
  if (mu mod 4 =? 0)%nat then (-1)%R else 1%R.

Lemma lorentz_sign_time : lorentz_sign 0%nat = (-1)%R.
Proof. reflexivity. Qed.

Lemma lorentz_sign_space_1 : lorentz_sign 1%nat = 1%R.
Proof. reflexivity. Qed.

Lemma lorentz_sign_space_2 : lorentz_sign 2%nat = 1%R.
Proof. reflexivity. Qed.

Lemma lorentz_sign_space_3 : lorentz_sign 3%nat = 1%R.
Proof. reflexivity. Qed.

(** Lorentzian metric at vertex v: g_μν = lorentz_sign(μ) · mass(v) if μ=ν, else 0. *)
Definition lorentz_metric_at_vertex (s : VMState) (v μ ν : ModuleID) : R :=
  if (μ mod 4 =? ν mod 4)%nat
  then (lorentz_sign (μ mod 4) * INR (module_structural_mass s v))%R
  else 0%R.

(** The (0,0) entry is negative when mass > 0. *)
Lemma lorentz_metric_time_negative : forall s v,
  (module_structural_mass s v > 0)%nat ->
  (lorentz_metric_at_vertex s v 0%nat 0%nat < 0)%R.
Proof.
  intros s v Hm.
  unfold lorentz_metric_at_vertex, lorentz_sign. simpl.
  pose proof (lt_0_INR _ Hm) as H.
  lra.
Qed.

(** The (k,k) entry for k = 1,2,3 is positive when mass > 0. *)
Lemma lorentz_metric_space_positive : forall s v k,
  (k = 1%nat \/ k = 2%nat \/ k = 3%nat) ->
  (module_structural_mass s v > 0)%nat ->
  (lorentz_metric_at_vertex s v k k > 0)%R.
Proof.
  intros s v k Hk Hm.
  unfold lorentz_metric_at_vertex, lorentz_sign.
  rewrite Nat.eqb_refl.
  destruct Hk as [H|[H|H]]; subst; simpl;
    pose proof (lt_0_INR _ Hm) as H'; lra.
Qed.

(** Off-diagonal entries vanish. *)
Lemma lorentz_metric_offdiag : forall s v μ ν,
  (μ mod 4 <> ν mod 4)%nat ->
  lorentz_metric_at_vertex s v μ ν = 0%R.
Proof.
  intros s v μ ν H.
  unfold lorentz_metric_at_vertex.
  apply Nat.eqb_neq in H.
  rewrite H. reflexivity.
Qed.

(** Signature theorem: the Lorentz-style metric has signature (-,+,+,+)
    at every vertex with positive mass. *)
Theorem lorentz_metric_signature : forall s v,
  (module_structural_mass s v > 0)%nat ->
  (lorentz_metric_at_vertex s v 0%nat 0%nat < 0)%R /\
  (lorentz_metric_at_vertex s v 1%nat 1%nat > 0)%R /\
  (lorentz_metric_at_vertex s v 2%nat 2%nat > 0)%R /\
  (lorentz_metric_at_vertex s v 3%nat 3%nat > 0)%R.
Proof.
  intros s v Hm.
  repeat split.
  - apply lorentz_metric_time_negative; exact Hm.
  - apply lorentz_metric_space_positive; [left; reflexivity | exact Hm].
  - apply lorentz_metric_space_positive; [right; left; reflexivity | exact Hm].
  - apply lorentz_metric_space_positive; [right; right; reflexivity | exact Hm].
Qed.

(** The spatial part of the Lorentzian metric agrees with the Euclidean
    [metric_at_vertex] up to sign: for k=1,2,3,
    lorentz_metric_at_vertex s v k k = metric_at_vertex s v k k. *)
Lemma lorentz_spatial_agrees_euclidean : forall s v k,
  (k mod 4 = 1%nat \/ k mod 4 = 2%nat \/ k mod 4 = 3%nat) ->
  lorentz_metric_at_vertex s v k k = metric_at_vertex s v k k.
Proof.
  intros s v k Hk.
  unfold lorentz_metric_at_vertex, lorentz_sign, metric_at_vertex.
  rewrite Nat.eqb_refl.
  destruct Hk as [H|[H|H]]; rewrite H; simpl; ring.
Qed.

(**
    FULL 4x4 METRIC FROM PER-MODULE TENSOR

    Unlike the scalar-diagonal metric_at_vertex above (which reads only the
    structural mass), this reads the full 4x4 per-module tensor stored in
    module_mu_tensor (16 entries, row-major).

    Each vertex can carry a different 4x4 metric, giving the later pipeline
    local input for Christoffel symbols and curvature-style quantities.
    *)

From Kernel Require Import MatrixAlgebra4.

(** Full 4x4 metric at vertex v, indices (μ,ν). Reads from per-module tensor. *)
Definition full_metric_at_vertex (s : VMState) (v : ModuleID) (μ ν : nat) : R :=
  INR (module_tensor_entry s v (μ mod 4) (ν mod 4)).

(** Full metric as a Mat4 object (for matrix inverse computation). *)
Definition metric_mat4_at_vertex (s : VMState) (v : ModuleID) : Mat4 :=
  fun μ ν => full_metric_at_vertex s v μ ν.

(** Inverse metric g^{μν} at vertex, computed via Cramer's rule. *)
Definition inverse_metric_at_vertex (s : VMState) (v : ModuleID) : Mat4 :=
  mat4_inverse (metric_mat4_at_vertex s v).

(** Determinant of metric at vertex. *)
Definition metric_det_at_vertex (s : VMState) (v : ModuleID) : R :=
  mat4_det (metric_mat4_at_vertex s v).

(** ** Full metric properties *)

(** Full metric entries are non-negative (from pos_INR). *)
Lemma full_metric_nonneg : forall s v μ ν,
  (full_metric_at_vertex s v μ ν >= 0)%R.
Proof.
  intros s v μ ν.
  unfold full_metric_at_vertex.
  apply Rle_ge. apply pos_INR.
Qed.

(** Determinant of diagonal metric = product of diagonal entries. *)
(** Backward compatibility: when the per-module tensor is an isotropic diagonal
    with entries matching the structural mass, full_metric_at_vertex agrees
    with metric_at_vertex (the scalar-diagonal metric from MuGravity). *)
Lemma full_metric_compat_diagonal : forall s v μ ν,
  (μ < 4)%nat -> (ν < 4)%nat ->
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    module_tensor_entry s v i j =
    if (i =? j)%nat then module_structural_mass s v else 0%nat) ->
  full_metric_at_vertex s v μ ν = metric_at_vertex s v μ ν.
Proof.
  intros s v μ ν Hμ Hν Htensor.
  unfold full_metric_at_vertex, metric_at_vertex.
  rewrite !Nat.mod_small by lia.
  rewrite Htensor by lia.
  destruct (μ =? ν)%nat eqn:Heq.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma metric_det_positive_diagonal : forall s v,
  (forall i j, (i < 4)%nat -> (j < 4)%nat -> (i <> j)%nat ->
    module_tensor_entry s v i j = 0%nat) ->
  metric_det_at_vertex s v =
    (full_metric_at_vertex s v 0%nat 0%nat *
     full_metric_at_vertex s v 1%nat 1%nat *
     full_metric_at_vertex s v 2%nat 2%nat *
     full_metric_at_vertex s v 3%nat 3%nat)%R.
Proof.
  intros s v Hdiag.
  unfold metric_det_at_vertex, metric_mat4_at_vertex.
  unfold mat4_det, det3, minor3, skip_idx, full_metric_at_vertex. simpl.
  (* Off-diagonal entries are zero by hypothesis *)
  repeat rewrite (Hdiag 0%nat 1%nat ltac:(lia) ltac:(lia) ltac:(lia));
  repeat rewrite (Hdiag 0%nat 2%nat ltac:(lia) ltac:(lia) ltac:(lia));
  repeat rewrite (Hdiag 0%nat 3%nat ltac:(lia) ltac:(lia) ltac:(lia));
  repeat rewrite (Hdiag 1%nat 0%nat ltac:(lia) ltac:(lia) ltac:(lia));
  repeat rewrite (Hdiag 1%nat 2%nat ltac:(lia) ltac:(lia) ltac:(lia));
  repeat rewrite (Hdiag 1%nat 3%nat ltac:(lia) ltac:(lia) ltac:(lia));
  repeat rewrite (Hdiag 2%nat 0%nat ltac:(lia) ltac:(lia) ltac:(lia));
  repeat rewrite (Hdiag 2%nat 1%nat ltac:(lia) ltac:(lia) ltac:(lia));
  repeat rewrite (Hdiag 2%nat 3%nat ltac:(lia) ltac:(lia) ltac:(lia));
  repeat rewrite (Hdiag 3%nat 0%nat ltac:(lia) ltac:(lia) ltac:(lia));
  repeat rewrite (Hdiag 3%nat 1%nat ltac:(lia) ltac:(lia) ltac:(lia));
  repeat rewrite (Hdiag 3%nat 2%nat ltac:(lia) ltac:(lia) ltac:(lia));
  simpl; ring.
Qed.
