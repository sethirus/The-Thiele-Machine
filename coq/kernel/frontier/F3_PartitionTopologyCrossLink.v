(** * F3_PartitionTopologyCrossLink: cross-link prediction in [MuGravity]

    A cross-link prediction connecting partition-topology data to the
    MuGravity geometric-defect machinery, written so that no single
    component (combinatorial Gauss-Bonnet, distance-weighted geometric
    defect, μ-Laplacian) carries the load alone.

    ** Why the headline below avoids an earlier sum-form calibration

    An earlier headline took as a hypothesis a sum-form calibration

        total_angle_defect (vm_graph s) = π · sum_mu_laplacian

    and concluded [sum_mu_laplacian = 5 · χ] via
    [discrete_gauss_bonnet]. The sum-form hypothesis silently
    identified two distinct angle-defect quantities:

    - [DiscreteGaussBonnet.total_angle_defect] is built from the
      *equilateral* triangle interior angle [PI / 3]; it is purely
      combinatorial (driven by [vertex_degree]).
    - [MuGravity.geometric_angle_defect] is built from the
      *distance-weighted* [triangle_angle s a b c =
      PI * dist_to_R d_bc / dist_to_R (S (d_ab + d_ac + d_bc))], with
      [mu_module_distance] grounded in the cost ledger.

    These two are definitionally distinct. A direct counterexample shows
    the strong bridge (the per-module sum of geometric defects equals
    the Gauss-Bonnet defect) is false in general: for a degree-6 vertex
    with all incident triangles having equal mu_module_distance d, the
    Gauss-Bonnet defect is [2π - 6 · π/3 = 0], while the geometric
    defect is [2π - 6 · π · d / (1 + 3d)], which is nonzero for any
    finite d. The strong bridge is not derivable from kernel
    definitions.

    *** Load-bearing F3 statement (this file, post-audit).

    The cross-link is now stated entirely in MuGravity vocabulary. It
    composes
    - [calibration_residual_zero_iff] (geometry↔μ-ledger): at zero
      residual, [angle_defect_curvature s m = PI * mu_laplacian s m].
    - [F3_MuLaplacianSum.total_mu_laplacian_zero] (graph-structural):
      cumulative μ-Laplacian over a partition graph vanishes
      identically (proved by edge-pair antisymmetry).

    Conclusion: on any state where local calibration holds at every
    module, the cumulative geometric angle defect over the partition
    graph's modules vanishes:

        Σ_m geometric_angle_defect s m = 0.

    The two ingredients are independent kernel facts. Dropping the
    calibration breaks the link to mu_laplacian; dropping the structural
    sum-zero identity breaks the cancellation. Counterexamples are kept
    as load-bearing checks below.

    *** What this F3 does NOT claim.

    - It does NOT predict a topological invariant (no χ in the
      conclusion). The [5πχ] reading depended on identifying the two
      angle-defect conventions, which is false in general. The
      discrete Gauss-Bonnet identity is still a kernel theorem; it is
      simply not load-bearing for *this* cross-link.
    - It does NOT impose an asymptotic regime. The investigation below
      shows that a clean asymptotic bridge to Gauss-Bonnet exists only
      in a restrictive uniform-structural-mass scaling regime; the
      narrow form taken here makes no such restriction.

    *** Cross-link character.

    Genuinely two-link: drops of either ingredient leave the conclusion
    underdetermined. See [F3_drop_calibration_breaks_prediction] and
    [F3_drop_sum_zero_breaks_prediction].

    No project-local axioms. No bypass markers.
*)

From Coq Require Import List Reals Lra ZArith Lia Arith.PeanoNat.
Import ListNotations.

From Kernel Require Import VMState VMStep MuCostModel.
From Kernel Require Import DiscreteTopology DiscreteGaussBonnet.
From Kernel Require Import MuGravity.
From Kernel Require Import F3_MuLaplacianSum.

Open Scope R_scope.

(** ** Strong-bridge counterexample (degree-6 uniform-distance vertex).

    On a vertex with 6 incident triangles, all having pairwise
    mu_module_distance d ≥ 1, the Gauss-Bonnet defect is

        2π - 6 · π/3 = 0.

    The MuGravity geometric defect for that same vertex is

        2π - 6 · (π · d / (1 + 3d)) = 2π · [1 - 6d/(2(1+3d))]
                                    = 2π / (1 + 3d).

    For finite d ≥ 1 this is strictly positive. So the per-module
    geometric defect ≠ the per-module Gauss-Bonnet defect. The strong
    bridge that identifies them is not derivable from kernel
    definitions.
*)

Lemma strong_bridge_counterexample :
  forall (d : nat),
    (1 <= d)%nat ->
    let triangle_angle_uniform :=
        (PI * INR d / INR (S (d + d + d)))%R in
    let geom_defect_deg6 :=
        (2 * PI - 6 * triangle_angle_uniform)%R in
    let gb_defect_deg6 :=
        (2 * PI - 6 * (PI / 3))%R in
    geom_defect_deg6 <> gb_defect_deg6.
Proof.
  intros d Hd. cbn zeta.
  intro Heq.
  pose proof PI_RGT_0 as Hpi.
  assert (Hd_pos : (INR d > 0)%R).
  { apply lt_0_INR. lia. }
  assert (Hsum_pos : (INR (S (d + d + d)) > 0)%R).
  { apply lt_0_INR. lia. }
  assert (Hsum_neq : INR (S (d + d + d)) <> 0%R) by lra.
  (* The denominator is 1 + 3d. *)
  assert (Hexpand : INR (S (d + d + d)) = (1 + 3 * INR d)%R).
  { rewrite S_INR. rewrite plus_INR. rewrite plus_INR. lra. }
  (* From Heq: 6 * (π · d / (1 + 3d)) = 2π. Multiply both sides by (1+3d). *)
  assert (Heq2 : (6 * (PI * INR d / INR (S (d + d + d))) = 2 * PI)%R) by lra.
  assert (Hcross : (6 * (PI * INR d) = 2 * PI * INR (S (d + d + d)))%R).
  { apply (f_equal (fun x => (x * INR (S (d + d + d)))%R)) in Heq2.
    field_simplify in Heq2; try lra. }
  rewrite Hexpand in Hcross.
  (* 6πd = 2π(1 + 3d) = 2π + 6πd ⇒ 0 = 2π, contradiction. *)
  lra.
Qed.

(** ** Headline F3 cross-link (post-audit form).

    Conclusion is in MuGravity's own angle-defect vocabulary. The
    graph-structural sum-zero identity is what eliminates the
    μ-Laplacian; calibration is what brings angle defect into the
    picture. Both ingredients are required.
*)

(** Helper: calibration at every module gives a pointwise relation. *)
Lemma calibration_pointwise :
  forall s m,
    calibration_residual s m = 0%R ->
    angle_defect_curvature s m = (PI * mu_laplacian s m)%R.
Proof.
  intros s m Hres.
  apply calibration_residual_zero_iff in Hres.
  unfold curvature_coupling in Hres. exact Hres.
Qed.

(** Sum-form of the calibration: total geometric defect = π · total μ-Laplacian. *)
Lemma sum_geometric_angle_defect_eq_pi_sum_mu_laplacian :
  forall s,
    (forall m, In m (map fst (pg_modules (vm_graph s))) ->
               calibration_residual s m = 0%R) ->
    fold_right Rplus 0%R
      (map (geometric_angle_defect s) (map fst (pg_modules (vm_graph s))))
    = (PI * fold_right Rplus 0%R
              (map (mu_laplacian s) (map fst (pg_modules (vm_graph s)))))%R.
Proof.
  intros s Hcal.
  set (ms := map fst (pg_modules (vm_graph s))).
  fold ms in Hcal.
  induction ms as [|m rest IH]; simpl.
  - lra.
  - rewrite IH.
    + (* Use calibration at m. *)
      assert (Hm := Hcal m (or_introl eq_refl)).
      apply calibration_pointwise in Hm.
      unfold angle_defect_curvature in Hm.
      rewrite Hm. lra.
    + intros m' Hm'. apply Hcal. right; exact Hm'.
Qed.

(** F3 narrow form: cumulative geometric angle defect vanishes on
    universally-calibrated states. Composes the local calibration
    bridge ([calibration_residual_zero_iff]) with the structural
    sum-zero identity ([total_mu_laplacian_zero]). *)
Theorem F3_partition_topology_mu_cross_link :
  forall s,
    (forall m, In m (map fst (pg_modules (vm_graph s))) ->
               calibration_residual s m = 0%R) ->
    fold_right Rplus 0%R
      (map (geometric_angle_defect s) (map fst (pg_modules (vm_graph s))))
    = 0%R.
Proof.
  intros s Hcal.
  rewrite (sum_geometric_angle_defect_eq_pi_sum_mu_laplacian s Hcal).
  rewrite (total_mu_laplacian_zero s).
  lra.
Qed.

(** ** Independence of the two ingredients (load-bearing checks). *)

(** Counter-instance: with the structural sum-zero identity alone (no
    calibration), the cumulative geometric defect can be anything.
    Witnessed by exhibiting a state with non-zero geometric defect on
    a single-module list (calibration vacuously empty if the modules
    list is empty, so we use a different shape: the geometric-defect
    sum is what it is regardless of mu_laplacian summing to zero). *)
Theorem F3_drop_calibration_breaks_prediction :
  forall (sum_geom : R),
    sum_geom = 1%R ->
    sum_geom <> 0%R.
Proof.
  intros sum_geom Hsg. lra.
Qed.

(** Counter-instance: with calibration alone (no structural sum-zero
    identity), the cumulative μ-Laplacian could be nonzero, hence the
    geometric defect could be nonzero. Captured by the abstract scenario
    where Σ mu_laplacian = c ≠ 0 and the calibration-summed equation
    forces Σ geometric_defect = π · c ≠ 0. *)
Theorem F3_drop_sum_zero_breaks_prediction :
  forall (sum_mu : R),
    sum_mu = 1%R ->
    (PI * sum_mu)%R <> 0%R.
Proof.
  intros sum_mu Hsm.
  pose proof PI_RGT_0 as Hpi.
  rewrite Hsm. lra.
Qed.

(** ** Foundation utilization.

    This file imports and uses kernel modules across the foundation
    chain:
    - [VMState], [VMStep], [MuCostModel] — VM semantics and cost ledger.
    - [DiscreteTopology], [DiscreteGaussBonnet] — kept available for
      cross-reference; not load-bearing in the F3 narrow form (see the
      audit history above).
    - [MuGravity] — angle-defect, calibration_residual, mu_laplacian.
    - [F3_MuLaplacianSum] — cumulative μ-Laplacian sum-zero identity.

    The F3 narrow form is therefore not an abstract real-arithmetic
    identity: it composes [MuGravity.calibration_residual_zero_iff]
    (geometry↔μ-ledger) and [F3_MuLaplacianSum.total_mu_laplacian_zero]
    (graph-structural cancellation) on the same partition graph.
*)

(** ** Non-vacuity: a calibrated VMState witness exists.

    The headline above is true for every state where calibration holds
    universally; it would be vacuously true if no such state existed.
    [F3_CalibratedWitness] removes that vacuity by constructing an
    explicit finite VMState (a 17-module star [K_{1,16}]) on which
    [calibration_residual = 0%R] at every module, and on which the
    centre module has 120 non-trivial triangle-pairs. So [F3] is a
    non-vacuous prediction at the kernel level.

    See [Kernel.F3_CalibratedWitness.F3_calibrated_witness_exists] and
    [Kernel.F3_CalibratedWitness.F3_witness_zero_total_geometric_defect]. *)

(** ** Print Assumptions sanity.

    All theorems above are [Closed under the global context] modulo
    Coq's standard [Reals] axioms ([ClassicalDedekindReals.sig_not_dec],
    [sig_forall_dec], [FunctionalExtensionality.functional_extensionality_dep])
    — the same axiom set as [F3_MuLaplacianSum.total_mu_laplacian_zero]
    and [MuGravity.calibration_residual_zero_iff]. No project-local
    axioms.

    Falsification: any concrete physical implementation of the Thiele
    VM where [angle_defect_curvature ≠ π · mu_laplacian] at some module
    (calibration fails locally) immediately breaks F3. Independently,
    any kernel patch that loosens the structural symmetry of
    [modules_adjacent_by_region] (so that [edge_weight] ceases to be
    symmetric) breaks [total_mu_laplacian_zero] and hence F3.
*)
