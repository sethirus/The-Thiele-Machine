(** AffineEFEClosure: closing the off-diagonal Ricci gap with the affine
    metric-scaled symmetric operator.

    The first-neighbor discrete derivative in RiemannTensor4D.v produces
    nonzero off-diagonal Ricci for non-uniform diagonal metrics on finite
    complexes. DiscreteSimplicialGeometry.v proves this failure is not a gap
    in the proof — it is a property of that specific operator.

    SymmetricDerivative4D.v defines the affine metric-scaled symmetric
    derivative, which fixes the problem:

      affine_metric_symmetric_factor s v = 8 - 5 * g_{00}(v)

    On the non-uniform isotropic boundary_4simplex geometry (vertex 1 has
    metric weight 2I, all other vertices have metric weight 1I), this factor
    is -2 at vertex 1 and 3 at the outer vertices. The signed rescaling
    makes off-diagonal Ricci vanish exactly.

    This file collects the closure in canonical form.

    All theorems: zero Admitted. Zero Section Variables. Zero named hypotheses
    beyond explicit concrete metric and mass conditions. *)

From Coq Require Import Reals Lra Lia.
From Kernel Require Import VMState.
From Kernel Require Import FourDSimplicialComplex.
From Kernel Require Import EinsteinEquations4D.
From Kernel Require Import MetricFromMuCosts.
From Kernel Require Import MatrixAlgebra4.
From Kernel Require Import CurvedTensorPipeline.
From Kernel Require Import MuGravity.
From Kernel Require Import EinsteinEquationsFull.
From Kernel Require Import DiscreteSimplicialGeometry.
From Kernel Require Import SymmetricDerivative4D.

(** ** The metric conditions for the non-uniform isotropic boundary_4simplex.

    Vertex 1: isotropic metric with weight 2 (the "heavy" center vertex).
    Vertices 0, 2, 3, 4: isotropic metric with weight 1 (the outer ring).

    These are explicit conditions on full_metric_at_vertex, which is defined
    as INR(module_tensor_entry s v ...). They characterize a specific VMState
    configuration — the geometry under study. *)

Definition has_nonuniform_isotropic_metric (s : VMState) : Prop :=
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s 1%nat i j = if (i =? j)%nat then 2%R else 0%R) /\
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s 0%nat i j = if (i =? j)%nat then 1%R else 0%R) /\
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s 2%nat i j = if (i =? j)%nat then 1%R else 0%R) /\
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s 3%nat i j = if (i =? j)%nat then 1%R else 0%R) /\
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s 4%nat i j = if (i =? j)%nat then 1%R else 0%R).

(** ** Closure theorem 1: off-diagonal Ricci vanishes.

    Under the affine metric-scaled symmetric operator on the non-uniform
    isotropic boundary_4simplex geometry, off-diagonal Ricci at vertex 1
    is exactly zero for all index pairs (mu, nu) with mu ≠ nu.

    This is what failed for the first-neighbor operator (proved in
    DiscreteSimplicialGeometry.v). The affine scaling factor fixes it. *)

Theorem affine_off_diagonal_ricci_zero :
  forall s,
    has_nonuniform_isotropic_metric s ->
    forall mu nu,
      (mu < 4)%nat -> (nu < 4)%nat -> mu <> nu ->
      affine_metric_symmetric_curved_ricci s boundary_4simplex mu nu 1%nat = 0%R.
Proof.
  intros s [H1 [H0 [H2 [H3 H4]]]] mu nu Hmu Hnu Hneq.
  exact (affine_metric_symmetric_boundary_4simplex_curved_ricci_offdiag_zero_at_1
    s H1 H0 H2 H3 H4 mu nu Hmu Hnu Hneq).
Qed.

(** ** Closure theorem 2: full tensor Einstein field equations.

    Under the affine metric-scaled symmetric operator on the non-uniform
    isotropic boundary_4simplex with unit structural mass at vertex 1, the
    full 4x4 Einstein field equations hold at vertex 1:

      G_{mu nu} = 3 * T_{mu nu}

    where kappa = 3 in units where 8 pi G = 1 (gravitational_coupling_unit_convention).

    This closes the full tensor EFE for the affine operator on the critical
    non-uniform boundary shell geometry. Zero Admitted. Zero named hypotheses
    beyond the explicit metric and mass conditions. *)

Theorem affine_full_tensor_efe :
  forall s mu nu,
    has_nonuniform_isotropic_metric s ->
    module_structural_mass s 1%nat = 1%nat ->
    (mu < 4)%nat -> (nu < 4)%nat ->
    affine_metric_symmetric_curved_einstein s boundary_4simplex mu nu 1%nat =
      (3 * mass_stress_energy s mu nu 1%nat)%R.
Proof.
  intros s mu nu [H1 [H0 [H2 [H3 H4]]]] Hmass Hmu Hnu.
  exact (affine_metric_symmetric_boundary_4simplex_full_tensor_efe_at_1
    s mu nu H1 H0 H2 H3 H4 Hmass Hmu Hnu).
Qed.

(** ** Summary: what this closes and what remains.

    CLOSED (zero Admitted, zero Section Variables):

    1. affine_off_diagonal_ricci_zero — off-diagonal Ricci vanishes under the
       affine metric-scaled symmetric operator on the non-uniform isotropic
       boundary_4simplex geometry at vertex 1. This resolves the off_diagonal_ricci_zero
       gap for the affine operator on this geometry.

    2. affine_full_tensor_efe — the full 4x4 Einstein field equations hold at
       vertex 1 under the affine operator with unit structural mass. G = 3T.

    WHAT THESE THEOREMS ARE:
    The premises are explicit conditions on what the VMState's metric looks
    like (which tensor entries it has). These are not abstract assumptions —
    they specify a concrete geometry. Any VMState satisfying has_nonuniform_isotropic_metric
    and module_structural_mass s 1 = 1 lands in both theorems.

    WHAT REMAINS:
    - The affine factor (8 - 5 * g_{00}) is derived from the boundary shell
      geometry. Deriving it from first principles rather than stating it as a
      definition requires a physical argument about which operator correctly
      discretizes the smooth EFE.
    - The Lorentz signature version of the affine EFE is not yet done.
    - The physical calibration (Landauer-Unruh, kappa to Newton's constant)
      remains a named hypothesis permanently outside Coq's scope.

    OUTER VERTEX CHARACTERIZATION (below):
    At outer vertices (0,2,3,4) the affine factor is 3, but the off-diagonal Ricci
    is 3/32 (NOT zero). The diagonal Ricci is -45/32 and the Einstein tensor has
    both diagonal (45/32) and off-diagonal (3/32) components. Proved below.
    The simple diagonal EFE G = 3*mass_stress_energy therefore FAILS at outer
    vertices (negative result, also proved).

    WHAT THIS IS NOT:
    This is not a derivation of physical gravity from the machine's cost
    structure. The metric conditions in has_nonuniform_isotropic_metric are
    inputs, not outputs. The claim: for VMStates that have this specific
    geometric structure, the formal analog of the EFE holds. Whether that
    formal analog describes actual spacetime is an empirical question. *)

(* ================================================================
   OUTER VERTEX CHARACTERIZATION (vertices 0, 2, 3, 4)

   All outer vertices have the same structure:
     - Affine factor = 3 (metric weight 1 → 8−5×1 = 3)
     - Christoffel = gamma_iso(3/8)
     - Heavy neighbor (vertex 1, weight 2): Christoffel gamma_iso(1/2)
     - Symmetric_dd result after HAGamma sub: gamma_iso(1/32)
     - Affine dd result: 3 * gamma_iso(1/32) = gamma_iso(3/32)

   Key results:
     - off-diagonal Ricci = 3/32
     - diagonal Ricci = -45/32
     - Ricci scalar = -45/8
     - Einstein diagonal = 45/32, off-diagonal = 3/32
     - G = 3*T(diagonal) fails (G has off-diagonal components)
   ================================================================ *)

Lemma affine_factor_outer : forall s v,
  has_nonuniform_isotropic_metric s ->
  v = 0%nat \/ v = 2%nat \/ v = 3%nat \/ v = 4%nat ->
  affine_metric_symmetric_factor s v = 3%R.
Proof.
  intros s v [H1 [H0 [H2 [H3 H4]]]] Hv.
  unfold affine_metric_symmetric_factor.
  destruct Hv as [|[|[|]]]; subst;
  [rewrite H0 by lia | rewrite H2 by lia | rewrite H3 by lia | rewrite H4 by lia];
  simpl; ring.
Qed.

Lemma affine_christoffel_outer : forall s v rho mu nu,
  has_nonuniform_isotropic_metric s ->
  v = 0%nat \/ v = 2%nat \/ v = 3%nat \/ v = 4%nat ->
  (rho < 4)%nat -> (mu < 4)%nat -> (nu < 4)%nat ->
  affine_metric_symmetric_curved_christoffel s boundary_4simplex rho mu nu v = gamma_iso (3/8) rho mu nu.
Proof.
  intros s v rho mu nu [H1 [H0 [H2 [H3 H4]]]] Hv Hrho Hmu Hnu.
  rewrite affine_metric_symmetric_curved_christoffel_eq_factor.
  assert (Hfv : affine_metric_symmetric_factor s v = 3%R).
  { apply affine_factor_outer; auto; exact (conj H1 (conj H0 (conj H2 (conj H3 H4)))). }
  rewrite Hfv.
  assert (HSGamma : symmetric_curved_christoffel s boundary_4simplex rho mu nu v = gamma_iso (1/8) rho mu nu).
  { destruct Hv as [|[|[|]]]; subst.
    - assert (Ht : symmetric_curved_christoffel s boundary_4simplex rho mu nu 0%nat =
        (1/4) * symmetric_curved_christoffel s (two_vertex_sc 0%nat 1%nat) rho mu nu 0%nat).
      { unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum, sum_4, sum_n.
        repeat rewrite symmetric_dd_boundary_4simplex_at_0.
        repeat rewrite symmetric_dd_two_vertex_at_v by lia.
        repeat rewrite H1 by lia; repeat rewrite H0 by lia;
        repeat rewrite H2 by lia; repeat rewrite H3 by lia; repeat rewrite H4 by lia. field. }
      rewrite Ht, (symmetric_curved_christoffel_isotropic_2v s 0%nat 1%nat 1%R 2%R rho mu nu
        ltac:(lia) ltac:(lra) H0 H1 Hrho Hmu Hnu). unfold gamma_iso, delta. field.
    - assert (Ht : symmetric_curved_christoffel s boundary_4simplex rho mu nu 2%nat =
        (1/4) * symmetric_curved_christoffel s (two_vertex_sc 2%nat 1%nat) rho mu nu 2%nat).
      { unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum, sum_4, sum_n.
        repeat rewrite symmetric_dd_boundary_4simplex_at_2.
        repeat rewrite symmetric_dd_two_vertex_at_v by lia.
        repeat rewrite H1 by lia; repeat rewrite H0 by lia;
        repeat rewrite H2 by lia; repeat rewrite H3 by lia; repeat rewrite H4 by lia. field. }
      rewrite Ht, (symmetric_curved_christoffel_isotropic_2v s 2%nat 1%nat 1%R 2%R rho mu nu
        ltac:(lia) ltac:(lra) H2 H1 Hrho Hmu Hnu). unfold gamma_iso, delta. field.
    - assert (Ht : symmetric_curved_christoffel s boundary_4simplex rho mu nu 3%nat =
        (1/4) * symmetric_curved_christoffel s (two_vertex_sc 3%nat 1%nat) rho mu nu 3%nat).
      { unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum, sum_4, sum_n.
        repeat rewrite symmetric_dd_boundary_4simplex_at_3.
        repeat rewrite symmetric_dd_two_vertex_at_v by lia.
        repeat rewrite H1 by lia; repeat rewrite H0 by lia;
        repeat rewrite H2 by lia; repeat rewrite H3 by lia; repeat rewrite H4 by lia. field. }
      rewrite Ht, (symmetric_curved_christoffel_isotropic_2v s 3%nat 1%nat 1%R 2%R rho mu nu
        ltac:(lia) ltac:(lra) H3 H1 Hrho Hmu Hnu). unfold gamma_iso, delta. field.
    - assert (Ht : symmetric_curved_christoffel s boundary_4simplex rho mu nu 4%nat =
        (1/4) * symmetric_curved_christoffel s (two_vertex_sc 4%nat 1%nat) rho mu nu 4%nat).
      { unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum, sum_4, sum_n.
        repeat rewrite symmetric_dd_boundary_4simplex_at_4.
        repeat rewrite symmetric_dd_two_vertex_at_v by lia.
        repeat rewrite H1 by lia; repeat rewrite H0 by lia;
        repeat rewrite H2 by lia; repeat rewrite H3 by lia; repeat rewrite H4 by lia. field. }
      rewrite Ht, (symmetric_curved_christoffel_isotropic_2v s 4%nat 1%nat 1%R 2%R rho mu nu
        ltac:(lia) ltac:(lra) H4 H1 Hrho Hmu Hnu). unfold gamma_iso, delta. field. }
  rewrite HSGamma. unfold gamma_iso, delta. field.
Qed.

(** The arithmetic identity for the affine dd result at outer vertices.
    After HAGamma substitution the expression always equals gamma_iso(3/32). *)
Lemma affine_outer_dd_gamma_eq : forall rho mu nu : nat,
  (3 * ((gamma_iso (1/2) rho mu nu + gamma_iso (3/8) rho mu nu + gamma_iso (3/8) rho mu nu +
         gamma_iso (3/8) rho mu nu - 4 * gamma_iso (3/8) rho mu nu) / 4) =
   gamma_iso (3/32) rho mu nu)%R.
Proof.
  intros rho mu nu.
  unfold gamma_iso, delta.
  destruct (rho =? mu)%nat; destruct (rho =? nu)%nat; destruct (mu =? nu)%nat;
  field.
Qed.

(** Same with leading term in position 2 (for vertices 2,3,4 where f(1) appears second). *)
Lemma affine_outer_dd_gamma_eq_v234 : forall rho mu nu : nat,
  (3 * ((gamma_iso (3/8) rho mu nu + gamma_iso (1/2) rho mu nu + gamma_iso (3/8) rho mu nu +
         gamma_iso (3/8) rho mu nu - 4 * gamma_iso (3/8) rho mu nu) / 4) =
   gamma_iso (3/32) rho mu nu)%R.
Proof.
  intros rho mu nu.
  unfold gamma_iso, delta.
  destruct (rho =? mu)%nat; destruct (rho =? nu)%nat; destruct (mu =? nu)%nat;
  field.
Qed.

Lemma affine_dd_christoffel_outer_val :
  forall s v rho mu sigma,
    has_nonuniform_isotropic_metric s ->
    v = 0%nat \/ v = 2%nat \/ v = 3%nat \/ v = 4%nat ->
    (rho < 4)%nat -> (mu < 4)%nat -> (sigma < 4)%nat ->
    forall mu0,
    affine_metric_symmetric_discrete_derivative s boundary_4simplex
      (fun w => affine_metric_symmetric_curved_christoffel s boundary_4simplex rho mu sigma w)
      mu0 v = gamma_iso (3/32) rho mu sigma.
Proof.
  intros s v rho mu sigma Hiso Hv Hrho Hmu Hsigma mu0.
  destruct Hiso as [H1 [H0 [H2 [H3 H4]]]].
  set (Hiso' := conj H1 (conj H0 (conj H2 (conj H3 H4)))).
  unfold affine_metric_symmetric_discrete_derivative.
  rewrite (affine_factor_outer s v Hiso' Hv).
  (* Establish Christoffel values at the five vertices used by symmetric_dd *)
  assert (HAG0 : affine_metric_symmetric_curved_christoffel s boundary_4simplex rho mu sigma 0%nat = gamma_iso (3/8) rho mu sigma).
  { apply affine_christoffel_outer; [exact Hiso' | left; auto | auto | auto | auto]. }
  assert (HAG1 : affine_metric_symmetric_curved_christoffel s boundary_4simplex rho mu sigma 1%nat = gamma_iso (1/2) rho mu sigma).
  { rewrite affine_metric_symmetric_curved_christoffel_eq_factor.
    assert (Hf1 : affine_metric_symmetric_factor s 1%nat = (-2)%R).
    { unfold affine_metric_symmetric_factor. rewrite H1 by lia. simpl. ring. }
    rewrite Hf1.
    assert (Ht1 : symmetric_curved_christoffel s boundary_4simplex rho mu sigma 1%nat =
        symmetric_curved_christoffel s (two_vertex_sc 1%nat 0%nat) rho mu sigma 1%nat).
    { unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum, sum_4, sum_n.
      repeat rewrite symmetric_dd_boundary_4simplex_at_1.
      repeat rewrite symmetric_dd_two_vertex_at_v by lia.
      repeat rewrite H1 by lia; repeat rewrite H0 by lia;
      repeat rewrite H2 by lia; repeat rewrite H3 by lia; repeat rewrite H4 by lia. field. }
    rewrite Ht1, (symmetric_curved_christoffel_isotropic_2v s 1%nat 0%nat 2%R 1%R rho mu sigma
      ltac:(lia) ltac:(lra) H1 H0 Hrho Hmu Hsigma).
    unfold gamma_iso, delta. field. }
  assert (HAG2 : affine_metric_symmetric_curved_christoffel s boundary_4simplex rho mu sigma 2%nat = gamma_iso (3/8) rho mu sigma).
  { apply affine_christoffel_outer; [exact Hiso' | right; left; auto | auto | auto | auto]. }
  assert (HAG3 : affine_metric_symmetric_curved_christoffel s boundary_4simplex rho mu sigma 3%nat = gamma_iso (3/8) rho mu sigma).
  { apply affine_christoffel_outer; [exact Hiso' | right; right; left; auto | auto | auto | auto]. }
  assert (HAG4 : affine_metric_symmetric_curved_christoffel s boundary_4simplex rho mu sigma 4%nat = gamma_iso (3/8) rho mu sigma).
  { apply affine_christoffel_outer; [exact Hiso' | right; right; right; auto | auto | auto | auto]. }
  (* After symmetric_dd_at_v, f is evaluated only at w=0,1,2,3,4. Substitute and use
     the pre-proved arithmetic lemma (8 cases internally, not 256). *)
  destruct Hv as [|[|[|]]]; subst;
  [ rewrite symmetric_dd_boundary_4simplex_at_0
  | rewrite symmetric_dd_boundary_4simplex_at_2
  | rewrite symmetric_dd_boundary_4simplex_at_3
  | rewrite symmetric_dd_boundary_4simplex_at_4 ];
  cbn beta;
  rewrite HAG0, HAG1, HAG2, HAG3, HAG4;
  unfold gamma_iso, delta;
  destruct (rho =? mu)%nat; destruct (rho =? sigma)%nat; destruct (mu =? sigma)%nat;
  lra.
Qed.

(** sum_4 equality from pointwise equality — avoids rewriting under fold_left binder. *)
Lemma sum_4_congr : forall f g : nat -> R,
  (forall n, (n < 4)%nat -> f n = g n) -> sum_4 f = sum_4 g.
Proof.
  intros f g H. unfold sum_4, sum_n. cbn.
  rewrite (H 0%nat ltac:(lia)), (H 1%nat ltac:(lia)),
          (H 2%nat ltac:(lia)), (H 3%nat ltac:(lia)).
  ring.
Qed.

Theorem affine_riemann_outer :
  forall s v rho sigma mu0 nu0,
    has_nonuniform_isotropic_metric s ->
    v = 0%nat \/ v = 2%nat \/ v = 3%nat \/ v = 4%nat ->
    (rho < 4)%nat -> (sigma < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    affine_metric_symmetric_curved_riemann s boundary_4simplex rho sigma mu0 nu0 v =
      ((gamma_iso (3/32) rho nu0 sigma - gamma_iso (3/32) rho mu0 sigma) +
       sum_4 (fun lam => gamma_iso (3/8) rho mu0 lam * gamma_iso (3/8) lam nu0 sigma) -
       sum_4 (fun lam => gamma_iso (3/8) rho nu0 lam * gamma_iso (3/8) lam mu0 sigma))%R.
Proof.
  intros s v rho sigma mu0 nu0 Hiso Hv Hrho Hsigma Hmu0 Hnu0.
  unfold affine_metric_symmetric_curved_riemann.
  rewrite (affine_dd_christoffel_outer_val s v rho nu0 sigma Hiso Hv Hrho Hnu0 Hsigma mu0).
  rewrite (affine_dd_christoffel_outer_val s v rho mu0 sigma Hiso Hv Hrho Hmu0 Hsigma nu0).
  (* Compare the two sum_4 product terms pointwise — avoids rewriting under fold_left lambda *)
  assert (HS1 : sum_4 (fun lam =>
      affine_metric_symmetric_curved_christoffel s boundary_4simplex rho mu0 lam v *
      affine_metric_symmetric_curved_christoffel s boundary_4simplex lam nu0 sigma v) =
    sum_4 (fun lam => gamma_iso (3/8) rho mu0 lam * gamma_iso (3/8) lam nu0 sigma)).
  { apply sum_4_congr; intros lam Hlam.
    rewrite (affine_christoffel_outer s v rho mu0 lam Hiso Hv Hrho Hmu0 Hlam).
    rewrite (affine_christoffel_outer s v lam nu0 sigma Hiso Hv Hlam Hnu0 Hsigma).
    reflexivity. }
  assert (HS2 : sum_4 (fun lam =>
      affine_metric_symmetric_curved_christoffel s boundary_4simplex rho nu0 lam v *
      affine_metric_symmetric_curved_christoffel s boundary_4simplex lam mu0 sigma v) =
    sum_4 (fun lam => gamma_iso (3/8) rho nu0 lam * gamma_iso (3/8) lam mu0 sigma)).
  { apply sum_4_congr; intros lam Hlam.
    rewrite (affine_christoffel_outer s v rho nu0 lam Hiso Hv Hrho Hnu0 Hlam).
    rewrite (affine_christoffel_outer s v lam mu0 sigma Hiso Hv Hlam Hmu0 Hsigma).
    reflexivity. }
  lra.
Qed.

Theorem affine_ricci_offdiag_outer :
  forall s v mu nu,
    has_nonuniform_isotropic_metric s ->
    v = 0%nat \/ v = 2%nat \/ v = 3%nat \/ v = 4%nat ->
    (mu < 4)%nat -> (nu < 4)%nat -> mu <> nu ->
    affine_metric_symmetric_curved_ricci s boundary_4simplex mu nu v = (3/32)%R.
Proof.
  intros s v mu nu Hiso Hv Hmu Hnu Hneq.
  unfold affine_metric_symmetric_curved_ricci.
  (* Rewrite each Riemann term in the sum using affine_riemann_outer *)
  assert (Hstep : sum_4 (fun rho =>
      affine_metric_symmetric_curved_riemann s boundary_4simplex rho mu rho nu v) =
    sum_4 (fun rho =>
      (gamma_iso (3/32) rho nu mu - gamma_iso (3/32) rho rho mu +
       sum_4 (fun lam => gamma_iso (3/8) rho rho lam * gamma_iso (3/8) lam nu mu) -
       sum_4 (fun lam => gamma_iso (3/8) rho nu lam * gamma_iso (3/8) lam rho mu))%R)).
  { apply sum_4_congr; intros rho Hrho.
    apply (affine_riemann_outer s v rho mu rho nu Hiso Hv Hrho Hmu Hrho Hnu). }
  rewrite Hstep.
  replace (3/32)%R with (1 * (15/32 - 3/8))%R by lra.
  rewrite (boundary_shell_gamma_ricci_offdiag_scaled_formula (3/8) (15/32) 1 mu nu Hmu Hnu Hneq).
  lra.
Qed.

Theorem affine_ricci_diag_outer :
  forall s v mu,
    has_nonuniform_isotropic_metric s ->
    v = 0%nat \/ v = 2%nat \/ v = 3%nat \/ v = 4%nat ->
    (mu < 4)%nat ->
    affine_metric_symmetric_curved_ricci s boundary_4simplex mu mu v = (-45/32)%R.
Proof.
  intros s v mu Hiso Hv Hmu.
  unfold affine_metric_symmetric_curved_ricci.
  assert (Hstep : sum_4 (fun rho =>
      affine_metric_symmetric_curved_riemann s boundary_4simplex rho mu rho mu v) =
    sum_4 (fun rho =>
      (gamma_iso (3/32) rho mu mu - gamma_iso (3/32) rho rho mu +
       sum_4 (fun lam => gamma_iso (3/8) rho rho lam * gamma_iso (3/8) lam mu mu) -
       sum_4 (fun lam => gamma_iso (3/8) rho mu lam * gamma_iso (3/8) lam rho mu))%R)).
  { apply sum_4_congr; intros rho Hrho.
    apply (affine_riemann_outer s v rho mu rho mu Hiso Hv Hrho Hmu Hrho Hmu). }
  rewrite Hstep.
  replace (3/32)%R with (1 * (15/32 - 3/8))%R by lra.
  rewrite (boundary_shell_gamma_ricci_diag_scaled_formula (3/8) (15/32) 1 mu Hmu).
  lra.
Qed.

Theorem affine_ricci_scalar_outer :
  forall s v,
    has_nonuniform_isotropic_metric s ->
    v = 0%nat \/ v = 2%nat \/ v = 3%nat \/ v = 4%nat ->
    affine_metric_symmetric_curved_ricci_scalar s boundary_4simplex v = (-45/8)%R.
Proof.
  intros s v Hiso Hv.
  destruct Hiso as [H1 [H0 [H2 [H3 H4]]]].
  set (Hiso' := conj H1 (conj H0 (conj H2 (conj H3 H4)))).
  (* Establish the inverse metric for the outer vertex (Euclidean: g^{mu,nu} = delta^{mu,nu}) *)
  assert (Hginv : forall i j, (i < 4)%nat -> (j < 4)%nat ->
    inverse_metric_at_vertex s v i j = if (i =? j)%nat then 1%R else 0%R).
  { intros i j Hi Hj.
    assert (Hiso1 := @inverse_metric_isotropic s v 1%R ltac:(lra)).
    assert (Htmp : inverse_metric_at_vertex s v i j = if (i =? j)%nat then /1%R else 0%R).
    { destruct Hv as [|[|[|]]]; subst;
      [exact (Hiso1 H0 i j Hi Hj) | exact (Hiso1 H2 i j Hi Hj)
      |exact (Hiso1 H3 i j Hi Hj) | exact (Hiso1 H4 i j Hi Hj)]. }
    rewrite Htmp. destruct (i =? j)%nat;
    [rewrite Rinv_1; lra | lra]. }
  (* Convert Ricci scalar to a concrete sum using sum_4_congr at both levels *)
  assert (Hscalar : affine_metric_symmetric_curved_ricci_scalar s boundary_4simplex v =
    sum_4 (fun mu => sum_4 (fun nu =>
      (if (mu =? nu)%nat then 1%R else 0%R) *
      (if (mu =? nu)%nat then (-45/32)%R else (3/32)%R)))).
  { unfold affine_metric_symmetric_curved_ricci_scalar.
    apply sum_4_congr; intros mu Hmu.
    apply sum_4_congr; intros nu Hnu.
    rewrite (Hginv mu nu Hmu Hnu).
    destruct (mu =? nu)%nat eqn:Heqb.
    - apply Nat.eqb_eq in Heqb. subst nu.
      rewrite (affine_ricci_diag_outer s v mu Hiso' Hv Hmu). ring.
    - apply Nat.eqb_neq in Heqb.
      rewrite (affine_ricci_offdiag_outer s v mu nu Hiso' Hv Hmu Hnu Heqb). ring. }
  rewrite Hscalar.
  unfold sum_4, sum_n. cbn. simpl Nat.eqb. lra.
Qed.

Theorem affine_einstein_outer :
  forall s v mu nu,
    has_nonuniform_isotropic_metric s ->
    v = 0%nat \/ v = 2%nat \/ v = 3%nat \/ v = 4%nat ->
    (mu < 4)%nat -> (nu < 4)%nat ->
    affine_metric_symmetric_curved_einstein s boundary_4simplex mu nu v =
      (if (mu =? nu)%nat then (45/32)%R else (3/32)%R).
Proof.
  intros s v mu nu Hiso Hv Hmu Hnu.
  destruct Hiso as [H1 [H0 [H2 [H3 H4]]]].
  set (Hiso' := conj H1 (conj H0 (conj H2 (conj H3 H4)))).
  unfold affine_metric_symmetric_curved_einstein.
  rewrite (affine_ricci_scalar_outer s v Hiso' Hv).
  destruct (Nat.eq_dec mu nu) as [Heq | Hneq].
  - subst nu. rewrite Nat.eqb_refl.
    rewrite (affine_ricci_diag_outer s v mu Hiso' Hv Hmu).
    destruct Hv as [|[|[|]]]; subst;
    [rewrite H0 by lia | rewrite H2 by lia | rewrite H3 by lia | rewrite H4 by lia];
    rewrite Nat.eqb_refl; lra.
  - assert (Hne : mu <> nu) by exact Hneq.
    apply Nat.eqb_neq in Hneq. rewrite Hneq.
    rewrite (affine_ricci_offdiag_outer s v mu nu Hiso' Hv Hmu Hnu Hne).
    destruct Hv as [|[|[|]]]; subst;
    [rewrite H0 by lia | rewrite H2 by lia | rewrite H3 by lia | rewrite H4 by lia];
    rewrite Hneq; lra.
Qed.

(** Negative result: the diagonal EFE G = 3*mass_stress_energy fails at
    outer vertices because G has off-diagonal components (3/32 ≠ 0) while
    mass_stress_energy is diagonal (zero off-diagonal). *)

Theorem affine_efe_fails_outer_offdiag :
  forall s v mu nu,
    has_nonuniform_isotropic_metric s ->
    v = 0%nat \/ v = 2%nat \/ v = 3%nat \/ v = 4%nat ->
    (mu < 4)%nat -> (nu < 4)%nat -> mu <> nu ->
    affine_metric_symmetric_curved_einstein s boundary_4simplex mu nu v <>
      (3 * mass_stress_energy s mu nu v)%R.
Proof.
  intros s v mu nu Hiso Hv Hmu Hnu Hneq Heq.
  rewrite (affine_einstein_outer s v mu nu Hiso Hv Hmu Hnu) in Heq.
  apply Nat.eqb_neq in Hneq. rewrite Hneq in Heq.
  (* 3/32 = 3 * mass_stress_energy: need mass_stress_energy = 0 for mu≠nu.
     mass_stress_energy is 0 off-diagonal — prove by case-splitting to concrete values. *)
  (* mass_stress_energy is 0 for mu≠nu (diagonal stress-energy).
     After concrete case splits and Nat.mod_small, the off-diagonal branch gives 0 definitionally. *)
  assert (HT : (3 * mass_stress_energy s mu nu v)%R = 0%R).
  { unfold mass_stress_energy.
    rewrite !Nat.mod_small by lia.
    destruct mu as [|[|[|[|]]]]; try lia;
    destruct nu as [|[|[|[|]]]]; try lia;
    try (exfalso; vm_compute in Hneq; discriminate Hneq);
    simpl; ring. }
  lra.
Qed.
