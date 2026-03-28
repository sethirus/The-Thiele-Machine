(** * LorentzianTensorPipeline: Proving lorentzian_coupling_positive (κ > 0)

    =========================================================================
    WHAT THIS FILE PROVES:

    [lorentzian_coupling_positive_from_mass_gradient] — the main result.

    For the isotropic 2-vertex complex, when vertex v has MORE structural mass
    than vertex w (mass decreases along the edge v→w), the Einstein coupling
    constant κ = G_{00}/mass is POSITIVE:

        module_structural_mass s v > module_structural_mass s w
          →  lorentzian_coupling_positive s v w (two_vertex_sc v w)

    PROOF CHAIN:
    1. Isotropic Christoffel formula: Γ^ρ_{μν}(v) = c·(δ_{νρ}+δ_{μρ}-δ_{μν})
       where c = (b-a)/(2a), a = INR(mass v), b = INR(mass w).
    2. Explicit Riemann via HRiem (same pattern as ricci_isotropy_isotropic_2v).
    3. Compute R_{00} = 6c - 6c² = 6c(1-c).
    4. When c < 0 (b < a, mass decreases): c < 0, 1-c > 1 > 0, so R_{00} < 0.
    5. From isotropic_einstein_ricci_relation: G_{00} = -R_{00} > 0.
    6. κ = G_{00}/a > 0 since a > 0.
    7. By ricci_isotropy_isotropic_2v, G_{dd} = G_{00} for all d, so
       G_{dd} = κ * T_{dd} for all d.

    THE LORENTZIAN CONNECTION:
    In the Euclidean (+,+,+,+) pipeline, G_{00}^Euc = -R_{00}^Euc.
    In Lorentzian (-,+,+,+), the sign of the Ricci scalar trace flips:
    G_{00}^Lor = +R_{00}^Lor (shown in DiscreteRaychaudhuri.v).
    Both analyses give G_{00} > 0 when mass decreases — the Euclidean κ is
    positive precisely because the Lorentzian interpretation is consistent.

    ONE ADDITIONAL HYPOTHESIS:
    module_structural_mass s v > module_structural_mass s w
    This is the mass-gradient condition (mass decreases along the null ray).
    It is falsifiable: a VM state with equal or increasing mass along the edge
    would make κ ≤ 0.

    ZERO AXIOMS. ZERO ADMITS.
    =========================================================================
*)

(* INQUISITOR NOTE: proof-connectivity — closes lorentzian_coupling_positive
   gap from DiscreteRaychaudhuri.v using the mass-gradient sign argument.
   Chain: mass_v > mass_w → c < 0 → R_{00} < 0 → G_{00} > 0 → κ > 0. *)

From Coq Require Import Reals Lra Psatz ZArith List Lia Arith.PeanoNat.
Import ListNotations.
Local Open Scope R_scope.

From Kernel Require Import VMState.
From Kernel Require Import MuCostModel.
From Kernel Require Import FourDSimplicialComplex.
From Kernel Require Import MatrixAlgebra4.
From Kernel Require Import MetricFromMuCosts.
From Kernel Require Import RiemannTensor4D.
From Kernel Require Import EinsteinEquations4D.
From Kernel Require Import MuGravity.
From Kernel Require Import CurvedTensorPipeline.
From Kernel Require Import DiscreteRaychaudhuri.

(** =========================================================================
    SECTION 1: THE KEY LEMMA — R_{00} < 0 WHEN MASS DECREASES
    =========================================================================

    Manual calculation (verified by ring):

      R_{00} = Σ_{ρ=0}^{3} R^ρ_{0ρ0}(v)

    Using HRiem (same pattern as ricci_isotropy_isotropic_2v), each term:
      ρ=0: linear=0, quad = (-2c²) - (-2c²) = 0
      ρ=1: linear=2c, quad = (-2c²) - 0 = -2c²  →  2c - 2c²
      ρ=2: same as ρ=1  →  2c - 2c²
      ρ=3: same as ρ=1  →  2c - 2c²

    Total: R_{00} = 6c - 6c²  =  6c(1-c)

    When c < 0 (b < a):  c < 0  and  1-c > 1 > 0  →  R_{00} < 0.
*)

(** [curved_ricci_00_negative_when_mass_decreases]: The (0,0) Ricci component
    is negative when the structural mass decreases from v to w.

    Proof copies the HRiem construction from ricci_isotropy_isotropic_2v,
    then unfolds the 4-term Ricci sum for d=0 and closes with nlinarith. *)
(* INQUISITOR NOTE: Key sign lemma — R_{00} < 0 when mass gradient c < 0 *)
Lemma curved_ricci_00_negative_when_mass_decreases :
  forall s v w a b,
    (v <> w)%nat ->
    (a > 0) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s v i j = if (i =? j)%nat then a else 0) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s w i j = if (i =? j)%nat then b else 0) ->
    (b < a) ->
    curved_ricci s (two_vertex_sc v w) 0%nat 0%nat v < 0.
Proof.
  intros s v w a b Hvw Ha Hiso_v Hiso_w Hba.
  set (c := (b - a) / (2 * a)).
  (* c < 0 since b - a < 0 and 2*a > 0 *)
  assert (Hc_neg : c < 0).
  { unfold c, Rdiv.
    assert (H1 : b - a < 0) by lra.
    assert (H2 : 0 < / (2 * a)) by (apply Rinv_0_lt_compat; lra).
    nra. }
  (* Christoffel closed form: Γ^ρ_{μν}(v) = c*(δ_{νρ}+δ_{μρ}-δ_{μν}) *)
  assert (HGamma : forall ρ μ ν, (ρ < 4)%nat -> (μ < 4)%nat -> (ν < 4)%nat ->
    curved_christoffel s (two_vertex_sc v w) ρ μ ν v =
    c * (delta ν ρ + delta μ ρ - delta μ ν)).
  { intros ρ μ ν Hρ Hμ Hν.
    rewrite (curved_christoffel_isotropic_2v s v w a b ρ μ ν Hvw Ha Hiso_v Hiso_w Hρ Hμ Hν).
    unfold c, delta. reflexivity. }
  (* Christoffel at w is zero *)
  assert (HGamma_w : forall ρ μ ν,
    curved_christoffel s (two_vertex_sc v w) ρ μ ν w = 0).
  { intros. apply curved_christoffel_at_w_zero; auto. }
  (* Riemann formula at v: discrete derivative uses dd_at_v *)
  assert (HRiem : forall ρ σ μ ν,
    (ρ < 4)%nat -> (σ < 4)%nat -> (μ < 4)%nat -> (ν < 4)%nat ->
    curved_riemann s (two_vertex_sc v w) ρ σ μ ν v =
    (- c * (delta σ ρ + delta ν ρ - delta ν σ)
     + c * (delta σ ρ + delta μ ρ - delta μ σ))
    + sum_4 (fun λ =>
        c * (delta λ ρ + delta μ ρ - delta μ λ) *
        (c * (delta σ λ + delta ν λ - delta ν σ)))
    - sum_4 (fun λ =>
        c * (delta λ ρ + delta ν ρ - delta ν λ) *
        (c * (delta σ λ + delta μ λ - delta μ σ)))).
  { intros ρ σ μ ν Hρ Hσ Hμ Hν.
    unfold curved_riemann.
    rewrite (dd_at_v s v w _ _ Hvw).
    rewrite (dd_at_v s v w _ _ Hvw).
    rewrite HGamma_w, HGamma_w.
    rewrite (HGamma ρ ν σ Hρ Hν Hσ).
    rewrite (HGamma ρ μ σ Hρ Hμ Hσ).
    unfold sum_4, sum_n.
    rewrite (HGamma ρ μ 0%nat Hρ Hμ ltac:(lia)),
            (HGamma 0%nat ν σ ltac:(lia) Hν Hσ),
            (HGamma ρ μ 1%nat Hρ Hμ ltac:(lia)),
            (HGamma 1%nat ν σ ltac:(lia) Hν Hσ),
            (HGamma ρ μ 2%nat Hρ Hμ ltac:(lia)),
            (HGamma 2%nat ν σ ltac:(lia) Hν Hσ),
            (HGamma ρ μ 3%nat Hρ Hμ ltac:(lia)),
            (HGamma 3%nat ν σ ltac:(lia) Hν Hσ).
    rewrite (HGamma ρ ν 0%nat Hρ Hν ltac:(lia)),
            (HGamma 0%nat μ σ ltac:(lia) Hμ Hσ),
            (HGamma ρ ν 1%nat Hρ Hν ltac:(lia)),
            (HGamma 1%nat μ σ ltac:(lia) Hμ Hσ),
            (HGamma ρ ν 2%nat Hρ Hν ltac:(lia)),
            (HGamma 2%nat μ σ ltac:(lia) Hμ Hσ),
            (HGamma ρ ν 3%nat Hρ Hν ltac:(lia)),
            (HGamma 3%nat μ σ ltac:(lia) Hμ Hσ).
    ring. }
  (* Step 1: compute the polynomial value R_{00} = 6c - 6c^2 using ring *)
  assert (Hval : curved_ricci s (two_vertex_sc v w) 0%nat 0%nat v =
                 6 * c - 6 * c ^ 2).
  { unfold curved_ricci, sum_4, sum_n.
    repeat match goal with
    | |- context [curved_riemann ?ss ?sc ?r ?s2 ?m ?n ?vv] =>
      rewrite (HRiem r s2 m n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    end.
    unfold sum_4, sum_n, delta.
    simpl Nat.eqb.
    (* Reduce all remaining if-true/if-false conditionals, then close by ring *)
    cbv iota.
    ring. }
  (* Step 2: prove 6c - 6c^2 < 0 from c < 0 *)
  (* 6c - 6c^2 = 6c(1-c).  c < 0 and 1-c > 0, so product < 0.
     Equivalently: 6c < 0 and c^2 ≥ 0, so 6c - 6c^2 ≤ 6c < 0. *)
  rewrite Hval.
  (* c < 0  →  c^2 > 0  →  6c - 6c^2 = 6c(1-c) < 0  (nra handles this) *)
  nra.
Qed.

(** =========================================================================
    SECTION 2: G_{00} > 0 FROM R_{00} < 0
    ========================================================================= *)

(** [einstein_00_positive_when_mass_decreases]: Under isotropic metric with
    mass decreasing from v to w, the (0,0) Einstein tensor component is positive.

    Proof: apply isotropic_einstein_ricci_relation (G_{00} = -R_{00}), then
    use the sign lemma above. *)
(* INQUISITOR NOTE: G_{00} > 0 from R_{00} < 0 via sign flip relation *)
Lemma einstein_00_positive_when_mass_decreases :
  forall s v w,
    (v <> w)%nat ->
    isotropic_mass_metric s v ->
    isotropic_mass_metric s w ->
    (module_structural_mass s v > 0)%nat ->
    (module_structural_mass s v > module_structural_mass s w)%nat ->
    0 < curved_einstein s (two_vertex_sc v w) 0%nat 0%nat v.
Proof.
  intros s v w Hvw Hphys_v Hphys_w Hmass Hmass_gt.
  set (a := INR (module_structural_mass s v)).
  set (b := INR (module_structural_mass s w)).
  assert (Ha : a > 0).
  { unfold a. apply lt_0_INR. lia. }
  assert (Hba : b < a).
  { unfold a, b. apply lt_INR. lia. }
  (* Establish isotropy *)
  assert (Hiso_v : forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s v i j = if (i =? j)%nat then a else 0).
  { intros. apply isotropic_mass_metric_diag; auto. }
  assert (Hiso_w : forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s w i j = if (i =? j)%nat then b else 0).
  { intros i j Hi Hj.
    unfold full_metric_at_vertex, b. rewrite !Nat.mod_small by lia.
    rewrite (Hphys_w i j Hi Hj).
    destruct (i =? j)%nat; reflexivity. }
  (* G_{00} = -R_{00} by isotropic_einstein_ricci_relation *)
  rewrite (isotropic_einstein_ricci_relation s v w Hvw Hmass Hphys_v Hphys_w).
  (* R_{00} < 0 by sign lemma *)
  pose proof (curved_ricci_00_negative_when_mass_decreases
                s v w a b Hvw Ha Hiso_v Hiso_w Hba) as HR00_neg.
  lra.
Qed.

(** =========================================================================
    SECTION 3: MAIN THEOREM — lorentzian_coupling_positive
    ========================================================================= *)

(** [lorentzian_coupling_positive_from_mass_gradient]: The main result.

    When vertex v has strictly more structural mass than vertex w,
    the gravitational coupling κ = G_{00}/mass is positive.

    This closes the open obligation in DiscreteRaychaudhuri.v:
    the hypothesis [lorentzian_coupling_positive] is now a theorem
    under the mass-gradient condition.

    PROOF:
    1. einstein_equation_from_mass gives ∃κ, ∀d, G_{dd} = κ·T_{dd}
       with κ = G_{00}/a.
    2. einstein_00_positive_when_mass_decreases gives G_{00} > 0.
    3. a > 0 from mass hypothesis.
    4. Therefore κ = G_{00}/a > 0. *)
(* INQUISITOR NOTE: Main theorem — closes lorentzian_coupling_positive gap.
   Zero admits. Hypothesis: mass_v > mass_w (mass gradient along edge). *)
Theorem lorentzian_coupling_positive_from_mass_gradient :
  forall s v w,
    (v <> w)%nat ->
    isotropic_mass_metric s v ->
    isotropic_mass_metric s w ->
    (module_structural_mass s v > 0)%nat ->
    (module_structural_mass s v > module_structural_mass s w)%nat ->
    lorentzian_coupling_positive s v w (two_vertex_sc v w).
Proof.
  intros s v w Hvw Hphys_v Hphys_w Hmass Hmass_gt.
  set (a := INR (module_structural_mass s v)).
  assert (Ha : a > 0).
  { unfold a. apply lt_0_INR. lia. }
  (* Get the Einstein equation: ∃κ, ∀d, G_{dd} = κ·T_{dd} with κ = G_{00}/a *)
  pose proof (einstein_equation_from_mass s v w Hvw Hphys_v Hphys_w Hmass)
    as [κ Hκ_eq].
  (* G_{00} > 0 *)
  pose proof (einstein_00_positive_when_mass_decreases
                s v w Hvw Hphys_v Hphys_w Hmass Hmass_gt) as HG00_pos.
  (* κ = G_{00}/a > 0 *)
  assert (Hκ_pos : 0 < κ).
  { (* From Hκ_eq at d=0: G_{00} = κ * T_{00} = κ * a *)
    assert (HT00 : mass_stress_energy s 0%nat 0%nat v = a).
    { unfold mass_stress_energy, a. simpl. reflexivity. }
    assert (HG_eq : curved_einstein s (two_vertex_sc v w) 0%nat 0%nat v = κ * a).
    { rewrite <- HT00. apply (Hκ_eq 0%nat). lia. }
    (* G_{00} > 0 and G_{00} = κ*a and a > 0 → κ > 0 *)
    rewrite HG_eq in HG00_pos.
    (* HG00_pos : 0 < κ * a, Ha : 0 < a → nra gives 0 < κ *)
    nra. }
  (* Unfold lorentzian_coupling_positive and provide κ *)
  unfold lorentzian_coupling_positive.
  exists κ.
  split.
  - exact Hκ_pos.
  - exact Hκ_eq.
Qed.

(** =========================================================================
    SECTION 4: DOWNSTREAM CONSEQUENCE FOR RAYCHAUDHURI FOCUSING
    =========================================================================

    With lorentzian_coupling_positive now proven (under mass-gradient),
    the theorem positive_mass_implies_lorentzian_ricci_positive in
    DiscreteRaychaudhuri.v no longer needs to take it as a hypothesis —
    it can be derived from mass-gradient instead.

    We provide a convenience wrapper here. *)

(** [positive_mass_implies_focusing_from_gradient]: Convenience re-export.
    Positive mass with gradient along edge → null congruence focuses. *)
(* INQUISITOR NOTE: Convenience wrapper — gradient → focusing, using
   lorentzian_coupling_positive_from_mass_gradient as the κ>0 source *)
Theorem positive_mass_implies_focusing_from_gradient :
  forall s v w,
    (v <> w)%nat ->
    (module_structural_mass s v > 0)%nat ->
    (module_structural_mass s v > module_structural_mass s w)%nat ->
    isotropic_mass_metric s v ->
    isotropic_mass_metric s w ->
    forall P,
    DiscreteRaychaudhuri.discrete_null_expansion_rate
      RaychaudhuriFluxBridge.calibrated_null_congruence
      s (two_vertex_sc v w) v P < 0.
Proof.
  intros s v w Hvw Hmass Hmass_gt Hphys_v Hphys_w P.
  apply (DiscreteRaychaudhuri.positive_mass_implies_focusing s v w Hvw Hmass
           Hphys_v Hphys_w
           (lorentzian_coupling_positive_from_mass_gradient
              s v w Hvw Hphys_v Hphys_w Hmass Hmass_gt)).
Qed.
