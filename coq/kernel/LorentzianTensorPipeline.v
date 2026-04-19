(** LorentzianTensorPipeline: discharging positive Lorentzian coupling.

    DiscreteRaychaudhuri.v leaves one interface hypothesis explicit: the
    effective Lorentzian coupling has to be positive. This file proves that
    positivity in the isotropic two-vertex case when mass decreases along the
    edge from v to w.

    The sign chain is the whole story. The mass gradient makes the isotropic c
    parameter negative, that makes R_00 negative, that flips G_00 positive in
    the way the earlier files need, and once the denominator is positive the
    coupling kappa comes out positive too. So this file is the concrete closure
    of that gap, but only for this specific mass-gradient setup. *)

(* INQUISITOR NOTE: proof-connectivity - closes lorentzian_coupling_positive
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

(**

    The hand calculation here is simple but important: in this isotropic setup,
    R_00 reduces to 6c(1-c). So once c < 0, the Ricci sign is fixed. That one
    sign computation is what the later coupling argument rides on.
*)

(** [curved_ricci_00_negative_when_mass_decreases]: The (0,0) Ricci component
    is negative when the structural mass decreases from v to w.

    Proof copies the HRiem construction from ricci_isotropy_isotropic_2v,
    then unfolds the 4-term Ricci sum for d=0 and closes with nlinarith. *)
(* INQUISITOR NOTE: Key sign lemma - R_{00} < 0 when mass gradient c < 0 *)
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


(** [lorentzian_coupling_positive_from_mass_gradient]: The main result.

    When vertex v has strictly more structural mass than vertex w,
    the gravitational coupling κ = G_{00}/mass is positive.

    This partially discharges the generic Raychaudhuri interface obligation
    from DiscreteRaychaudhuri.v: the hypothesis
    [lorentzian_coupling_positive] is a theorem under the isotropic
    mass-gradient condition.

    PROOF:
    1. einstein_equation_from_mass gives ∃κ, ∀d, G_{dd} = κ·T_{dd}
       with κ = G_{00}/a.
    2. einstein_00_positive_when_mass_decreases gives G_{00} > 0.
    3. a > 0 from mass hypothesis.
    4. Therefore κ = G_{00}/a > 0. *)
(* INQUISITOR NOTE: Main theorem closes the lorentzian_coupling_positive gap
  for the isotropic mass-gradient case under the stated hypothesis
  mass_v > mass_w. *)
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

(**

    With lorentzian_coupling_positive proven for the mass-gradient case,
    the hypothesis used by DiscreteRaychaudhuri.v can be discharged in that
    setting rather than assumed externally.

    We provide a convenience wrapper here. *)

(** [positive_mass_implies_focusing_from_gradient]: Convenience re-export.
    Positive mass with gradient along edge → null congruence focuses. *)
(* INQUISITOR NOTE: Convenience wrapper - gradient -> focusing, using
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
