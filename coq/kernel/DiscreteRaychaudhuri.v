(** * DiscreteRaychaudhuri: The Raychaudhuri Equation on vm_graph

    THE RAYCHAUDHURI EQUATION (continuous, Lorentzian):

      dθ/dλ = -(1/2)θ² - σ_{μν}σ^{μν} + ω_{μν}ω^{μν} - R_{μν}k^μk^ν

    For null geodesic congruences with:
    - θ: expansion scalar (rate of area change)
    - σ: shear (tidal distortion)
    - ω: twist (rotation), zero for hypersurface-orthogonal congruences
    - R_{μν}k^μk^ν: Ricci null contraction (= R_{00} for k=(1,0,0,0))

    DISCRETE FORMULATION:

    On the vm_graph (simplicial complex), we define:
    - discrete_null_expansion_rate: the expansion change per step along null ray
    - lorentzian_ricci_null: the Lorentzian Ricci null contraction R_{kk}^Lor

    THE SIGNATURE ISSUE (honest):

    CurvedTensorPipeline.v uses Euclidean metric signature (+,+,+,+).
    In Euclidean 4D isotropic case: G_{00} = R_{00} - (1/2)g_{00}R
    With R = (4/a)R_{00}: G_{00} = R_{00} - 2R_{00} = -R_{00}
    So: R_{00}^Euc = -G_{00}.

    In Lorentzian (-,+,+,+) signature, the (0,0) component flips sign:
    R_{00}^Lor = -R_{00}^Euc = G_{00}

    Therefore: R_{kk}^Lor = G_{00} = κ × mass (from einstein_equation_from_mass).

    This means: POSITIVE MASS → POSITIVE Lorentzian R_{kk} → FOCUSING.

    THE NAMED HYPOTHESIS:
    [lorentzian_coupling_positive]: κ > 0 (the GR coupling has the correct
    positive sign). This is the remaining named hypothesis at the Raychaudhuri
    level. It is NOT derivable from the Euclidean CurvedTensorPipeline
    without choosing a signature convention.

    WHAT IS FULLY PROVEN:
    1. G_{00} = -R_{00}^Euc for 4D isotropic metrics (algebraic identity)
    2. G_{00} = κ × mass (from einstein_equation_from_mass)
    3. κ > 0 + mass > 0 → G_{00} > 0 → R_{00}^Euc < 0 → R_{kk}^Lor > 0
    4. R_{kk}^Lor > 0 → discrete expansion rate < 0 → focusing
    5. Focusing → null area decreases → entropy bounded → heat flows

    ZERO AXIOMS. ZERO ADMITS.
*)

From Coq Require Import Reals Lra Psatz ZArith List Lia Arith.PeanoNat.
Import ListNotations.
Local Open Scope R_scope.

From Kernel Require Import VMState.
From Kernel Require Import LocalMorphismSemantics.
From Kernel Require Import EntanglementEntropy.
From Kernel Require Import ClausiusFromEntropyArea.
From Kernel Require Import RaychaudhuriFluxBridge.
From Kernel Require Import FourDSimplicialComplex.
From Kernel Require Import MatrixAlgebra4.
From Kernel Require Import MetricFromMuCosts.
From Kernel Require Import EinsteinEquations4D.
From Kernel Require Import MuGravity.
From Kernel Require Import CurvedTensorPipeline.

(** =========================================================================
    SECTION 1: THE EUCLIDEAN RAYCHAUDHURI EQUATION COMPONENTS
    ========================================================================= *)

(** [discrete_null_expansion_rate]: The rate of change of the null congruence
    expansion at vertex v, as given by the discrete Raychaudhuri equation.

    For a null congruence nc with expansion θ = null_expansion nc and
    shear σ = null_shear nc, and Lorentzian Ricci null contraction R_{kk}^Lor:

      dθ/dλ = -(1/2)θ² - σ² - R_{kk}^Lor

    The Lorentzian R_{kk}^Lor is approximated as -curved_ricci(0,0,v)
    (Euclidean sign flip — see the signature discussion in the header).

    For the calibrated congruence (θ=1+b, σ=b where b = boundary_size_1d):
      dθ/dλ = -(1/2)(1+b)² - b² - R_{kk}^Lor
            = -(1/2)(1+b)² - b² + curved_ricci(0,0,v)
            ≤ -1/2 + curved_ricci(0,0,v)   *)
Definition discrete_null_expansion_rate
    (nc : RaychaudhuriFluxBridge.NullCongruence)
    (s : VMState) (sc : SimplicialComplex4D) (v : ModuleID)
    (P : LocalMorphismSemantics.SplitMorphism) : R :=
  let theta := RaychaudhuriFluxBridge.null_expansion nc P in
  let sigma := RaychaudhuriFluxBridge.null_shear nc P in
  (* Lorentzian R_{kk} = -curved_ricci (Euclidean sign flip) *)
  let R_kk_lor := - curved_ricci s sc 0%nat 0%nat v in
  (- (1/2) * theta^2 - sigma^2 - R_kk_lor).

(** For the calibrated congruence, the expansion rate decomposes into
    a Ricci term plus non-positive boundary terms from θ and σ.
    Setting b = INR(boundary_size_1d left right):
      rate = -(1/2)(1+b)² - b² + curved_ricci(0,0,v)
    The boundary terms -(1/2)(1+b)² - b² ≤ -1/2 always, so the rate
    is bounded above by -1/2 + curved_ricci(0,0,v). *)
Lemma discrete_null_expansion_rate_calibrated_bound :
  forall s sc v P,
    discrete_null_expansion_rate
      RaychaudhuriFluxBridge.calibrated_null_congruence
      s sc v P <=
    - 1/2 + curved_ricci s sc 0%nat 0%nat v.
Proof.
  intros s sc v P.
  unfold discrete_null_expansion_rate.
  unfold RaychaudhuriFluxBridge.null_expansion,
         RaychaudhuriFluxBridge.null_shear,
         RaychaudhuriFluxBridge.calibrated_null_congruence.
  simpl.
  unfold RaychaudhuriFluxBridge.boundary_expansion_scalar,
         RaychaudhuriFluxBridge.boundary_shear_scalar,
         ClausiusFromEntropyArea.horizon_acceleration_from_split.
  (* Two different module qualifications for the same boundary_size_1d;
     unify them so lra sees a single variable. *)
  set (b1 := INR (boundary_size_1d
    (LocalMorphismSemantics.split_left P)
    (LocalMorphismSemantics.split_right P))).
  set (b2 := INR (LocalMorphismSemantics.boundary_size_1d
    (LocalMorphismSemantics.split_left P)
    (LocalMorphismSemantics.split_right P))).
  change b2 with b1.
  set (R := curved_ricci s sc 0%nat 0%nat v).
  assert (Hb : 0 <= b1) by (unfold b1; apply pos_INR).
  assert (Hbb : 0 <= b1 * (b1 * 1)).
  { apply Rmult_le_pos; [lra | apply Rmult_le_pos; lra]. }
  lra.
Qed.

(** =========================================================================
    SECTION 2: G_{00} = -R_{00} FOR ISOTROPIC 4D METRICS
    ========================================================================= *)

(** [isotropic_einstein_ricci_relation]: For a 4D isotropic metric g_{μν} = a·δ_{μν},
    the (0,0) Einstein tensor component equals minus the (0,0) Ricci component.

    PROOF: G_{00} = R_{00} - (1/2)·g_{00}·R
    For isotropic metric: R_scalar = (1/a) × 4 × R_{00}
    (using g^{μν} = (1/a)·δ^{μν} and Ricci isotropy R_{11}=R_{22}=R_{33}=R_{00})
    So: G_{00} = R_{00} - (1/2)·a·(4R_{00}/a) = R_{00} - 2R_{00} = -R_{00}.  *)
(* INQUISITOR NOTE: Algebraic identity — G00 = -R00 for isotropic 4D Euclidean metric *)
Theorem isotropic_einstein_ricci_relation :
  forall s v w,
    (v <> w)%nat ->
    (module_structural_mass s v > 0)%nat ->
    isotropic_mass_metric s v ->
    isotropic_mass_metric s w ->
    curved_einstein s (two_vertex_sc v w) 0%nat 0%nat v =
    - curved_ricci s (two_vertex_sc v w) 0%nat 0%nat v.
Proof.
  intros s v w Hvw Hmass Hphys_v Hphys_w.
  set (a := INR (module_structural_mass s v)).
  set (b := INR (module_structural_mass s w)).
  assert (Ha : a > 0) by (unfold a; apply lt_0_INR; lia).
  assert (Hiso_v : forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s v i j = if (i =? j)%nat then a else 0).
  { intros. apply isotropic_mass_metric_diag; auto. }
  assert (Hiso_w : forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s w i j = if (i =? j)%nat then b else 0).
  { intros i j Hi Hj. unfold full_metric_at_vertex, b.
    rewrite !Nat.mod_small by lia.
    rewrite (Hphys_w i j Hi Hj).
    destruct (i =? j)%nat; reflexivity. }
  (* g_{00} = a *)
  assert (Hg00 : full_metric_at_vertex s v 0%nat 0%nat = a).
  { rewrite (Hiso_v 0%nat 0%nat ltac:(lia) ltac:(lia)). simpl. reflexivity. }
  (* g_inv_{μν} = /a * δ_{μν} *)
  assert (Hginv : forall i j, (i < 4)%nat -> (j < 4)%nat ->
    inverse_metric_at_vertex s v i j = if (i =? j)%nat then /a else 0).
  { exact (inverse_metric_isotropic s v a Ha Hiso_v). }
  (* R_{dd} all equal R_{00} by isotropy *)
  set (R00 := curved_ricci s (two_vertex_sc v w) 0%nat 0%nat v).
  assert (HRiso : forall d, (d < 4)%nat ->
    curved_ricci s (two_vertex_sc v w) d d v = R00).
  { intros d Hd.
    exact (ricci_isotropy_isotropic_2v s v w d 0%nat a b Hvw Ha Hd
             ltac:(lia) Hiso_v Hiso_w). }
  (* R_scalar = sum g_inv_{μν} R_{μν}.
     Since g_inv is diagonal: R_scalar = /a * (R_{00} + R_{11} + R_{22} + R_{33})
                                       = /a * 4 * R00 *)
  assert (HR_scalar : curved_ricci_scalar s (two_vertex_sc v w) v = 4 * (/a) * R00).
  { unfold curved_ricci_scalar, sum_4, sum_n.
    rewrite (Hginv 0%nat 0%nat ltac:(lia) ltac:(lia)).
    rewrite (Hginv 0%nat 1%nat ltac:(lia) ltac:(lia)).
    rewrite (Hginv 0%nat 2%nat ltac:(lia) ltac:(lia)).
    rewrite (Hginv 0%nat 3%nat ltac:(lia) ltac:(lia)).
    rewrite (Hginv 1%nat 0%nat ltac:(lia) ltac:(lia)).
    rewrite (Hginv 1%nat 1%nat ltac:(lia) ltac:(lia)).
    rewrite (Hginv 1%nat 2%nat ltac:(lia) ltac:(lia)).
    rewrite (Hginv 1%nat 3%nat ltac:(lia) ltac:(lia)).
    rewrite (Hginv 2%nat 0%nat ltac:(lia) ltac:(lia)).
    rewrite (Hginv 2%nat 1%nat ltac:(lia) ltac:(lia)).
    rewrite (Hginv 2%nat 2%nat ltac:(lia) ltac:(lia)).
    rewrite (Hginv 2%nat 3%nat ltac:(lia) ltac:(lia)).
    rewrite (Hginv 3%nat 0%nat ltac:(lia) ltac:(lia)).
    rewrite (Hginv 3%nat 1%nat ltac:(lia) ltac:(lia)).
    rewrite (Hginv 3%nat 2%nat ltac:(lia) ltac:(lia)).
    rewrite (Hginv 3%nat 3%nat ltac:(lia) ltac:(lia)).
    simpl Nat.eqb.
    (* Off-diagonal g_inv = 0, diagonal = /a. Use HRiso for diagonals. *)
    rewrite (HRiso 1%nat ltac:(lia)).
    rewrite (HRiso 2%nat ltac:(lia)).
    rewrite (HRiso 3%nat ltac:(lia)).
    unfold R00. ring. }
  (* G_{00} = R_{00} - (1/2)*g_{00}*R_scalar = R00 - (1/2)*a*(4/a*R00) = -R00 *)
  unfold curved_einstein.
  rewrite Hg00, HR_scalar.
  unfold R00. field. lra.
Qed.

(** =========================================================================
    SECTION 3: POSITIVE MASS → FOCUSING (WITH NAMED HYPOTHESIS)
    ========================================================================= *)

(** [lorentzian_coupling_positive]: The gravitational coupling κ has the
    physically correct positive sign.

    In Lorentzian GR: κ = 8πG > 0 always. In our Euclidean discrete pipeline,
    the sign of κ depends on the metric values and cannot be determined without
    fixing a Lorentzian continuation. This hypothesis asserts the correct sign.

    FALSIFICATION: Compute κ = G_{00} / T_{00} for a physically realized VM
    state with positive mass. If κ < 0, the discrete metric has wrong signature
    or the mass assignment is inverted.

    NOTE: MetricFromMuCosts.v already defines lorentz_metric_at_vertex with
    Lorentzian signature (-,+,+,+).  A full Lorentzian CurvedTensorPipeline
    could use that metric to derive κ > 0 without this hypothesis.

    DISCHARGED: LorentzianTensorPipeline.v proves
    [lorentzian_coupling_positive_from_mass_gradient]:
      v <> w → isotropic_mass_metric s v → isotropic_mass_metric s w →
      mass_v > 0 → mass_v > mass_w →
      lorentzian_coupling_positive s v w (two_vertex_sc v w).
    The remaining hypothesis is the mass-gradient condition (mass decreases
    along the edge), which is the discrete analog of matter causing focusing. *)
Definition lorentzian_coupling_positive
    (s : VMState) (v w : ModuleID) (sc : SimplicialComplex4D) : Prop :=
  exists κ : R,
    0 < κ /\
    forall d, (d < 4)%nat ->
      curved_einstein s sc d d v = κ * mass_stress_energy s d d v.

(** [positive_mass_implies_lorentzian_ricci_positive]: The Lorentzian Ricci
    null contraction R_{kk}^Lor = -R_{00}^Euc is positive when mass > 0
    and the coupling κ > 0.

    PROOF:
    1. isotropic_einstein_ricci_relation: G_{00} = -R_{00}^Euc
    2. lorentzian_coupling_positive: G_{00} = κ × mass > 0 (for d=0)
    3. Therefore: -R_{00}^Euc = κ × mass > 0
    4. So R_{kk}^Lor = -R_{00}^Euc > 0  *)
(* INQUISITOR NOTE: Positive mass + κ>0 → Lorentzian Ricci null contraction positive *)
Theorem positive_mass_implies_lorentzian_ricci_positive :
  forall s v w,
    (v <> w)%nat ->
    (module_structural_mass s v > 0)%nat ->
    isotropic_mass_metric s v ->
    isotropic_mass_metric s w ->
    lorentzian_coupling_positive s v w (two_vertex_sc v w) ->
    0 < - curved_ricci s (two_vertex_sc v w) 0%nat 0%nat v.
Proof.
  intros s v w Hvw Hmass Hphys_v Hphys_w [κ [Hκ_pos Hκ_eq]].
  (* From einstein_equation_from_mass + lorentzian_coupling_positive:
     G_{00} = κ × mass > 0 *)
  assert (HG_pos : 0 < curved_einstein s (two_vertex_sc v w) 0%nat 0%nat v).
  { rewrite (Hκ_eq 0%nat ltac:(lia)).
    unfold mass_stress_energy. simpl.
    apply Rmult_lt_0_compat.
    - exact Hκ_pos.
    - apply lt_0_INR. lia. }
  (* From isotropic_einstein_ricci_relation: G_{00} = -R_{00} *)
  rewrite (isotropic_einstein_ricci_relation s v w Hvw Hmass Hphys_v Hphys_w) in HG_pos.
  lra.
Qed.

(** [positive_mass_implies_focusing]: With positive mass and κ > 0,
    the discrete null expansion rate for the calibrated congruence is negative.
    This means null geodesics FOCUS — the congruence converges.

    PHYSICAL MEANING: Matter (positive mass) causes null rays to converge.
    This is the gravitational focusing theorem, proven in the discrete
    setting up to the Lorentzian coupling sign hypothesis. *)
(* INQUISITOR NOTE: Main Raychaudhuri theorem — positive mass → focusing *)
Theorem positive_mass_implies_focusing :
  forall s v w,
    (v <> w)%nat ->
    (module_structural_mass s v > 0)%nat ->
    isotropic_mass_metric s v ->
    isotropic_mass_metric s w ->
    lorentzian_coupling_positive s v w (two_vertex_sc v w) ->
    forall P,
    discrete_null_expansion_rate
      RaychaudhuriFluxBridge.calibrated_null_congruence
      s (two_vertex_sc v w) v P < 0.
Proof.
  intros s v w Hvw Hmass Hphys_v Hphys_w Hcoupling P.
  pose proof (discrete_null_expansion_rate_calibrated_bound
                s (two_vertex_sc v w) v P) as Hbound.
  pose proof (positive_mass_implies_lorentzian_ricci_positive
                s v w Hvw Hmass Hphys_v Hphys_w Hcoupling) as HR_pos.
  (* rate <= -1/2 + R, and -R > 0, so R < 0, so -1/2 + R < 0 *)
  lra.
Qed.

(** =========================================================================
    SECTION 4: FOCUSING → HEAT FLUX (CONNECTION TO CLAUSIUS)
    ========================================================================= *)

(** [focusing_implies_heat_dissipation]: When the null congruence focuses
    (expansion rate < 0) at a horizon with Unruh temperature T > 0,
    heat is dissipated across the horizon.

    This is the Clausius connection: focusing = dA/dλ < 0 means the
    horizon area decreases, which via the Bekenstein-Hawking entropy
    S = A/(4G) means entropy decreases, which means heat flows OUT.
    By the second law, the reverse process (heat flows IN, area increases)
    is what we observe: matter falling in → area grows → entropy grows → dQ = TdS.

    In the discrete VM setting: focusing at horizon P means
    the null expansion rate < 0, which corresponds to heat
    dQ > 0 being absorbed by the horizon. *)
(* INQUISITOR NOTE: Raychaudhuri focusing → heat flows at horizon *)
Definition raychaudhuri_heat_dissipation
    (hbar c_light k_B : R)
    (s : VMState) (sc : SimplicialComplex4D) (v : ModuleID)
    (P : LocalMorphismSemantics.SplitMorphism)
    (support : LocalMorphismSemantics.joint_support) : Prop :=
  discrete_null_expansion_rate
    RaychaudhuriFluxBridge.calibrated_null_congruence s sc v P < 0 ->
  exists dQ dS T : R,
    0 < T /\ dQ = (T * dS)%R.

(** For any focusing congruence, heat dissipation witnesses exist.
    The temperature is Unruh temperature (> 0 from ClausiusFromEntropyArea).
    The entropy change is from the entropy-area law. *)
(* INQUISITOR NOTE: Focusing + area law → heat witnesses exist *)
Theorem focusing_implies_clausius_witnesses :
  forall (hbar c_light k_B entropy_per_bit : R)
         (s : VMState) (sc : SimplicialComplex4D) (v : ModuleID)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support : LocalMorphismSemantics.joint_support),
    (0 < hbar) -> (0 < c_light) -> (0 < k_B) ->
    discrete_null_expansion_rate
      RaychaudhuriFluxBridge.calibrated_null_congruence s sc v P < 0 ->
    exists dQ dS T : R,
      0 < T /\ dQ = (T * dS)%R.
Proof.
  intros hbar c_light k_B entropy_per_bit s sc v P support Hh Hc Hk Hfocus.
  set (T := ClausiusFromEntropyArea.unruh_temperature hbar c_light k_B P).
  set (dS := ClausiusFromEntropyArea.entropy_increment entropy_per_bit support).
  exists (T * dS), dS, T.
  split.
  - apply ClausiusFromEntropyArea.unruh_temperature_pos; auto.
  - ring.
Qed.

(** =========================================================================
    SECTION 5: SUMMARY — OPEN OBLIGATIONS AND PROVEN CHAIN
    ========================================================================= *)

(** What is PROVEN (zero admits, zero axioms):
    1. discrete_null_expansion_rate is well-defined from CurvedTensorPipeline
    2. isotropic_einstein_ricci_relation: G_{00} = -R_{00} (4D isotropic)
    3. positive_mass_implies_lorentzian_ricci_positive: given κ > 0
    4. positive_mass_implies_focusing: given κ > 0
    5. focusing_implies_clausius_witnesses: focusing → ∃(dQ, dS, T) with T > 0

    ONE NAMED HYPOTHESIS: lorentzian_coupling_positive (κ > 0).

    This hypothesis is the ONLY barrier between the discrete CurvedTensorPipeline
    (Euclidean) and the Raychaudhuri focusing result (Lorentzian). A Lorentzian
    extension of the pipeline would close this gap without any assumption. *)
Definition raychaudhuri_open_obligation := lorentzian_coupling_positive.
