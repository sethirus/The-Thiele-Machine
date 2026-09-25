(** DiscreteRaychaudhuri: a finite expansion-rate chain on vm_graph.

    This file defines a finite-model analogue of the sign pattern used in a
    Raychaudhuri-style argument. The theorem statements below operate on the
    selected VM expressions and their explicit premises.

    CurvedTensorPipeline.v uses a Euclidean-signature convention, so the
    selected 00-component has the sign recorded by the algebraic identity
    below. The named coupling predicate supplies the positive proportionality
    premise used to obtain the displayed inequality.

    That is why this file carries the named hypothesis
    lorentzian_coupling_positive. The sign is a premise of this finite bridge,
    not a consequence of the Euclidean definitions alone.

    What gets proved is the stated chain: an isotropic algebraic identity,
    positive coupling times positive structural mass, the selected positive
    Ricci expression, a negative discrete expansion rate, and a weak
    Clausius-shaped witness. No new project-local axioms or admitted proofs
    are introduced by this file. *)

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


(** [discrete_null_expansion_rate]: rate of change for the null congruence
    expansion at vertex v, as given by the discrete Raychaudhuri equation.

    For a null congruence nc with expansion θ = null_expansion nc and
    shear σ = null_shear nc, and Lorentzian Ricci null contraction R_{kk}^Lor:

      dθ/dλ = -(1/2)θ² - σ² - R_{kk}^Lor

    The Lorentzian R_{kk}^Lor is represented as -curved_ricci(0,0,v).
    That is the Euclidean sign flip explained in the header.

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


(** [isotropic_einstein_ricci_relation]: For a 4D isotropic metric g_{μν} = a·δ_{μν},
    the (0,0) Einstein tensor component equals minus the (0,0) Ricci component.

    PROOF: G_{00} = R_{00} - (1/2)·g_{00}·R
    For isotropic metric: R_scalar = (1/a) × 4 × R_{00}
    (using g^{μν} = (1/a)·δ^{μν} and Ricci isotropy R_{11}=R_{22}=R_{33}=R_{00})
    So: G_{00} = R_{00} - (1/2)·a·(4R_{00}/a) = R_{00} - 2R_{00} = -R_{00}.  *)
(* SCOPE NOTE: Algebraic identity: G00 = -R00 for isotropic 4D Euclidean metric. *)
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


(** [lorentzian_coupling_positive]: a positive proportionality witness for the
    selected diagonal expressions.

    The predicate supplies the positive constant and the proportionality
    equation as premises. The Euclidean definitions do not derive that
    positivity on their own. *)
Definition lorentzian_coupling_positive
    (s : VMState) (v w : ModuleID) (sc : SimplicialComplex4D) : Prop :=
  exists κ : R,
    0 < κ /\
    forall d, (d < 4)%nat ->
      curved_einstein s sc d d v = κ * mass_stress_energy s d d v.

(** [positive_mass_implies_lorentzian_ricci_positive]: the selected negated
    00-component is positive under the stated structural-mass and coupling
    premises.

    The proof uses the isotropic identity and the positive proportionality
    witness, then applies real-order arithmetic. *)
(* SCOPE NOTE: Positive mass + κ>0 → Lorentzian Ricci null contraction positive *)
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

(** [positive_mass_implies_focusing]: with positive structural mass and the
    coupling witness, the selected discrete null-expansion expression is
    negative.

    SCOPE: Under the stated discrete mass, metric, and positive-coupling
    hypotheses, the selected null-expansion expression is negative. The
    theorem is an inequality in this finite model; it is not by itself a
    derivation of a gravitational focusing law. *)
(* SCOPE NOTE: Main Raychaudhuri theorem: positive mass → focusing. *)
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


(** [focusing_implies_heat_dissipation]: this is the contract shape for the
    Clausius bridge. If the calibrated congruence focuses, the conclusion must
    provide dQ, dS, and T with T > 0 and dQ = T dS.

    This definition does not derive the numerical heat flow. It pins down the
    witness shape that the theorem below can fill. *)
(* SCOPE NOTE: Raychaudhuri focusing gives the trigger for the Clausius witness. *)
Definition raychaudhuri_heat_dissipation
    (hbar c_light k_B : R)
    (s : VMState) (sc : SimplicialComplex4D) (v : ModuleID)
    (P : LocalMorphismSemantics.SplitMorphism)
    (support : LocalMorphismSemantics.joint_support) : Prop :=
  discrete_null_expansion_rate
    RaychaudhuriFluxBridge.calibrated_null_congruence s sc v P < 0 ->
  exists dQ dS T : R,
    0 < T /\ dQ = (T * dS)%R.

(** Given the selected negative expansion expression, the Clausius-shaped
    witnesses exist.
    The temperature comes from unruh_temperature_pos. The entropy term comes
    from entropy_increment. This is a weak existence bridge: the proof does
    not compute heat from the focusing rate. *)
(* SCOPE NOTE: Focusing + area law provide Clausius-shaped witnesses; no heat magnitude is derived here. *)
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


(** What this file actually delivers.

   First, it fixes the sign bookkeeping between the Euclidean tensor pipeline
   and the Lorentzian focusing story. Second, under the explicit positive-
   coupling hypothesis, it proves the chain from positive mass to positive
   Lorentzian Ricci null term to focusing. Third, it packages focusing into a
   weak Clausius-shaped witness.

   The open interface remains the same: lorentzian_coupling_positive. The
   current specialized discharge lives in LorentzianTensorPipeline.v for the
   isotropic mass-gradient case. What is still missing is a broader discharge
   that does not rely on that narrow setup. *)
Definition raychaudhuri_open_obligation := lorentzian_coupling_positive.
