(** PhysicalSubstrate.v

    Typeclass bundling the physical constants (k_B, ħ, c) with their
    positivity conditions and the Landauer-Unruh calibration relation.

    PURPOSE: The Bekenstein calibration theorems in BekensteinCalibration.v
    already accept physical constants as explicit arguments.  This file
    creates a named record for those constants so callers can work with
    "any substrate obeying Landauer" rather than explicitly mentioning
    hbar, c_light, k_B everywhere.

    METROLOGICAL BOUNDARY: The exact values of k_B, ħ, c are physical
    measurements (SI definitions, not mathematical theorems).  This typeclass
    captures the algebraic structure that the proofs require:
      (a) all constants are strictly positive, and
      (b) the unit-system calibration hbar * ln 2 = 2 * PI * c_light holds.

    Item (b) is the Landauer-Unruh unit bridge — it equates one μ-unit to
    one bit-erasure energy at the Rindler horizon.  It is not derivable from
    (a) alone; it is the statement that the VM's μ unit is calibrated in the
    same system as the physical constants.

    INSTANCE: natural_units_substrate demonstrates non-vacuity.
    Any physical implementation can provide its own instance by measuring
    its operating constants and verifying the calibration relation holds.
*)

From Coq Require Import Reals Lra Lia List ZArith.
Import ListNotations.

From Kernel Require Import VMState VMStep.
From Kernel Require Import LocalMorphismSemantics.
From Kernel Require Import EntanglementEntropy.
From Kernel Require Import ClausiusFromEntropyArea.
From Kernel Require Import RaychaudhuriFluxBridge.
From Kernel Require Import BekensteinCalibration.
From Kernel Require Import DiscreteTopology.
From Kernel Require Import DiscreteGaussBonnet.
From Kernel Require Import EinsteinEmergence.
From Kernel Require Import NoFIToEinstein.

Open Scope R_scope.

(** ** The typeclass *)

Class PhysicalSubstrate := {
  (** The three fundamental constants. *)
  ps_k_B     : R;
  ps_hbar    : R;
  ps_c_light : R;

  (** Positivity: all three are strictly positive. *)
  ps_k_B_pos     : 0 < ps_k_B;
  ps_hbar_pos    : 0 < ps_hbar;
  ps_c_light_pos : 0 < ps_c_light;

  (** Unit-system calibration: ħ ln 2 = 2π c_light.
      This relation identifies 1 μ-unit with 1 bit-erasure energy
      at the Rindler-horizon temperature T_Unruh.
      In SI units this requires a specific choice of energy/time scale;
      in the abstract algebra it is the single constraint that ties
      mu-cost bookkeeping to thermodynamics. *)
  ps_landauer_calibrated :
    BekensteinCalibration.landauer_unruh_constant_calibration ps_hbar ps_c_light;
}.

(** ** Main corollary: discrete Einstein emergence from a physical substrate.

    Given any substrate satisfying the typeclass, the existing
    nfi_to_discrete_einstein_from_bekenstein_calibration chain applies
    directly.  The proof just names the typeclass fields and forwards. *)
Theorem substrate_implies_discrete_einstein
    `{sub : PhysicalSubstrate}
    (s_pre s_post : VMState)
    (P : LocalMorphismSemantics.SplitMorphism)
    (support_pre support_post : LocalMorphismSemantics.joint_support) :
    LocalMorphismSemantics.is_nearest_neighbor P ->
    In support_pre (LocalMorphismSemantics.morphism_support_semantics P) ->
    In support_post (LocalMorphismSemantics.morphism_support_semantics P) ->
    BekensteinCalibration.mu_bit_calibration
      support_pre support_post s_pre s_post ->
    well_formed_triangulated (vm_graph s_pre) ->
    well_formed_triangulated (vm_graph s_post) ->
    (total_curvature (vm_graph s_post) -
     total_curvature (vm_graph s_pre))%R =
    (einstein_coupling_constant *
     IZR (euler_characteristic (vm_graph s_post) -
          euler_characteristic (vm_graph s_pre))%Z)%R.
Proof.
  intros Hnn Hin_pre Hin_post Hbit Hwf_pre Hwf_post.
  exact (NoFIToEinstein.nfi_to_discrete_einstein_from_bekenstein_calibration
           ps_hbar ps_c_light ps_k_B
           s_pre s_post P support_pre support_post
           ps_hbar_pos ps_c_light_pos ps_k_B_pos
           Hnn Hin_pre Hin_post
           ps_landauer_calibrated
           Hbit
           Hwf_pre Hwf_post).
Qed.

(** ** Non-vacuity: natural_units_substrate

    We exhibit a concrete substrate instance using "natural units" where
    all dimensionful constants are chosen to make the algebra work.
    Setting hbar := 2*PI and c_light := ln 2 satisfies:
        hbar * ln 2 = 2*PI * ln 2  and  2 * PI * c_light = 2*PI * ln 2.
    Both k_B := 1 and the two positivity facts follow from standard Reals. *)
Instance natural_units_substrate : PhysicalSubstrate := {|
  ps_k_B     := 1;
  ps_hbar    := 2 * PI;
  ps_c_light := ln 2;
  ps_k_B_pos     := Rlt_0_1;
  ps_hbar_pos    := (ltac:(apply Rmult_lt_0_compat;
                             [lra | exact PI_RGT_0]));
  ps_c_light_pos := (ltac:(rewrite <- ln_1; apply ln_increasing; lra));
  ps_landauer_calibrated := (ltac:(unfold BekensteinCalibration.landauer_unruh_constant_calibration;
                                    ring));
|}.

(** ** PSPLIT-specific discrete Einstein, using the substrate typeclass.

    This is the PSPLIT version of substrate_implies_discrete_einstein.
    Proof: delegate to nfi_to_discrete_einstein_from_psplit_bekenstein_calibration. *)
Theorem substrate_psplit_implies_discrete_einstein
    `{sub : PhysicalSubstrate}
    (s_pre s_post : VMState)
    (module : ModuleID)
    (left right : list nat)
    (cost : nat) :
    vm_step s_pre (instr_psplit module left right cost) s_post ->
    LocalMorphismSemantics.is_nearest_neighbor
      (LocalMorphismSemantics.psplit_transition_morphism left right) ->
    BekensteinCalibration.psplit_cost_matches_entropy left right cost ->
    well_formed_triangulated (vm_graph s_pre) ->
    well_formed_triangulated (vm_graph s_post) ->
    (total_curvature (vm_graph s_post) -
     total_curvature (vm_graph s_pre))%R =
    (einstein_coupling_constant *
     IZR (euler_characteristic (vm_graph s_post) -
          euler_characteristic (vm_graph s_pre))%Z)%R.
Proof.
  intros Hstep Hnn Hcost Hwf_pre Hwf_post.
  exact (NoFIToEinstein.nfi_to_discrete_einstein_from_psplit_bekenstein_calibration
           ps_hbar ps_c_light ps_k_B
           s_pre s_post module left right cost
           ps_hbar_pos ps_c_light_pos ps_k_B_pos
           Hstep Hnn ps_landauer_calibrated Hcost Hwf_pre Hwf_post).
Qed.

(** ** PNEW-specific discrete Einstein, using the substrate typeclass.

    This completes the bedrock-facing export surface for the two concrete
    structure-creating operations already handled in NoFIToEinstein.v.
    Proof: delegate to nfi_to_discrete_einstein_from_pnew_bekenstein_calibration. *)
Theorem substrate_pnew_implies_discrete_einstein
    `{sub : PhysicalSubstrate}
    (s_pre s_post : VMState)
    (region : list nat)
    (cost : nat) :
    vm_step s_pre (instr_pnew region cost) s_post ->
    LocalMorphismSemantics.is_nearest_neighbor
      (LocalMorphismSemantics.pnew_creation_morphism region) ->
    BekensteinCalibration.pnew_cost_matches_entropy region cost ->
    well_formed_triangulated (vm_graph s_pre) ->
    well_formed_triangulated (vm_graph s_post) ->
    (total_curvature (vm_graph s_post) -
     total_curvature (vm_graph s_pre))%R =
    (einstein_coupling_constant *
     IZR (euler_characteristic (vm_graph s_post) -
          euler_characteristic (vm_graph s_pre))%Z)%R.
Proof.
  intros Hstep Hnn Hcost Hwf_pre Hwf_post.
  exact (NoFIToEinstein.nfi_to_discrete_einstein_from_pnew_bekenstein_calibration
           ps_hbar ps_c_light ps_k_B
           s_pre s_post region cost
           ps_hbar_pos ps_c_light_pos ps_k_B_pos
           Hstep Hnn ps_landauer_calibrated Hcost Hwf_pre Hwf_post).
Qed.

(** ** Explicit bedrock statement.

    The following is the honest, irreducible bedrock for Item 2:

    > *Given a physical substrate that obeys Landauer's principle
    >  (ps_landauer_calibrated) with constants that are strictly positive,
    >  the NoFI theorem implies discrete Einstein emergence for any PSPLIT
    >  or PNEW operation.*

    The [natural_units_substrate] instance is a witness that such a
    substrate exists (the algebra is consistent).  It does not purport to
    match any particular physical measurement.  A real deployment would
    provide an instance calibrated to its operating temperature and
    energy scale.

    This is the metrological boundary.  Proving ps_landauer_calibrated for
    a specific physical substrate would require empirical measurement of ħ,
    c, and k_B in whatever unit system the VM operates in — that is outside
    the scope of formal verification. *)
Definition landauer_metrological_boundary_closed : Prop :=
  forall (sub : PhysicalSubstrate)
         (s_pre s_post : VMState)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support_pre support_post : LocalMorphismSemantics.joint_support),
    LocalMorphismSemantics.is_nearest_neighbor P ->
    In support_pre (LocalMorphismSemantics.morphism_support_semantics P) ->
    In support_post (LocalMorphismSemantics.morphism_support_semantics P) ->
    BekensteinCalibration.mu_bit_calibration
      support_pre support_post s_pre s_post ->
    well_formed_triangulated (vm_graph s_pre) ->
    well_formed_triangulated (vm_graph s_post) ->
    (total_curvature (vm_graph s_post) -
     total_curvature (vm_graph s_pre))%R =
    (einstein_coupling_constant *
     IZR (euler_characteristic (vm_graph s_post) -
          euler_characteristic (vm_graph s_pre))%Z)%R.

Theorem landauer_metrological_boundary_closed_proof :
    landauer_metrological_boundary_closed.
Proof.
  unfold landauer_metrological_boundary_closed.
  intros sub s_pre s_post P support_pre support_post Hnn Hpre Hpost Hbit Hwf_pre Hwf_post.
  exact (substrate_implies_discrete_einstein
           s_pre s_post P support_pre support_post
           Hnn Hpre Hpost Hbit Hwf_pre Hwf_post).
Qed.
