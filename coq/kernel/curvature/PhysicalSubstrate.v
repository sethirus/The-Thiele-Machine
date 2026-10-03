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

    Item (b) is the Landauer-Unruh unit bridge: it equates one μ-unit to
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

(** ** Non-vacuity: natural_units_substrate

    This section exhibits a concrete substrate instance using "natural units" where
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

(** ** Bedrock statement.

    The typeclass is consistent: [natural_units_substrate] satisfies the
    positivity conditions and the calibration relation together. The
    instance does not purport to match any particular physical measurement.
    A real deployment would provide an instance calibrated to its operating
    temperature and energy scale.

    No theorem here derives curvature from the substrate. The discrete
    Gauss-Bonnet delta identity ([NoFIToEinstein.discrete_gauss_bonnet_delta])
    holds for any two well-formed triangulated states with no substrate
    premise at all.

    This is the metrological boundary. Proving ps_landauer_calibrated for a
    specific physical substrate would require empirical measurement of hbar,
    c and k_B in whatever unit system the VM operates in; that is outside the
    scope of formal verification. *)
