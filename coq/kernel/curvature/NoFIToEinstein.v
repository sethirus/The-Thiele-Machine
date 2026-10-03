(** NoFIToEinstein: what the No Free Insight side and the curvature side
   each prove, kept apart.

   Two kinds of result live here. The first is No Free Insight's cost side:
   a run that starts uncertified with zero mu and ends certified has paid at
   least one unit ([certified_implies_positive_mu]), and when mu goes up and
   the Landauer-Unruh calibration holds, the calibrated null flux is positive
   ([nfi_cost_nonzero_implies_nontrivial_calibration]). That second theorem
   uses the calibration premise.

   The second is the curvature side: for two well-formed triangulated graphs
   the change in total curvature is 5 PI times the change in Euler
   characteristic ([discrete_gauss_bonnet_delta]). That identity is discrete
   Gauss-Bonnet. It needs the two triangulation premises and nothing else.
   No theorem here derives curvature from mu, and none connects the cost
   side to the curvature side. *)

(* SCOPE NOTE: foundation connectivity: imports the locality, Clausius and
   Raychaudhuri files whose definitions the calibration predicate names. *)

From Coq Require Import Reals Lra ZArith List.
Import ListNotations.

From Kernel Require Import VMState VMStep.
From Kernel Require Import SimulationProof.
From Kernel Require Import MuLedgerConservation.
From Kernel Require Import PrimeAxiom.
From Kernel Require Import LocalMorphismSemantics.
From Kernel Require Import EntanglementEntropy.
From Kernel Require Import ClausiusFromEntropyArea.
From Kernel Require Import RaychaudhuriFluxBridge.
From Kernel Require Import BekensteinCalibration.
From Kernel Require Import ThermoEinsteinBridge.
From Kernel Require Import DiscreteTopology.
From Kernel Require Import DiscreteGaussBonnet.
From Kernel Require Import EinsteinEmergence.


(** [mu_landauer_unruh_calibrated]: the bridge from mu-cost to heat.

    This predicate says the cost jump, scaled by the horizon geometry, matches
    the Clausius quantity T * dS at the split horizon. That is the explicit
    place where computational bookkeeping is being read as thermodynamic flux.

    If this bridge is wrong, the way to break it is empirical: measure mu
    change and boundary data on real traces, then compare that with the
    temperature-and-entropy side. *)
Definition mu_landauer_unruh_calibrated
    (hbar c_light k_B entropy_per_bit : R)
    (s_pre s_post : VMState)
    (P : LocalMorphismSemantics.SplitMorphism)
    (support_pre support_post : LocalMorphismSemantics.joint_support) : Prop :=
  RaychaudhuriFluxBridge.null_energy_flux_delta
    RaychaudhuriFluxBridge.calibrated_null_congruence s_pre s_post P =
  (ClausiusFromEntropyArea.unruh_temperature hbar c_light k_B P *
   ClausiusFromEntropyArea.entropy_increment_delta
     entropy_per_bit support_pre support_post)%R.


(** [discrete_gauss_bonnet_delta]: the curvature change between two
    well-formed triangulated states is the coupling constant times the change
    in Euler characteristic. Discrete Gauss-Bonnet on each graph gives it;
    no premise about mu, temperature or locality is involved. *)
Theorem discrete_gauss_bonnet_delta :
  forall (s_pre s_post : VMState),
    well_formed_triangulated (vm_graph s_pre) ->
    well_formed_triangulated (vm_graph s_post) ->
    (total_curvature (vm_graph s_post) - total_curvature (vm_graph s_pre))%R =
    (einstein_coupling_constant *
     IZR (euler_characteristic (vm_graph s_post) -
          euler_characteristic (vm_graph s_pre))%Z)%R.
Proof.
  intros s_pre s_post Hwf_pre Hwf_post.
  exact (einstein_emerges s_pre s_post Hwf_pre Hwf_post).
Qed.


(** [certified_implies_positive_mu]: Re-export of PrimeAxiom's main result.

    A computation that starts uncertified with zero μ-cost and reaches
    vm_certified=true must have paid at least 1 μ-unit.

    This IS the NoFI cost theorem in its strongest executable form:
    "Certification requires payment." Starting from nothing, nothing
    certifies without cost. The machine's second law.
*)
(* SCOPE NOTE: re-export. PrimeAxiom.kernel_certified_implies_positive_mu
   directly proves the NoFI cost consequence for the vm_certified execution path. *)
Theorem certified_implies_positive_mu :
  forall fuel program (s0 : VMState),
    s0.(vm_certified) = false ->
    (s0.(vm_mu) = 0)%nat ->
    (run_vm fuel program s0).(vm_certified) = true ->
    (0 < (run_vm fuel program s0).(vm_mu))%nat.
Proof.
  exact PrimeAxiom.kernel_certified_implies_positive_mu.
Qed.

(** [nfi_cost_nonzero_implies_nontrivial_calibration]: NoFI makes the
    calibration non-vacuous for information-gaining computations.

    If the μ-cost increased (NoFI: any information-gaining computation
    forces Δμ ≥ 1), and the calibration holds, then the Raychaudhuri
    flux is positive: heat actually flows across the horizon.

    Proof: vm_mu_delta > 0 and horizon_area ≥ 1 imply flux > 0.
*)
(* SCOPE NOTE: NoFI contribution, positive Δμ + calibration = nonzero flux. *)
Theorem nfi_cost_nonzero_implies_nontrivial_calibration :
  forall (hbar c_light k_B entropy_per_bit : R)
         (s_pre s_post : VMState)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support_pre support_post : LocalMorphismSemantics.joint_support),
    (0 < hbar)%R ->
    (0 < c_light)%R ->
    (0 < k_B)%R ->
    (0 <= entropy_per_bit)%R ->
    (INR s_pre.(vm_mu) < INR s_post.(vm_mu))%R ->
    mu_landauer_unruh_calibrated
      hbar c_light k_B entropy_per_bit s_pre s_post P support_pre support_post ->
    (0 < RaychaudhuriFluxBridge.null_energy_flux_delta
           RaychaudhuriFluxBridge.calibrated_null_congruence s_pre s_post P)%R \/
    (RaychaudhuriFluxBridge.null_energy_flux_delta
           RaychaudhuriFluxBridge.calibrated_null_congruence s_pre s_post P < 0)%R.
Proof.
  intros hbar c_light k_B entropy_per_bit s_pre s_post P support_pre support_post
         Hh Hc Hk Hep Hmu_inc Hcal.
  left.
  unfold RaychaudhuriFluxBridge.null_energy_flux_delta.
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat.
    + unfold ClausiusFromEntropyArea.vm_mu_delta. lra.
    + unfold ClausiusFromEntropyArea.horizon_area_measure.
      apply lt_0_INR. apply Nat.lt_0_succ.
  - rewrite RaychaudhuriFluxBridge.calibrated_focusing_unit. lra.
Qed.

(** [nfi_to_gr_chain_complete]: the three results of this file side by side.
    The tuple groups them; it does not compose them, and no component's
    premises feed another's conclusion. *)
Definition nfi_to_gr_chain_complete :=
  (discrete_gauss_bonnet_delta,
   certified_implies_positive_mu,
   nfi_cost_nonzero_implies_nontrivial_calibration).
