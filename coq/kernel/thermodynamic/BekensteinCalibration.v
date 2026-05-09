(** BekensteinCalibration: explicit assumptions for Landauer-Unruh calibration.

    This file exists to name the physics gap instead of hand-waving past it. If
    you assume a Bekenstein-style saturation relation and then plug in the
    Landauer entropy per bit, the algebra tells you what energy per mu-unit
    would have to look like. But that still does not identify the VM cost unit
    with physical energy by magic.

    So the missing step is made explicit as a named hypothesis. That is the
    honest move here. The file gives the clean algebra it can prove directly and
    forces callers to state the extra calibration premise when they want the
    physical bridge. *)

From Coq Require Import Reals Lra Lia List.
Import ListNotations.
From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import MuCostModel.
From Kernel Require Import LocalMorphismSemantics.
From Kernel Require Import EntanglementEntropy.
From Kernel Require Import ClausiusFromEntropyArea.
From Kernel Require Import RaychaudhuriFluxBridge.

Local Open Scope R_scope.

(** The Bekenstein-Rindler algebra this file can prove directly. *)

(** [bekenstein_rindler_energy_per_bit]: Pure algebra, no VM hypothesis.
    Given Bekenstein saturation (E = T_Unruh × S) and Landauer
    entropy (S = n_bits × k_B × ln 2), the energy per bit is T × k_B × ln 2.

    The theorem does not prove saturation. It says that if saturation is one of
    your inputs, the Landauer energy per bit falls out by algebra. *)
(* INQUISITOR NOTE: Pure algebra, Bekenstein saturation plus Landauer entropy gives energy per bit. *)
Theorem bekenstein_rindler_energy_per_bit :
  forall (k_B T_Unruh n_bits E_total : R),
    0 < n_bits ->
    0 < T_Unruh ->
    (* Bekenstein saturation: energy = T_Unruh × (n_bits × k_B × ln 2) *)
    E_total = T_Unruh * (n_bits * k_B * ln 2) ->
    (* Conclusion: energy per bit = Landauer energy T × k_B × ln 2 *)
    E_total / n_bits = T_Unruh * k_B * ln 2.
Proof.
  intros k_B T_Unruh n_bits E_total Hn HT Hsat.
  rewrite Hsat. field. lra.
Qed.

(** [bekenstein_entropy_energy_ratio]: If the saturation equality is assumed,
    then entropy divided by energy is 1/T_Unruh. *)
(* INQUISITOR NOTE: Bekenstein equality gives S/E = 1/T *)
Theorem bekenstein_entropy_energy_ratio :
  forall (T_Unruh S_total E_total : R),
    0 < E_total ->
    0 < T_Unruh ->
    (* Bekenstein saturation *)
    E_total = T_Unruh * S_total ->
    0 < S_total ->
    (* Conclusion: ratio S/E = 1/T *)
    S_total / E_total = 1 / T_Unruh.
Proof.
  intros T_Unruh S_total E_total HE HT Hsat HS.
  rewrite Hsat. field. lra.
Qed.

(** Named hypotheses that close the physics-to-VM gap. *)

(** [landauer_unruh_constant_calibration]: a unit-system calibration, not a
    derived physical constant. It is the relation needed by the algebra below
    to identify the split-geometry horizon unit with the Landauer energy unit. *)
Definition landauer_unruh_constant_calibration
  (hbar c_light : R) : Prop :=
  (hbar * ln 2 = 2 * PI * c_light)%R.

(** [mu_energy_unit_is_landauer]: The Thiele Machine's μ-cost unit is
    calibrated such that one μ-unit = Landauer erasure energy at the
    local Rindler horizon temperature.

    PHYSICAL MEANING: When the VM charges cost 1 via REVEAL/EMIT/etc,
    this hypothesis says it represents erasing one bit of information at the
    Rindler temperature T_Unruh, dissipating energy E = T_Unruh × k_B × ln 2.

    To falsify: Measure the energy consumed per vm_mu increment on
    physical hardware operating at temperature T. Compare against
    T × k_B × ln 2 × (number of bits per instruction). *)
Definition mu_energy_unit_is_landauer
    (hbar c_light k_B : R)
    (s_pre s_post : VMState)
    (P : LocalMorphismSemantics.SplitMorphism) : Prop :=
  (* The null energy flux per μ-unit at the horizon equals Landauer energy *)
  ClausiusFromEntropyArea.vm_mu_delta s_pre s_post *
  ClausiusFromEntropyArea.horizon_area_measure P =
  ClausiusFromEntropyArea.unruh_temperature hbar c_light k_B P *
  ClausiusFromEntropyArea.vm_mu_delta s_pre s_post *
  (k_B * ln 2).

(** [landauer_entropy_identification]: the caller's entropy bridge.
    It says each μ-unit corresponds to k_B × ln 2 of entropy change.

    This file does not derive that bridge from NoFI. It packages it as a
    hypothesis so later theorems can show exactly where it is used. *)
Definition landauer_entropy_identification
    (k_B entropy_per_bit : R)
    (support_pre support_post : LocalMorphismSemantics.joint_support)
    (s_pre s_post : VMState) : Prop :=
  entropy_per_bit = k_B * ln 2 /\
  ClausiusFromEntropyArea.entropy_increment_delta
    entropy_per_bit support_pre support_post =
  k_B * ln 2 *
  ClausiusFromEntropyArea.vm_mu_delta s_pre s_post.

(** [mu_bit_calibration]: the machine-native version of the entropy bridge.

    This isolates the empirical content of the entropy identification:
    the support-level entropy change in bits equals the VM μ-cost delta. *)
Definition mu_bit_calibration
    (support_pre support_post : LocalMorphismSemantics.joint_support)
    (s_pre s_post : VMState) : Prop :=
  (INR (entanglement_entropy_vn_bits support_post) -
   INR (entanglement_entropy_vn_bits support_pre))%R =
  ClausiusFromEntropyArea.vm_mu_delta s_pre s_post.

(** If support entropy in bits matches μ, then multiplying by k_B ln 2 gives
    the Landauer entropy identification. *)
Theorem landauer_identification_from_bit_calibration :
  forall (k_B : R)
         (support_pre support_post : LocalMorphismSemantics.joint_support)
         (s_pre s_post : VMState),
    (0 < k_B)%R ->
    mu_bit_calibration support_pre support_post s_pre s_post ->
    landauer_entropy_identification
      k_B (k_B * ln 2) support_pre support_post s_pre s_post.
Proof.
  intros k_B support_pre support_post s_pre s_post _ Hbit.
  unfold landauer_entropy_identification.
  split.
  - reflexivity.
  - assert (Hdelta :
        ClausiusFromEntropyArea.entropy_increment_delta
          (k_B * ln 2) support_pre support_post =
        ((k_B * ln 2) *
         (INR (entanglement_entropy_vn_bits support_post) -
          INR (entanglement_entropy_vn_bits support_pre)))%R).
    {
      unfold ClausiusFromEntropyArea.entropy_increment_delta,
             ClausiusFromEntropyArea.entropy_increment.
      ring.
    }
    rewrite Hdelta.
    unfold mu_bit_calibration in Hbit.
    rewrite Hbit.
    ring.
Qed.

(** PSPLIT uses the cartesian product of its normalized regions as the support
    event whose entropy is charged to μ. *)
Definition psplit_entropy_event
    (left right : list nat) : LocalMorphismSemantics.joint_support :=
  LocalMorphismSemantics.cartesian_pairs
    (normalize_region left) (normalize_region right).

(** The PSPLIT price tag is explicit: the declared cost must equal the
    entropy computed for the PSPLIT support event. *)
Definition psplit_cost_matches_entropy
    (left right : list nat) (cost : nat) : Prop :=
  cost = entanglement_entropy_vn_bits (psplit_entropy_event left right).

(** The empty support has zero von Neumann support entropy in this finite model. *)
Lemma entanglement_entropy_vn_bits_nil :
  entanglement_entropy_vn_bits [] = 0%nat.
Proof.
  unfold entanglement_entropy_vn_bits,
         reduced_state_support,
         partial_trace_right_support.
  simpl.
  apply Nat.log2_up_nonpos.
  lia.
Qed.

(** A PSPLIT step increases vm_mu by the declared instruction cost. *)
Lemma vm_mu_delta_of_psplit_step :
  forall s s' module left right cost,
    vm_step s (instr_psplit module left right cost) s' ->
    ClausiusFromEntropyArea.vm_mu_delta s s' = INR cost.
Proof.
  intros s s' module left right cost Hstep.
  inversion Hstep; subst.
  unfold ClausiusFromEntropyArea.vm_mu_delta,
         advance_state,
         apply_cost.
  simpl.
  rewrite plus_INR.
  lra.
Qed.

(** When PSPLIT's declared cost matches the support entropy event, the step
    satisfies the machine-native bit calibration. *)
Theorem psplit_step_mu_bit_calibration :
  forall s s' module left right cost,
    vm_step s (instr_psplit module left right cost) s' ->
    psplit_cost_matches_entropy left right cost ->
    mu_bit_calibration [] (psplit_entropy_event left right) s s'.
Proof.
  intros s s' module left right cost Hstep Hcost.
  unfold mu_bit_calibration, psplit_cost_matches_entropy.
  rewrite entanglement_entropy_vn_bits_nil.
  rewrite vm_mu_delta_of_psplit_step
    with (module := module) (left := left) (right := right) (cost := cost);
    try exact Hstep.
  unfold psplit_entropy_event.
  rewrite <- Hcost.
  simpl.
  lra.
Qed.

(** A PSPLIT step can be represented as a local split morphism whose support
    trace contains the empty pre-event and the PSPLIT entropy event. *)
Theorem psplit_step_realizes_transition_entropy_event :
  forall s s' module left right cost,
    vm_step s (instr_psplit module left right cost) s' ->
    psplit_cost_matches_entropy left right cost ->
    exists P : LocalMorphismSemantics.SplitMorphism,
      LocalMorphismSemantics.split_left P = normalize_region left /\
      LocalMorphismSemantics.split_right P = normalize_region right /\
      In [] (LocalMorphismSemantics.morphism_support_semantics P) /\
      In (psplit_entropy_event left right)
         (LocalMorphismSemantics.morphism_support_semantics P) /\
      mu_bit_calibration [] (psplit_entropy_event left right) s s'.
Proof.
  intros s s' module left right cost Hstep Hcost.
  exists (LocalMorphismSemantics.psplit_transition_morphism left right).
  simpl.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * left. reflexivity.
      * split.
        -- right. left. reflexivity.
        -- eapply psplit_step_mu_bit_calibration; eauto.
Qed.

(** Landauer hypotheses imply the calibrated flux equation. *)

(** The constant calibration is a strong unit choice. Under that choice, the
    algebraic definition of [mu_energy_unit_is_landauer] follows for any
    split morphism and any VM states. *)
Theorem landauer_unruh_constant_calibration_implies_mu_energy_unit_is_landauer :
  forall (hbar c_light k_B : R)
         (s_pre s_post : VMState)
         (P : LocalMorphismSemantics.SplitMorphism),
    (0 < c_light)%R ->
    (0 < k_B)%R ->
    landauer_unruh_constant_calibration hbar c_light ->
    mu_energy_unit_is_landauer hbar c_light k_B s_pre s_post P.
Proof.
  intros hbar c_light k_B s_pre s_post P Hc Hk Hcal.
  assert (Hpi : (0 < PI)%R) by apply PI_RGT_0.
  assert (Hcal' : (2 * PI * c_light = hbar * ln 2)%R).
  { unfold landauer_unruh_constant_calibration in Hcal. lra. }
  assert (Hhln : (0 < hbar * ln 2)%R).
  { rewrite <- Hcal'. nra. }
  unfold mu_energy_unit_is_landauer.
  rewrite ClausiusFromEntropyArea.horizon_area_measure_eq_horizon_acceleration.
  unfold ClausiusFromEntropyArea.unruh_temperature.
  rewrite Hcal'.
  set (delta := ClausiusFromEntropyArea.vm_mu_delta s_pre s_post).
  set (a := ClausiusFromEntropyArea.horizon_acceleration_from_split P).
  replace ((hbar * a / (hbar * ln 2 * k_B) * delta * (k_B * ln 2))%R)
    with ((delta * a) * (hbar * (k_B * ln 2) / (hbar * ln 2 * k_B)))%R
    by (field; nra).
  assert (Hunit : (hbar * (k_B * ln 2) / (hbar * ln 2 * k_B) = 1)%R).
  {
    field.
    nra.
  }
  rewrite Hunit.
  ring.
Qed.

(** [bekenstein_implies_landauer_calibration]: The two named physical
    hypotheses (mu_energy_unit_is_landauer + landauer_entropy_identification)
    together imply mu_landauer_unruh_calibrated.

    - mu_energy_unit_is_landauer says:
        vm_mu_delta × area = T_Unruh × vm_mu_delta × k_B × ln 2
    - landauer_entropy_identification says:
        entropy_increment_delta = k_B × ln 2 × vm_mu_delta
    - Combining: vm_mu_delta × area = T_Unruh × entropy_increment_delta
    - But null_energy_flux_delta = vm_mu_delta × area × 1 (focusing=1)
    - Therefore: null_energy_flux_delta = T_Unruh × entropy_increment_delta
    = mu_landauer_unruh_calibrated.                                          *)
(* INQUISITOR NOTE: Two named physical hypotheses give the calibration equation. *)
Theorem bekenstein_implies_landauer_calibration :
  forall (hbar c_light k_B entropy_per_bit : R)
         (s_pre s_post : VMState)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support_pre support_post : LocalMorphismSemantics.joint_support),
    mu_energy_unit_is_landauer hbar c_light k_B s_pre s_post P ->
    landauer_entropy_identification
      k_B entropy_per_bit support_pre support_post s_pre s_post ->
    RaychaudhuriFluxBridge.null_energy_flux_delta
      RaychaudhuriFluxBridge.calibrated_null_congruence s_pre s_post P =
    (ClausiusFromEntropyArea.unruh_temperature hbar c_light k_B P *
     ClausiusFromEntropyArea.entropy_increment_delta
       entropy_per_bit support_pre support_post)%R.
Proof.
  intros hbar c_light k_B entropy_per_bit s_pre s_post P support_pre support_post
         Henergy [Hep Hentropy].
  unfold RaychaudhuriFluxBridge.null_energy_flux_delta.
  rewrite RaychaudhuriFluxBridge.calibrated_focusing_unit.
  (* After rewrite: vm_mu_delta * horizon_area * 1 = T * entropy_increment_delta *)
  unfold ClausiusFromEntropyArea.heat_flux_delta_from_split in *.
  (* Use mu_energy_unit_is_landauer: vm_mu_delta * area = T * vm_mu_delta * k_B * ln2 *)
  (* Use landauer_entropy_identification: entropy_increment_delta = k_B * ln2 * vm_mu_delta *)
  rewrite Hentropy.
  unfold mu_energy_unit_is_landauer in Henergy.
  ring_simplify.
  (* Goal: vm_mu_delta * area * 1 = T * (k_B * ln2 * vm_mu_delta) *)
  (* From Henergy: vm_mu_delta * area = T * vm_mu_delta * k_B * ln2 *)
  lra.
Qed.

(** Replace [mu_energy_unit_is_landauer] with the explicit constant
    calibration, while keeping the entropy bridge as an input. *)
Theorem mu_landauer_unruh_calibrated_from_constant_calibration :
  forall (hbar c_light k_B entropy_per_bit : R)
         (s_pre s_post : VMState)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support_pre support_post : LocalMorphismSemantics.joint_support),
    (0 < c_light)%R ->
    (0 < k_B)%R ->
    landauer_unruh_constant_calibration hbar c_light ->
    landauer_entropy_identification
      k_B entropy_per_bit support_pre support_post s_pre s_post ->
    RaychaudhuriFluxBridge.null_energy_flux_delta
      RaychaudhuriFluxBridge.calibrated_null_congruence s_pre s_post P =
    (ClausiusFromEntropyArea.unruh_temperature hbar c_light k_B P *
     ClausiusFromEntropyArea.entropy_increment_delta
       entropy_per_bit support_pre support_post)%R.
Proof.
  intros hbar c_light k_B entropy_per_bit s_pre s_post P support_pre support_post
         Hc Hk Hcal Hentropy.
  apply bekenstein_implies_landauer_calibration.
  - apply landauer_unruh_constant_calibration_implies_mu_energy_unit_is_landauer;
      assumption.
  - exact Hentropy.
Qed.

(** The most concrete bridge in this file: constant calibration plus
    machine-native bit calibration give the Landauer-Unruh flux equation. *)
Theorem mu_landauer_unruh_calibrated_from_constant_and_bit_calibration :
  forall (hbar c_light k_B : R)
         (s_pre s_post : VMState)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support_pre support_post : LocalMorphismSemantics.joint_support),
    (0 < c_light)%R ->
    (0 < k_B)%R ->
    landauer_unruh_constant_calibration hbar c_light ->
    mu_bit_calibration support_pre support_post s_pre s_post ->
    RaychaudhuriFluxBridge.null_energy_flux_delta
      RaychaudhuriFluxBridge.calibrated_null_congruence s_pre s_post P =
    (ClausiusFromEntropyArea.unruh_temperature hbar c_light k_B P *
     ClausiusFromEntropyArea.entropy_increment_delta
       (k_B * ln 2) support_pre support_post)%R.
Proof.
  intros hbar c_light k_B s_pre s_post P support_pre support_post
         Hc Hk Hconst Hbit.
  apply (mu_landauer_unruh_calibrated_from_constant_calibration
           hbar c_light k_B (k_B * ln 2)
           s_pre s_post P support_pre support_post);
    try assumption.
  apply landauer_identification_from_bit_calibration; assumption.
Qed.

(** What the Bekenstein calculation establishes. *)

(** [bekenstein_establishes_energy_ratio]: The Bekenstein calculation above
    proves the energy-per-bit ratio once saturation is assumed. This alias names
    that exact theorem for downstream files.

    The argument:
    1. Bekenstein bound: S ≤ 2π k_B R E / (ℏ c) at radius R
    2. Rindler horizon: R = c²/a, T_Unruh = ℏa/(2π c k_B)
    3. Substituting: S ≤ E / T_Unruh  (Rindler version of Bekenstein)
    4. Saturation (thermal equilibrium): S = E / T_Unruh → E = T_Unruh × S
    5. Each μ unit = one Landauer bit: S = k_B ln 2 per μ unit
    6. Therefore: E per μ unit = T_Unruh × k_B × ln 2  [Landauer energy]

    Steps 1-6 are the calculation. The identification of VM energy with
    physical energy is still the named hypothesis [mu_energy_unit_is_landauer].
    The calculation gives a ratio, not a free calibration of VM units. *)
Definition bekenstein_rindler_ratio_justified := bekenstein_rindler_energy_per_bit.

(** Summary: after the constants calibration is made explicit, the remaining
    semantic input is the ledger-to-support entropy identification. *)
Definition bekenstein_calibration_open_obligation :=
  mu_bit_calibration.

(** PNEW entropy calibration.
    This extends the same support-entropy check to the module-creation
    instruction family.

    MODEL INTERPRETATION: The support event for a new module is the
    self-support of the normalized region. The entropy calculation then reads
    off log₂ of that finite support size.
*)

(** The entropy event for PNEW: each region element paired with itself,
    forming a diagonal joint_support.  The reduced-state support equals
    the normalized region, so the entropy is log₂(|region|) bits. *)
Definition pnew_entropy_event
    (region : list nat) : LocalMorphismSemantics.joint_support :=
  map (fun x => (x, x)) (normalize_region region).

(** Cost-entropy matching for PNEW. *)
Definition pnew_cost_matches_entropy
    (region : list nat) (cost : nat) : Prop :=
  cost = entanglement_entropy_vn_bits (pnew_entropy_event region).

(** μ-delta for a PNEW step equals the declared cost. *)
Lemma vm_mu_delta_of_pnew_step :
  forall s s' region cost,
    vm_step s (instr_pnew region cost) s' ->
    ClausiusFromEntropyArea.vm_mu_delta s s' = INR cost.
Proof.
  intros s s' region cost Hstep.
  inversion Hstep; subst.
  unfold ClausiusFromEntropyArea.vm_mu_delta,
         advance_state,
         apply_cost.
  simpl.
  rewrite plus_INR.
  lra.
Qed.

(** The reduced-state support of the PNEW diagonal event equals the
    normalized region (since nodup is idempotent on normalize_region). *)
Lemma pnew_reduced_support_eq :
  forall region,
    reduced_state_support (pnew_entropy_event region) =
    normalize_region region.
Proof.
  intro region.
  unfold pnew_entropy_event, reduced_state_support,
         partial_trace_right_support.
  rewrite map_map. simpl.
  rewrite map_id.
  apply normalize_region_idempotent.
Qed.

(** PNEW satisfies mu_bit_calibration when the cost matches the
    entropy of the new module's region. *)
Theorem pnew_step_mu_bit_calibration :
  forall s s' region cost,
    vm_step s (instr_pnew region cost) s' ->
    pnew_cost_matches_entropy region cost ->
    mu_bit_calibration [] (pnew_entropy_event region) s s'.
Proof.
  intros s s' region cost Hstep Hcost.
  unfold mu_bit_calibration, pnew_cost_matches_entropy.
  rewrite entanglement_entropy_vn_bits_nil.
  rewrite vm_mu_delta_of_pnew_step
    with (region := region) (cost := cost);
    try exact Hstep.
  rewrite <- Hcost.
  simpl.
  lra.
Qed.

(** [natural_units_consistency]: In the computational unit system defined by
    landauer_unruh_constant_calibration, the ratio hbar * ln 2 / (2 * PI * c_light)
    equals 1. This confirms what the calibration definition says: it is a
    dimensionless unit normalization. *)
Lemma natural_units_consistency :
  forall (hbar c_light : R),
    (0 < c_light)%R ->
    landauer_unruh_constant_calibration hbar c_light ->
    (hbar * ln 2) / (2 * PI * c_light) = 1%R.
Proof.
  intros hbar c_light Hc Hcal.
  unfold landauer_unruh_constant_calibration in Hcal.
  assert (HPI : (0 < PI)%R) by apply PI_RGT_0.
  rewrite Hcal. field; lra.
Qed.
