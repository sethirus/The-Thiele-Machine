(** Raychaudhuri Flux Bridge

    Provide a dedicated null-congruence flux layer with explicit expansion
    and shear terms, and connect that flux to the Clausius heat/entropy link
    used by ThermoEinsteinBridge.

    The key point is structural honesty: heat flux is represented by a null
    flux object built from congruence terms, and only then related to the
    Clausius product side.
*)

From Coq Require Import Reals Lra.

From Kernel Require Import VMState.
From Kernel Require Import LocalMorphismSemantics.
From Kernel Require Import ClausiusFromEntropyArea.

Section RaychaudhuriFlux.

Record NullCongruence := {
  expansion_scalar : LocalMorphismSemantics.SplitMorphism -> R;
  shear_scalar : LocalMorphismSemantics.SplitMorphism -> R
}.

Definition null_expansion
  (nc : NullCongruence)
  (P : LocalMorphismSemantics.SplitMorphism) : R :=
  expansion_scalar nc P.

Definition null_shear
  (nc : NullCongruence)
  (P : LocalMorphismSemantics.SplitMorphism) : R :=
  shear_scalar nc P.

Definition raychaudhuri_focusing
  (nc : NullCongruence)
  (P : LocalMorphismSemantics.SplitMorphism) : R :=
  (null_expansion nc P - null_shear nc P)%R.

Definition null_energy_flux
  (nc : NullCongruence)
  (s : VMState)
  (P : LocalMorphismSemantics.SplitMorphism) : R :=
  (INR s.(vm_mu) *
   ClausiusFromEntropyArea.horizon_area_measure P *
   raychaudhuri_focusing nc P)%R.

Definition null_energy_flux_delta
  (nc : NullCongruence)
  (s_pre s_post : VMState)
  (P : LocalMorphismSemantics.SplitMorphism) : R :=
  (ClausiusFromEntropyArea.vm_mu_delta s_pre s_post *
   ClausiusFromEntropyArea.horizon_area_measure P *
   raychaudhuri_focusing nc P)%R.

Definition boundary_expansion_scalar
  (P : LocalMorphismSemantics.SplitMorphism) : R :=
  ClausiusFromEntropyArea.horizon_acceleration_from_split P.

Definition boundary_shear_scalar
  (P : LocalMorphismSemantics.SplitMorphism) : R :=
  INR (LocalMorphismSemantics.boundary_size_1d
    (LocalMorphismSemantics.split_left P)
    (LocalMorphismSemantics.split_right P)).

Definition calibrated_null_congruence : NullCongruence :=
  {| expansion_scalar := boundary_expansion_scalar;
     shear_scalar := boundary_shear_scalar |}.

Lemma boundary_geodesic_focusing_unit :
  forall (P : LocalMorphismSemantics.SplitMorphism),
    raychaudhuri_focusing calibrated_null_congruence P = 1%R.
Proof.
  intro P.
  unfold raychaudhuri_focusing, null_expansion, null_shear,
         calibrated_null_congruence.
  simpl.
  unfold boundary_expansion_scalar, boundary_shear_scalar.
  unfold ClausiusFromEntropyArea.horizon_acceleration_from_split.
  set (b := INR
    (LocalMorphismSemantics.boundary_size_1d
      (LocalMorphismSemantics.split_left P)
      (LocalMorphismSemantics.split_right P))).
  change ((1 + b - b)%R = 1%R).
  ring.
Qed.

Lemma calibrated_focusing_unit :
  forall (P : LocalMorphismSemantics.SplitMorphism),
    raychaudhuri_focusing calibrated_null_congruence P = 1%R.
Proof.
  exact boundary_geodesic_focusing_unit.
Qed.

Theorem raychaudhuri_flux_implies_clausius_link :
  forall (hbar c_light k_B entropy_per_bit : R)
         (nc : NullCongruence)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support : LocalMorphismSemantics.joint_support)
         (s : VMState),
    raychaudhuri_focusing nc P = 1%R ->
    null_energy_flux nc s P =
      (ClausiusFromEntropyArea.unruh_temperature hbar c_light k_B P *
       ClausiusFromEntropyArea.entropy_increment entropy_per_bit support)%R ->
    ClausiusFromEntropyArea.heat_flux_from_split s P =
      (ClausiusFromEntropyArea.unruh_temperature hbar c_light k_B P *
       ClausiusFromEntropyArea.entropy_increment entropy_per_bit support)%R.
Proof.
  intros hbar c_light k_B entropy_per_bit nc P support s Hfocus Hnull.
  unfold ClausiusFromEntropyArea.heat_flux_from_split.
  unfold null_energy_flux in Hnull.
  unfold raychaudhuri_focusing in Hfocus.
  unfold raychaudhuri_focusing in Hnull.
  rewrite Hfocus in Hnull.
  replace (INR s.(vm_mu) * ClausiusFromEntropyArea.horizon_area_measure P * 1)%R
    with (INR s.(vm_mu) * ClausiusFromEntropyArea.horizon_area_measure P)%R in Hnull
    by ring.
  exact Hnull.
Qed.

Theorem raychaudhuri_delta_flux_implies_clausius_delta_link :
  forall (hbar c_light k_B entropy_per_bit : R)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support_pre support_post : LocalMorphismSemantics.joint_support)
         (s_pre s_post : VMState),
    null_energy_flux_delta calibrated_null_congruence s_pre s_post P =
      (ClausiusFromEntropyArea.unruh_temperature hbar c_light k_B P *
       ClausiusFromEntropyArea.entropy_increment_delta
         entropy_per_bit support_pre support_post)%R ->
    ClausiusFromEntropyArea.heat_flux_delta_from_split s_pre s_post P =
      (ClausiusFromEntropyArea.unruh_temperature hbar c_light k_B P *
       ClausiusFromEntropyArea.entropy_increment_delta
         entropy_per_bit support_pre support_post)%R.
Proof.
  intros hbar c_light k_B entropy_per_bit P support_pre support_post s_pre s_post
         Hnull_delta.
  unfold null_energy_flux_delta in Hnull_delta.
  rewrite calibrated_focusing_unit in Hnull_delta.
  replace
    (ClausiusFromEntropyArea.vm_mu_delta s_pre s_post *
     ClausiusFromEntropyArea.horizon_area_measure P * 1)%R
    with
    (ClausiusFromEntropyArea.heat_flux_delta_from_split s_pre s_post P)
    in Hnull_delta.
  - exact Hnull_delta.
  - unfold ClausiusFromEntropyArea.heat_flux_delta_from_split.
    ring.
Qed.

End RaychaudhuriFlux.
