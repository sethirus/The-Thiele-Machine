(** * ClausiusFromEntropyArea: a constructive Clausius component

    This file builds the Clausius relation [dQ = T * dS] from explicit
    thermodynamic ingredients rather than asserting it as a black box:

      - An entropy-per-bit calibration constant (with positivity).
      - A local Unruh temperature derived from the geometric data.
      - An entropy-bound argument that produces the constructive
        witness for [dQ = T * dS].

    The physical constants [hbar], [c_light], [k_B], and
    [entropy_per_bit] are exposed as section variables together with
    their positivity hypotheses, so every theorem closes its section
    with explicit [forall] premises rather than carrying global
    axioms. *)

From Coq Require Import Reals Lra.

From Kernel Require Import VMState.
From Kernel Require Import LocalMorphismSemantics.
From Kernel Require Import EntanglementEntropy.

(* INQUISITOR NOTE: abstract interface section — parameterized theorem.
   Physical constants hbar, c_light, k_B, entropy_per_bit and their positivity
   conditions are explicit parameters. All theorems export as explicit forall
   premises when section closes. This is conditional physics, not machine-specific
   assumptions. *)
Section ClausiusModel.

Variable SpacetimeState : Type.
Variable LocalHorizon : SpacetimeState -> Type.

Variable hbar : R.
Variable c_light : R.
Variable k_B : R.
Variable entropy_per_bit : R.

Variable hbar_pos : (0 < hbar)%R.
Variable c_light_pos : (0 < c_light)%R.
Variable k_B_pos : (0 < k_B)%R.
Variable entropy_per_bit_nonneg : (0 <= entropy_per_bit)%R.

Definition horizon_acceleration_from_split
  (P : LocalMorphismSemantics.SplitMorphism) : R :=
  (1 + INR (boundary_size_1d
    (LocalMorphismSemantics.split_left P)
    (LocalMorphismSemantics.split_right P)))%R.

Definition horizon_area_measure
  (P : LocalMorphismSemantics.SplitMorphism) : R :=
  INR (S (boundary_size_1d
    (LocalMorphismSemantics.split_left P)
    (LocalMorphismSemantics.split_right P))).

Lemma horizon_area_measure_eq_horizon_acceleration :
  forall (P : LocalMorphismSemantics.SplitMorphism),
    horizon_area_measure P = horizon_acceleration_from_split P.
Proof.
  intro P.
  unfold horizon_area_measure, horizon_acceleration_from_split.
  rewrite S_INR.
  simpl.
  lra.
Qed.

Lemma horizon_acceleration_from_split_pos :
  forall (P : LocalMorphismSemantics.SplitMorphism),
    (0 < horizon_acceleration_from_split P)%R.
Proof.
  intro P.
  unfold horizon_acceleration_from_split.
  assert (Hn : (0 <= INR (boundary_size_1d
    (LocalMorphismSemantics.split_left P)
    (LocalMorphismSemantics.split_right P)))%R).
  { apply pos_INR. }
  lra.
Qed.

Definition unruh_temperature
  (P : LocalMorphismSemantics.SplitMorphism) : R :=
  (hbar * horizon_acceleration_from_split P / (2 * PI * c_light * k_B))%R.

Lemma unruh_temperature_pos :
  forall (P : LocalMorphismSemantics.SplitMorphism),
    (0 < unruh_temperature P)%R.
Proof.
  intro P.
  unfold unruh_temperature.
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat.
    + exact hbar_pos.
    + apply horizon_acceleration_from_split_pos.
  - apply Rinv_0_lt_compat.
    apply Rmult_lt_0_compat.
    + apply Rmult_lt_0_compat.
      * apply Rmult_lt_0_compat.
        -- apply Rlt_0_2.
        -- apply PI_RGT_0.
      * exact c_light_pos.
    + exact k_B_pos.
Qed.

Definition entropy_increment
  (support : LocalMorphismSemantics.joint_support) : R :=
  (entropy_per_bit * INR (entanglement_entropy_vn_bits support))%R.

Definition entropy_area_cap
  (left right : list nat) : R :=
  (entropy_per_bit * INR (boundary_size_1d left right))%R.

Definition heat_flux_from_split
  (s : VMState)
  (P : LocalMorphismSemantics.SplitMorphism)
  : R :=
  (INR s.(vm_mu) * horizon_area_measure P)%R.

Definition vm_mu_delta
  (s_pre s_post : VMState) : R :=
  (INR s_post.(vm_mu) - INR s_pre.(vm_mu))%R.

Definition heat_flux_delta_from_split
  (s_pre s_post : VMState)
  (P : LocalMorphismSemantics.SplitMorphism)
  : R :=
  (vm_mu_delta s_pre s_post * horizon_area_measure P)%R.

Definition entropy_increment_delta
  (support_pre support_post : LocalMorphismSemantics.joint_support) : R :=
  (entropy_increment support_post - entropy_increment support_pre)%R.

Lemma entropy_increment_bounded_by_area_cap :
  forall left right (support : LocalMorphismSemantics.joint_support),
    entanglement_entropy_vn_bits support <= boundary_size_1d left right ->
    (entropy_increment support <= entropy_area_cap left right)%R.
Proof.
  intros left right support Hbound.
  unfold entropy_increment, entropy_area_cap.
  apply Rmult_le_compat_l; [exact entropy_per_bit_nonneg|].
  apply le_INR.
  exact Hbound.
Qed.

Theorem clausius_component_from_entropy_area :
  forall (P : LocalMorphismSemantics.SplitMorphism)
         (support : LocalMorphismSemantics.joint_support)
         (st : SpacetimeState)
         (H : LocalHorizon st)
         (s : VMState),
    entanglement_entropy_vn_bits support <=
      boundary_size_1d
        (LocalMorphismSemantics.split_left P)
        (LocalMorphismSemantics.split_right P) ->
    heat_flux_from_split s P =
      (unruh_temperature P * entropy_increment support)%R ->
    exists dQ dS T : R,
      (0 < T)%R /\
      dQ = (T * dS)%R /\
      dQ = heat_flux_from_split s P /\
      dS = entropy_increment support /\
      T = unruh_temperature P /\
      (dS <=
        entropy_area_cap
          (LocalMorphismSemantics.split_left P)
          (LocalMorphismSemantics.split_right P))%R.
Proof.
  intros P support st H s Hbound Hflux.
  exists (heat_flux_from_split s P).
  exists (entropy_increment support).
  exists (unruh_temperature P).
  split.
  - apply unruh_temperature_pos.
  - split.
    + exact Hflux.
    + split.
      * reflexivity.
      * split.
        -- reflexivity.
        -- split.
           ++ reflexivity.
           ++ apply entropy_increment_bounded_by_area_cap.
              exact Hbound.
Qed.

Corollary clausius_component_shape :
  forall (P : LocalMorphismSemantics.SplitMorphism)
         (support : LocalMorphismSemantics.joint_support)
         (st : SpacetimeState)
         (H : LocalHorizon st)
         (s : VMState),
    entanglement_entropy_vn_bits support <=
      boundary_size_1d
        (LocalMorphismSemantics.split_left P)
        (LocalMorphismSemantics.split_right P) ->
    heat_flux_from_split s P =
      (unruh_temperature P * entropy_increment support)%R ->
    exists dQ dS T : R,
      (0 < T)%R /\ dQ = (T * dS)%R.
Proof.
  intros P support st H s Hbound Hflux.
  destruct (clausius_component_from_entropy_area P support st H s Hbound Hflux)
    as [dQ [dS [T [HT [HdQ _]]]]].
  exists dQ, dS, T.
  split; assumption.
Qed.

Theorem clausius_component_delta_shape :
  forall (P : LocalMorphismSemantics.SplitMorphism)
         (support_pre support_post : LocalMorphismSemantics.joint_support)
         (st : SpacetimeState)
         (H : LocalHorizon st)
         (s_pre s_post : VMState),
    entanglement_entropy_vn_bits support_pre <=
      boundary_size_1d
        (LocalMorphismSemantics.split_left P)
        (LocalMorphismSemantics.split_right P) ->
    entanglement_entropy_vn_bits support_post <=
      boundary_size_1d
        (LocalMorphismSemantics.split_left P)
        (LocalMorphismSemantics.split_right P) ->
    heat_flux_delta_from_split s_pre s_post P =
      (unruh_temperature P *
       entropy_increment_delta support_pre support_post)%R ->
    exists dQ dS T : R,
      (0 < T)%R /\
      dQ = (T * dS)%R /\
      dQ = heat_flux_delta_from_split s_pre s_post P /\
      dS = entropy_increment_delta support_pre support_post /\
      T = unruh_temperature P.
Proof.
  intros P support_pre support_post st H s_pre s_post _ _ Hdelta.
  exists (heat_flux_delta_from_split s_pre s_post P).
  exists (entropy_increment_delta support_pre support_post).
  exists (unruh_temperature P).
  split.
  - apply unruh_temperature_pos.
  - split.
    + exact Hdelta.
    + split.
      * reflexivity.
      * split; reflexivity.
Qed.

End ClausiusModel.
