(** Thermodynamic-to-Einstein Bridge
    (* SCOPE NOTE: MISSING einstein_equation IS INTENTIONAL *)

    Connect the entropy-locality bridge (nearest-neighbor split morphisms
    imply boundary entropy scaling) to an explicit Jacobson-style bridge
    hypothesis that maps entropy-area control to Einstein dynamics. The
    generic corridor theorems take that hypothesis as a premise; this file
    does not derive Jacobson's argument.

    Two concrete instances close the file. The discrete instance
    ([thermodynamic_locality_toward_discrete_einstein_emergence]) concludes
    the Gauss-Bonnet delta identity, which holds from the two triangulation
    premises alone; its Clausius and flux data are carried. The 4D instance
    ([einstein_4d_successor_diag_from_positive_mass]) gives the diagonal
    Einstein tensor on the successor chain from positive structural mass.
    The premise named [clausius_structural_mass_axiom_statement] is
    equivalent to positive structural mass
    ([clausius_structural_mass_axiom_statement_iff]), so no Clausius data
    reaches that theorem either. *)

From Coq Require Import List Arith.PeanoNat Reals ZArith Lia.
Import ListNotations.

From Kernel Require Import VMState.
From Kernel Require Import LocalMorphismSemantics.
From Kernel Require Import EntanglementEntropy.
From Kernel Require Import ClausiusFromEntropyArea.
From Kernel Require Import RaychaudhuriFluxBridge.
From Kernel Require Import JacobsonBridgeComponents.
From Kernel Require Import DiscreteTopology DiscreteGaussBonnet.
From Kernel Require Import EinsteinEmergence.
From Kernel Require Import MuGravity.
From Kernel Require Import EinsteinEquations4D.
From Kernel Require Import CurvedTensorPipeline.
From Kernel Require Import DiscreteRaychaudhuri.

Definition discrete_einstein_emergence_target
  (st_pair : VMState * VMState) : Prop :=
  well_formed_triangulated (vm_graph (fst st_pair)) ->
  well_formed_triangulated (vm_graph (snd st_pair)) ->
  (total_curvature (vm_graph (snd st_pair)) -
   total_curvature (vm_graph (fst st_pair)))%R =
    (einstein_coupling_constant *
     IZR (euler_characteristic (vm_graph (snd st_pair)) -
          euler_characteristic (vm_graph (fst st_pair))))%R.

(* DEPRECATED: vacuous 2D proof; the Clausius params (dQ, dS, T) are unused
   because 2D Gauss-Bonnet does not need them.  The lemma accepts them only for
   interface compatibility with the generic corridor theorem
   (thermodynamic_locality_toward_einstein_with_clausius_model), but the 2D
   proof path calls einstein_emerges directly and ignores all thermodynamic data. *)
Lemma discrete_einstein_emergence_component :
  forall (st_pair : VMState * VMState)
         (_ : unit)
         (dQ dS T : R),
    (0 < T)%R ->
    dQ = (T * dS)%R ->
    discrete_einstein_emergence_target st_pair.
Proof.
  intros [s_pre s_post] _ dQ dS T _ _ Hwf_pre Hwf_post.
  exact (einstein_emerges s_pre s_post Hwf_pre Hwf_post).
Qed.

(* SCOPE NOTE: abstract interface section, parameterized theorem.
   EinsteinTarget is an abstract predicate. All theorems export as explicit
   forall premises when section closes. *)
Section TowardEinstein.

Variable SpacetimeState : Type.
Variable EinsteinTarget : SpacetimeState -> Prop.
Variable LocalHorizon : SpacetimeState -> Type.

Theorem thermodynamic_locality_toward_einstein :
  forall (clausius_component :
            forall (P : LocalMorphismSemantics.SplitMorphism)
                   (support : LocalMorphismSemantics.joint_support)
                   (st : SpacetimeState)
                   (H : LocalHorizon st),
              entanglement_entropy_vn_bits support <=
                boundary_size_1d
                  (LocalMorphismSemantics.split_left P)
                  (LocalMorphismSemantics.split_right P) ->
              exists dQ dS T : R,
                (0 < T)%R /\ dQ = (T * dS)%R)
         (raychaudhuri_component :
            forall (st : SpacetimeState)
                   (H : LocalHorizon st)
                   (dQ dS T : R),
              (0 < T)%R ->
              dQ = (T * dS)%R ->
              EinsteinTarget st)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support : LocalMorphismSemantics.joint_support)
         (st : SpacetimeState)
         (H : LocalHorizon st),
    LocalMorphismSemantics.is_nearest_neighbor P ->
    In support (LocalMorphismSemantics.morphism_support_semantics P) ->
    EinsteinTarget st.
Proof.
  intros clausius_component raychaudhuri_component P support st H Hnn Hin.
  eapply (@jacobson_components_imply_target
            SpacetimeState
            EinsteinTarget
            LocalHorizon
            clausius_component
            raychaudhuri_component
            P support st H).
  apply local_morphism_entropy_area_law_bits; assumption.
Qed.

Theorem thermodynamic_locality_toward_einstein_with_clausius_model :
  forall (hbar c_light k_B entropy_per_bit : R)
         (hbar_pos : (0 < hbar)%R)
         (c_light_pos : (0 < c_light)%R)
         (k_B_pos : (0 < k_B)%R)
         (raychaudhuri_component :
            forall (st : SpacetimeState)
                   (H : LocalHorizon st)
                   (dQ dS T : R),
              (0 < T)%R ->
              dQ = (T * dS)%R ->
              EinsteinTarget st)
         (s_pre s_post : VMState)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support_pre support_post : LocalMorphismSemantics.joint_support)
         (st : SpacetimeState)
         (H : LocalHorizon st),
    LocalMorphismSemantics.is_nearest_neighbor P ->
    In support_pre (LocalMorphismSemantics.morphism_support_semantics P) ->
    In support_post (LocalMorphismSemantics.morphism_support_semantics P) ->
    RaychaudhuriFluxBridge.null_energy_flux_delta
      RaychaudhuriFluxBridge.calibrated_null_congruence s_pre s_post P =
      (ClausiusFromEntropyArea.unruh_temperature
         hbar c_light k_B
        P *
       ClausiusFromEntropyArea.entropy_increment_delta
         entropy_per_bit
         support_pre support_post)%R ->
    EinsteinTarget st.
Proof.
  intros hbar c_light k_B entropy_per_bit Hh Hc Hk Hray
          s_pre s_post P support_pre support_post st H Hnn Hin_pre Hin_post
          Hray_transition.
  assert (Hflux_delta : ClausiusFromEntropyArea.heat_flux_delta_from_split s_pre s_post P =
      (ClausiusFromEntropyArea.unruh_temperature hbar c_light k_B P *
       ClausiusFromEntropyArea.entropy_increment_delta
         entropy_per_bit support_pre support_post)%R).
  { eapply RaychaudhuriFluxBridge.raychaudhuri_delta_flux_implies_clausius_delta_link; eauto. }
  assert (Hbound_pre :
    entanglement_entropy_vn_bits support_pre <=
      boundary_size_1d
        (LocalMorphismSemantics.split_left P)
        (LocalMorphismSemantics.split_right P)).
  { apply local_morphism_entropy_area_law_bits; assumption. }
  assert (Hbound_post :
    entanglement_entropy_vn_bits support_post <=
      boundary_size_1d
        (LocalMorphismSemantics.split_left P)
        (LocalMorphismSemantics.split_right P)).
  { apply local_morphism_entropy_area_law_bits; assumption. }
  destruct (ClausiusFromEntropyArea.clausius_component_delta_shape
    SpacetimeState LocalHorizon hbar c_light k_B entropy_per_bit
    Hh Hc Hk
    P support_pre support_post st H s_pre s_post
    Hbound_pre Hbound_post Hflux_delta) as [dQ [dS [T [HT [HdQ _]]]]].
  eapply Hray; eauto.
Qed.

End TowardEinstein.

(** The generic corridor theorem instantiated at the discrete target. The
    instance runs through [discrete_einstein_emergence_component], which
    ignores the Clausius data, so the conclusion follows from the two
    triangulation premises; the locality, support and null-flux premises are
    carried. *)
Theorem thermodynamic_locality_toward_discrete_einstein_emergence :
  forall (hbar c_light k_B entropy_per_bit : R)
         (hbar_pos : (0 < hbar)%R)
         (c_light_pos : (0 < c_light)%R)
         (k_B_pos : (0 < k_B)%R)
         (s_pre s_post : VMState)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support_pre support_post : LocalMorphismSemantics.joint_support),
    LocalMorphismSemantics.is_nearest_neighbor P ->
    In support_pre (LocalMorphismSemantics.morphism_support_semantics P) ->
    In support_post (LocalMorphismSemantics.morphism_support_semantics P) ->
    RaychaudhuriFluxBridge.null_energy_flux_delta
      RaychaudhuriFluxBridge.calibrated_null_congruence s_pre s_post P =
      (ClausiusFromEntropyArea.unruh_temperature hbar c_light k_B P *
       ClausiusFromEntropyArea.entropy_increment_delta
         entropy_per_bit support_pre support_post)%R ->
    well_formed_triangulated (vm_graph s_pre) ->
    well_formed_triangulated (vm_graph s_post) ->
    (total_curvature (vm_graph s_post) - total_curvature (vm_graph s_pre))%R =
      (einstein_coupling_constant *
       IZR (euler_characteristic (vm_graph s_post) -
            euler_characteristic (vm_graph s_pre)))%R.
Proof.
  intros hbar c_light k_B entropy_per_bit Hh Hc Hk
         s_pre s_post P support_pre support_post
         Hnn Hin_pre Hin_post Hray_transition Hwf_pre Hwf_post.
  pose proof
    (@thermodynamic_locality_toward_einstein_with_clausius_model
       (VMState * VMState)
       discrete_einstein_emergence_target
       (fun _ => unit)
       hbar c_light k_B entropy_per_bit
       Hh Hc Hk
       discrete_einstein_emergence_component
       s_pre s_post P support_pre support_post (s_pre, s_post) tt
       Hnn Hin_pre Hin_post Hray_transition) as Htarget.
  exact (Htarget Hwf_pre Hwf_post).
Qed.

(** [clausius_structural_mass_axiom_statement]: the premise "every
    positive-temperature Clausius pair at [v] gives positive structural mass
    at [v]". Its conclusion does not mention the pair, and the pair
    (dQ, dS, T) = (0, 0, 1) always exists, so the premise says exactly that
    the structural mass at [v] is positive
    ([clausius_structural_mass_axiom_statement_iff]). *)
Definition clausius_structural_mass_axiom_statement (s : VMState) (v : ModuleID) : Prop :=
  forall dQ dS T : R, (0 < T)%R -> dQ = (T * dS)%R -> (module_structural_mass s v > 0)%nat.

Lemma clausius_structural_mass_axiom_statement_iff :
  forall (s : VMState) (v : ModuleID),
    clausius_structural_mass_axiom_statement s v <->
    (module_structural_mass s v > 0)%nat.
Proof.
  intros s v. unfold clausius_structural_mass_axiom_statement. split.
  - intro H. apply (H 0%R 0%R 1%R).
    + apply Rlt_0_1.
    + ring.
  - intros Hm dQ dS T _ _. exact Hm.
Qed.

(** [einstein_4d_successor_diag_from_positive_mass]: on the natural-number
    successor chain, at a module with positive structural mass, each diagonal
    component of the 4D Einstein tensor equals 8 PI G times the mass factor
    times the mass stress-energy. Positive mass is needed only to divide by
    the mass. *)
Theorem einstein_4d_successor_diag_from_positive_mass :
  forall (s : VMState) (n : nat) (v : ModuleID) (d : nat),
    (d < 4)%nat ->
    (module_structural_mass s v > 0)%nat ->
    (local_einstein_tensor_4d s (nat_chain_sc n) d d v =
      (8 * PI * EinsteinEquations4D.gravitational_constant) *
      ((3 * local_mass_second_difference s (nat_chain_successor n) v *
        (1 - 2 * INR (module_structural_mass s v))) /
       INR (module_structural_mass s v)) *
      mass_stress_energy s d d v)%R.
Proof.
  intros s n v d Hd Hmass.
  rewrite EinsteinEquations4D.gravitational_coupling_unit_convention, Rmult_1_l.
  rewrite (EinsteinEquations4D.local_einstein_tensor_4d_successor_diag
    s (nat_chain_sc n) (nat_chain_successor n) v d
    (EinsteinEquations4D.nat_chain_successor_derivative_semantics s n) Hd).
  unfold mass_stress_energy. rewrite Nat.eqb_refl. field.
  apply not_0_INR. lia.
Qed.
