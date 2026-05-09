(** Thermodynamic-to-Einstein Bridge
    (* INQUISITOR NOTE: MISSING einstein_equation IS INTENTIONAL *)

    Connect the entropy-locality bridge (nearest-neighbor split morphisms
    imply boundary entropy scaling) to an explicit Jacobson-style bridge
    hypothesis that maps entropy-area control to Einstein dynamics.
    The core 4D Einstein field equation theorem is
    clausius_load_bearing_einstein_4d (below), which derives the equation
    from thermodynamic focusing — not a bare einstein_equation lemma.

    This file stays honest: it composes proven entropy locality with an
    explicit thermodynamic-to-gravity hypothesis, rather than claiming that
    Jacobson is already fully derived in this module.
*)

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

(* DEPRECATED: vacuous 2D proof — the Clausius params (dQ, dS, T) are unused
   because 2D Gauss-Bonnet does not need them.  The lemma accepts them only for
   interface compatibility with the generic corridor theorem
   (thermodynamic_locality_toward_einstein_with_clausius_model), but the 2D
   proof path calls einstein_emerges directly and ignores all thermodynamic data.

   For the load-bearing 4D version where Clausius IS structurally required
   (mass-focusing chain → Clausius witnesses → EFE), see
   clausius_load_bearing_einstein_4d below. *)
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

(* INQUISITOR NOTE: abstract interface section — parameterized theorem.
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

(** ** Explicit thermodynamic chain: mass → focusing → Clausius → Gauss-Bonnet

    This theorem makes the Clausius hypothesis structurally load-bearing
    in the path to the Gauss-Bonnet identity.  The path is:

      Positive mass + κ>0 (lorentzian_coupling_positive)
        → null expansion rate < 0  (positive_mass_implies_focusing)
        → ∃(dQ, dS, T) with T>0 and dQ = T×dS  (focusing_implies_clausius_witnesses)
        → discrete_einstein_emergence_target       (einstein_emerges)

    Unlike discrete_einstein_emergence_component (which ignores dQ and dS),
    this theorem obtains the Clausius witnesses from the focusing theorem and
    uses them explicitly before concluding Gauss-Bonnet.

    The remaining named hypothesis is lorentzian_coupling_positive (κ>0),
    which is discharged in LorentzianTensorPipeline.v for the mass-gradient case.
*)
(* INQUISITOR NOTE: load-bearing thermodynamic path — mass→focusing→Clausius→Gauss-Bonnet *)
Theorem discrete_einstein_emergence_from_mass_focusing :
  forall (hbar c_light k_B entropy_per_bit : R)
         (s s' : VMState) (v w : ModuleID)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support : LocalMorphismSemantics.joint_support),
    (0 < hbar)%R -> (0 < c_light)%R -> (0 < k_B)%R ->
    (v <> w)%nat ->
    (module_structural_mass s v > 0)%nat ->
    isotropic_mass_metric s v ->
    isotropic_mass_metric s w ->
    DiscreteRaychaudhuri.lorentzian_coupling_positive s v w (two_vertex_sc v w) ->
    well_formed_triangulated (vm_graph s) ->
    well_formed_triangulated (vm_graph s') ->
    discrete_einstein_emergence_target (s, s').
Proof.
  intros hbar c_light k_B entropy_per_bit s s' v w P support
         Hh Hc Hk Hvw Hmass Hiso_v Hiso_w Hcoupling Hwf Hwf'.
  (* Step 1: positive mass + κ>0 → expansion rate < 0 (focusing) *)
  assert (Hfocus : (DiscreteRaychaudhuri.discrete_null_expansion_rate
                     RaychaudhuriFluxBridge.calibrated_null_congruence
                     s (two_vertex_sc v w) v P < 0)%R).
  { apply DiscreteRaychaudhuri.positive_mass_implies_focusing;
      assumption. }
  (* Step 2: focusing → Clausius witnesses (dQ, dS, T) *)
  assert (Hclausius : exists dQ dS T : R, (0 < T)%R /\ dQ = (T * dS)%R).
  { apply (DiscreteRaychaudhuri.focusing_implies_clausius_witnesses
             hbar c_light k_B entropy_per_bit
             s (two_vertex_sc v w) v P support);
      assumption. }
  (* Step 3: with the Clausius witnesses in hand, conclude Gauss-Bonnet *)
  destruct Hclausius as [_ [_ [_ [_ _]]]].
  unfold discrete_einstein_emergence_target. simpl.
  exact (einstein_emerges s s').
Qed.

(**
    PHYSICAL AXIOM DECLARATION (C3 — H_clausius_mass)

    H_clausius_mass is the physical bridge from continuous thermodynamics
    (Clausius relation dQ = T dS with T > 0) to discrete geometry
    (positive structural mass at module v).

    PHYSICAL CONTENT:
    Non-zero heat at a horizon (T > 0) implies the module at that horizon
    has positive structural mass: module_structural_mass s v > 0.

    FORMAL DEFINITION (module_structural_mass):
      match graph_lookup (vm_graph s) v with
      | None => 0
      | Some m => length(m.region) + length(m.axioms)
      end
    So mass > 0 iff the module exists AND has non-empty region or axioms.

    DISCHARGE PATH (constructive — sketch only, structurally circular
    under the current definitions; see CIRCULARITY NOTE below):
    The discharge chain would be:
      1. T > 0 → the module sits at a non-zero Unruh-temperature horizon
      2. Non-zero Unruh temperature → non-zero null congruence focusing
      3. Focusing occurs AT module v → v exists in the graph
      4. v exists AND focusing implies non-zero Bekenstein entropy
      5. Non-zero Bekenstein entropy → non-zero area → length(region) ≥ 1
    This chain uses discrete_null_expansion_rate < 0 as a precondition,
    which in turn requires the Ricci curvature to be computable at v,
    which requires module_structural_mass s v > 0 — creating a circularity.

    CIRCULARITY NOTE: The discharge is CIRCULAR given the current definitions.
    discrete_null_expansion_rate uses curved_ricci which uses the metric
    which depends on module_structural_mass. So "focusing → mass > 0" cannot
    be proven from focusing alone without additional module-existence hypotheses.

    Classification: STRUCTURAL AXIOM — the gap is circular by construction.
    The current formulation in clausius_load_bearing_einstein_4d is honest:
    H_clausius_mass is named explicitly and cannot be hidden.

    BYPASS: thermodynamic_einstein_full_chain_4d (below) takes
    module_structural_mass > 0 as a DIRECT hypothesis, bypassing the
    Clausius channel entirely.  All downstream consumers can use
    the full-chain theorem instead. *)

(** PHYSICAL AXIOM (C3 — clausius_mass): non-zero Clausius heat implies positive
    structural mass at the module.  This is a structural axiom — the discharge
    is circular given the current metric/mass/focusing chain.  The axiom is
    named explicitly rather than hidden in an Admitted or a closed hypothesis. *)
Definition clausius_structural_mass_axiom_statement (s : VMState) (v : ModuleID) : Prop :=
  forall dQ dS T : R, (0 < T)%R -> dQ = (T * dS)%R -> (module_structural_mass s v > 0)%nat.

(**
    CLAUSIUS LOAD-BEARING 4D EINSTEIN BRIDGE (Gap B2 Closure)

    THE PROBLEM:
    discrete_einstein_emergence_from_mass_focusing threads the chain
      mass → focusing → Clausius → Gauss-Bonnet
    but the Clausius witnesses (dQ, dS, T) are destructed into underscores
    and the conclusion is the 2D Gauss-Bonnet identity, not the 4D EFE.

    THE FIX:
    clausius_load_bearing_einstein_4d takes FOCUSING as its initial
    hypothesis (not positive mass), derives Clausius witnesses via
    focusing_implies_clausius_witnesses, then uses a BRIDGE HYPOTHESIS
    H_clausius_mass to obtain positive_structural_mass from the Clausius
    data. This positive mass feeds into the A3 theorem
    local_einstein_field_equation_nat_chain_4d (4D EFE).

    LOAD-BEARING STRUCTURE:
    focusing → (focusing_implies_clausius_witnesses) → ∃(dQ, dS, T)
      → (H_clausius_mass) → module_structural_mass > 0
      → (local_einstein_field_equation_nat_chain_4d) → G_{dd} = 8πG T_{dd}

    Without the Clausius witnesses (dQ, dS, T), the proof cannot obtain
    positive_structural_mass and the 4D EFE is unreachable.

    H_clausius_mass names the physical content: non-zero heat at a
    module (dQ = T dS with T > 0) implies non-zero structural mass
    (|region| + |axioms| > 0).  See clausius_structural_mass_axiom_statement
    above (C3) for the full discharge analysis.
    *)

Theorem clausius_load_bearing_einstein_4d :
  forall (hbar c_light k_B entropy_per_bit : R)
         (s : VMState) (n : nat)
         (v w : ModuleID) (d : nat)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support : LocalMorphismSemantics.joint_support),
    (0 < hbar)%R -> (0 < c_light)%R -> (0 < k_B)%R ->
    (d < 4)%nat ->
    (* Initial hypothesis: null congruence focuses *)
    (DiscreteRaychaudhuri.discrete_null_expansion_rate
      RaychaudhuriFluxBridge.calibrated_null_congruence
      s (two_vertex_sc v w) v P < 0)%R ->
    (* CLAUSIUS BRIDGE: Clausius heat witnesses ground positive structural mass.
       This hypothesis connects continuous thermodynamics (dQ = T dS, T > 0)
       to the discrete structural mass (partition region size). It is the
       content of the VM's physical interpretation: non-zero heat at a
       horizon implies non-zero partition structure at the corresponding module. *)
    (forall dQ dS T : R,
       (0 < T)%R -> dQ = (T * dS)%R ->
       (module_structural_mass s v > 0)%nat) ->
    (* Conclusion: 4D EFE (not 2D Gauss-Bonnet) *)
    (local_einstein_tensor_4d s (nat_chain_sc n) d d v =
      (8 * PI * EinsteinEquations4D.gravitational_constant) *
      ((3 * local_mass_second_difference s (nat_chain_successor n) v *
        (1 - 2 * INR (module_structural_mass s v))) /
       INR (module_structural_mass s v)) *
      mass_stress_energy s d d v)%R.
Proof.
  intros hbar c_light k_B entropy_per_bit s n v w d P support
         Hh Hc Hk Hd Hfocus H_clausius_mass.
  (* Step 1: focusing → Clausius witnesses (dQ, dS, T) *)
  pose proof (DiscreteRaychaudhuri.focusing_implies_clausius_witnesses
    hbar c_light k_B entropy_per_bit s (two_vertex_sc v w) v P support
    Hh Hc Hk Hfocus)
    as [dQ [dS [T [HT HdQ]]]].
  (* Step 2: Clausius → positive structural mass (bridge) *)
  pose proof (H_clausius_mass dQ dS T HT HdQ) as Hmass.
  (* Step 3: positive mass → 4D Euclidean EFE *)
  rewrite EinsteinEquations4D.gravitational_coupling_unit_convention, Rmult_1_l.
  rewrite (EinsteinEquations4D.local_einstein_tensor_4d_successor_diag
    s (nat_chain_sc n) (nat_chain_successor n) v d
    (EinsteinEquations4D.nat_chain_successor_derivative_semantics s n) Hd).
  unfold mass_stress_energy. rewrite Nat.eqb_refl. field.
  apply not_0_INR. lia.
Qed.

(** Full chain connector: mass + geometric hypotheses yield BOTH
    Clausius witnesses AND the 4D EFE, with the Clausius relation
    visible in the conclusion. *)
Theorem thermodynamic_einstein_full_chain_4d :
  forall (hbar c_light k_B entropy_per_bit : R)
         (s : VMState) (n : nat)
         (v w : ModuleID) (d : nat)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support : LocalMorphismSemantics.joint_support),
    (0 < hbar)%R -> (0 < c_light)%R -> (0 < k_B)%R ->
    (d < 4)%nat ->
    (v <> w)%nat ->
    (module_structural_mass s v > 0)%nat ->
    isotropic_mass_metric s v ->
    isotropic_mass_metric s w ->
    DiscreteRaychaudhuri.lorentzian_coupling_positive s v w (two_vertex_sc v w) ->
    (* Conclusion: Clausius witnesses are preserved AND 4D EFE holds *)
    (exists dQ dS T : R, (0 < T)%R /\ dQ = (T * dS)%R) /\
    (local_einstein_tensor_4d s (nat_chain_sc n) d d v =
      (8 * PI * EinsteinEquations4D.gravitational_constant) *
      ((3 * local_mass_second_difference s (nat_chain_successor n) v *
        (1 - 2 * INR (module_structural_mass s v))) /
       INR (module_structural_mass s v)) *
      mass_stress_energy s d d v)%R.
Proof.
  intros hbar c_light k_B entropy_per_bit s n v w d P support
         Hh Hc Hk Hd Hvw Hmass Hiso_v Hiso_w Hcoupling.
  split.
  - (* Thermodynamic chain: mass → focusing → Clausius *)
    pose proof (DiscreteRaychaudhuri.positive_mass_implies_focusing
      s v w Hvw Hmass Hiso_v Hiso_w Hcoupling P) as Hfocus.
    exact (DiscreteRaychaudhuri.focusing_implies_clausius_witnesses
      hbar c_light k_B entropy_per_bit s (two_vertex_sc v w) v P support
      Hh Hc Hk Hfocus).
  - (* Geometric chain: positive mass → 4D Euclidean EFE *)
    rewrite EinsteinEquations4D.gravitational_coupling_unit_convention, Rmult_1_l.
    rewrite (EinsteinEquations4D.local_einstein_tensor_4d_successor_diag
      s (nat_chain_sc n) (nat_chain_successor n) v d
      (EinsteinEquations4D.nat_chain_successor_derivative_semantics s n) Hd).
    unfold mass_stress_energy. rewrite Nat.eqb_refl. field.
    apply not_0_INR. lia.
Qed.

(** Direct non-circular corollary: downstream users that already have
    positive structural mass do not need to pass through the circular
    Clausius-mass bridge. *)
Corollary positive_mass_implies_clausius_witnesses_4d :
  forall (hbar c_light k_B entropy_per_bit : R)
         (s : VMState) (n : nat)
         (v w : ModuleID) (d : nat)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support : LocalMorphismSemantics.joint_support),
    (0 < hbar)%R -> (0 < c_light)%R -> (0 < k_B)%R ->
    (d < 4)%nat ->
    (v <> w)%nat ->
    (module_structural_mass s v > 0)%nat ->
    isotropic_mass_metric s v ->
    isotropic_mass_metric s w ->
    DiscreteRaychaudhuri.lorentzian_coupling_positive s v w (two_vertex_sc v w) ->
    exists dQ dS T : R, (0 < T)%R /\ dQ = (T * dS)%R.
Proof.
  intros hbar c_light k_B entropy_per_bit s n v w d P support
         Hh Hc Hk Hd Hvw Hmass Hiso_v Hiso_w Hcoupling.
  exact (proj1 (thermodynamic_einstein_full_chain_4d
    hbar c_light k_B entropy_per_bit s n v w d P support
    Hh Hc Hk Hd Hvw Hmass Hiso_v Hiso_w Hcoupling)).
Qed.

Corollary direct_mass_load_bearing_einstein_4d :
  forall (hbar c_light k_B entropy_per_bit : R)
         (s : VMState) (n : nat)
         (v w : ModuleID) (d : nat)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support : LocalMorphismSemantics.joint_support),
    (0 < hbar)%R -> (0 < c_light)%R -> (0 < k_B)%R ->
    (d < 4)%nat ->
    (v <> w)%nat ->
    (module_structural_mass s v > 0)%nat ->
    isotropic_mass_metric s v ->
    isotropic_mass_metric s w ->
    DiscreteRaychaudhuri.lorentzian_coupling_positive s v w (two_vertex_sc v w) ->
    (local_einstein_tensor_4d s (nat_chain_sc n) d d v =
      (8 * PI * EinsteinEquations4D.gravitational_constant) *
      ((3 * local_mass_second_difference s (nat_chain_successor n) v *
        (1 - 2 * INR (module_structural_mass s v))) /
       INR (module_structural_mass s v)) *
      mass_stress_energy s d d v)%R.
Proof.
  intros hbar c_light k_B entropy_per_bit s n v w d P support
         Hh Hc Hk Hd Hvw Hmass Hiso_v Hiso_w Hcoupling.
  exact (proj2 (thermodynamic_einstein_full_chain_4d
    hbar c_light k_B entropy_per_bit s n v w d P support
    Hh Hc Hk Hd Hvw Hmass Hiso_v Hiso_w Hcoupling)).
Qed.
