(** * Jacobson Bridge Components

    WHY THIS FILE EXISTS:
    Replace a monolithic Jacobson bridge assumption with explicit components:
    Clausius-type thermodynamic relation and Raychaudhuri-to-Einstein link.

    This keeps the remaining gap named and typed in physically meaningful
    sub-hypotheses that can be discharged progressively.
*)

From Coq Require Import Reals.

From Kernel Require Import VMState.
From Kernel Require Import MuCostModel.
From Kernel Require Import LocalMorphismSemantics.
From Kernel Require Import EntanglementEntropy.

Section JacobsonComponents.

Variable SpacetimeState : Type.
Variable EinsteinTarget : SpacetimeState -> Prop.
Variable LocalHorizon : SpacetimeState -> Type.

Theorem jacobson_components_imply_target :
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
    entanglement_entropy_vn_bits support <=
      boundary_size_1d
        (LocalMorphismSemantics.split_left P)
        (LocalMorphismSemantics.split_right P) ->
    EinsteinTarget st.
Proof.
  intros clausius_component raychaudhuri_component P support st H Hbound.
  destruct (clausius_component P support st H Hbound) as [dQ [dS [T [HT HdQ]]]].
  eapply raychaudhuri_component; eauto.
Qed.

End JacobsonComponents.
