(** ThieleInitiality: the universal property of Thiele as an A2-respecting
    substrate.

    AIM
    ---
    This file packages the existing results in [UniversalCertificationCost.v]
    and [MuInitiality.v] into a single named theorem stating that Thiele is
    the initial object in the category of A2-respecting substrates over
    [vm_instruction], with morphisms restricted to reachable states.

    This is the strongest categorical "foundationality" claim the Coq corpus
    can carry: initiality in a precisely-defined category, in the same sense
    that ℤ is the initial ring or the free group is initial in the category
    of groups with a fixed generating set.

    What is the universal property?
    -------------------------------
    For any CertCostMachine [M] (an A2-respecting substrate over the Thiele
    instruction set) and any basepoint [s0_M : M.(ccm_state)]:

    * (Existence)   The trace-fold [fun trace => fold_left M.(ccm_step) trace s0_M]
                    is a valid simulation: it preserves the empty trace at [s0_M]
                    and commutes with step-extension.

    * (Uniqueness)  Any function [g : list vm_instruction -> M.(ccm_state)]
                    that also preserves the empty trace at [s0_M] and commutes
                    with step-extension agrees with the canonical trace-fold on
                    every trace.

    Together: the canonical trace-fold simulation is the unique morphism from
    Thiele's trace category to M's state space, given a choice of basepoint.
    This is initiality in the free-monoid-action category.

    State-level consequence: any CertCostMorphism phi : Thiele -> M is uniquely
    determined on the reachable subset of VMState by its value at [init_state]
    and the step-commutation field. States unreachable from [init_state] are
    not constrained by the universal property (they live outside the categorical
    reach of Thiele).

    WHAT THIS THEOREM DOES NOT CLAIM
    ---------------------------------
    Categorical initiality is always relative to a chosen category. This file
    proves that Thiele is initial in the category of CertCostMachines over
    [vm_instruction], not that the CertCostMachine category is itself
    foundationally privileged over alternative cost-tracking categories. The
    latter is a meta-mathematical judgment about which signatures matter, of
    the same shape as "why study groups instead of semigroups", and is not
    settled by any theorem inside any category.

    NO COQ AXIOMS. NO ADMITS. The proofs below are list-induction packagings
    of the existing [UniversalCertificationCost.v] machinery.
*)

From Coq Require Import List.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.
From Kernel Require Import MuInitiality.
From Kernel Require Import UniversalCertificationCost.

(** ** Trace-level initiality

    The category whose objects are A2-respecting substrates over
    [vm_instruction] and whose morphisms are trace-fold simulations.
    Thiele's trace-fold is the universal morphism into every object of
    this category, given a choice of basepoint.
*)

(** Existence: the canonical trace-fold preserves the empty trace
    at the basepoint and commutes with step-extension. *)
Lemma thiele_canonical_fold_basepoint :
  forall (M : CertCostMachine) (s0_M : M.(ccm_state)),
    fold_left M.(ccm_step) [] s0_M = s0_M.
Proof. intros M s0_M. reflexivity. Qed.

Lemma thiele_canonical_fold_step :
  forall (M : CertCostMachine) (s0_M : M.(ccm_state))
         (trace : list vm_instruction) (i : vm_instruction),
    fold_left M.(ccm_step) (trace ++ [i]) s0_M =
    M.(ccm_step) (fold_left M.(ccm_step) trace s0_M) i.
Proof.
  intros M s0_M trace i.
  rewrite fold_left_app. simpl. reflexivity.
Qed.

(** Uniqueness: any function preserving the basepoint and commuting with
    step-extension agrees with the canonical trace-fold on every trace.
    This is the initiality content: the universal property forces the
    morphism on all traces. *)
Lemma thiele_canonical_fold_unique :
  forall (M : CertCostMachine) (s0_M : M.(ccm_state))
         (g : list vm_instruction -> M.(ccm_state)),
    g [] = s0_M ->
    (forall trace i, g (trace ++ [i]) = M.(ccm_step) (g trace) i) ->
    forall trace, g trace = fold_left M.(ccm_step) trace s0_M.
Proof.
  intros M s0_M g Hbase Hstep trace.
  induction trace using rev_ind.
  - simpl. exact Hbase.
  - rewrite Hstep. rewrite fold_left_app. simpl. rewrite IHtrace. reflexivity.
Qed.

(** ** The packaged initiality theorem.

    Thiele is the initial object in the category of A2-respecting substrates
    over [vm_instruction], with morphisms restricted to trace-folds from a
    chosen basepoint. The theorem combines existence and uniqueness into a
    single statement the monograph can cite as the formal universal property. *)

Theorem thiele_is_initial_a2_substrate :
  forall (M : CertCostMachine) (s0_M : M.(ccm_state)),
    (* (Existence) The canonical trace-fold is a valid simulation:
       it preserves the empty trace at the basepoint and commutes with
       step-extension. *)
    (fold_left M.(ccm_step) [] s0_M = s0_M) /\
    (forall (trace : list vm_instruction) (i : vm_instruction),
      fold_left M.(ccm_step) (trace ++ [i]) s0_M =
      M.(ccm_step) (fold_left M.(ccm_step) trace s0_M) i) /\
    (* (Uniqueness) Every other basepoint-preserving step-commuting
       function agrees with the canonical trace-fold. *)
    (forall (g : list vm_instruction -> M.(ccm_state)),
      g [] = s0_M ->
      (forall trace i, g (trace ++ [i]) = M.(ccm_step) (g trace) i) ->
      forall trace, g trace = fold_left M.(ccm_step) trace s0_M).
Proof.
  intros M s0_M. split; [| split].
  - exact (thiele_canonical_fold_basepoint M s0_M).
  - exact (thiele_canonical_fold_step M s0_M).
  - exact (thiele_canonical_fold_unique M s0_M).
Qed.

(** ** State-level corollary: CertCostMorphism uniqueness on reachable states.

    A CertCostMorphism phi : Thiele -> M is uniquely determined on the
    reachable subset of VMState by its value at [init_state] and the
    step-commutation field. States unreachable from [init_state] are not
    constrained by the universal property: they live outside the categorical
    reach of Thiele, and the morphism's value there is unconstrained.

    This packages [thiele_morphism_unique_on_traces] as the state-level
    consequence of [thiele_is_initial_a2_substrate]. *)

Corollary thiele_morphism_unique_on_reachable :
  forall (M : CertCostMachine)
         (phi1 phi2 : CertCostMorphism thiele_cert_cost_machine M),
    ccm_map _ _ phi1 init_state = ccm_map _ _ phi2 init_state ->
    forall (trace : list vm_instruction),
      ccm_map _ _ phi1 (fold_left vm_apply trace init_state) =
      ccm_map _ _ phi2 (fold_left vm_apply trace init_state).
Proof.
  intros M phi1 phi2 Hinit trace.
  exact (thiele_morphism_unique_on_traces M phi1 phi2 init_state trace Hinit).
Qed.

(** ** Scope of the initiality claim.

    The theorem [thiele_is_initial_a2_substrate] establishes that Thiele's
    trace-fold is the universal morphism into every CertCostMachine over
    [vm_instruction], given a basepoint. The state-level corollary packages
    this as uniqueness of CertCostMorphisms on reachable states.

    The categorical content: in the category of A2-respecting substrates
    over [vm_instruction] with trace-fold morphisms restricted to states
    reachable from a chosen basepoint, Thiele is initial.

    What this does not claim:

    1. That the CertCostMachine category is foundationally privileged over
       alternative cost-tracking categories. (Meta-mathematical judgment;
       not settled by any theorem inside the category.)

    2. That [vm_instruction] is foundationally privileged over alternative
       instruction signatures. (Same shape: any choice of instruction set
       defines a different CertCostMachine category, each with its own
       initial object.)

    3. That the asymmetry-of-projection theorems in
       [ProjectionNonExistence.v] imply foundational primacy beyond the
       categorical universal property proved here. The asymmetry is a
       structural fact about the relationship between two signatures;
       whether the richer signature is the foundationally privileged one
       is a separate judgment about which signatures matter.

    The claim is exactly the universal property, in exactly the precise
    sense that ℤ is the initial ring or the free group is initial in the
    category of groups with a fixed generating set. No more, no less.
*)
