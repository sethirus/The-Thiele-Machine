(** ThieleInitiality: trace-fold initiality and conditional state-map uniqueness.

    The source of the universal evaluation map is [list vm_instruction].
    Given a target step function and a basepoint, its fold is the unique
    basepoint-preserving map commuting with instruction extension. The
    theorem is stated for [CertCostMachine] targets; its proof does not use
    their certification or cost fields and does not select a pricing law.

    This is a free-trace universal property, not existence of a
    [CertCostMorphism] from [VMState] into every A2 system. The state-level
    corollary proves uniqueness of maps already supplied. Existence requires
    compatibility with VM trace identifications and certification. The active
    ClaimBoundaryRegression test exhibits an A2 target with no such map.

    Ledger uniqueness for a fixed schedule is proved separately in
    [MuInitiality]; exact event pricing is treated in
    [CommitmentPredicateAdequacy]. None selects a physical interpretation.
*)

From Coq Require Import List.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.
From Kernel Require Import MuInitiality.
From Kernel Require Import UniversalCertificationCost.

(** ** Unique evaluation of free instruction traces. *)

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

(** The trace-fold universal property, with an explicit target basepoint. *)
Theorem thiele_trace_fold_initial :
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

(** Compatibility name retained for existing clients. The name does not
    assert initiality of VMState under certification-preserving morphisms. *)
Definition thiele_is_initial_a2_substrate := thiele_trace_fold_initial.

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

(** Scope: a fold exists on traces without needing to descend to VMState.
    To descend, equal VM executions must have equal target evaluations and
    the target certification must agree with the VM certification. A target
    satisfying A2 alone need not satisfy either condition. A constant-false
    certification target is a counterexample even though its A2 law holds.

    No topology, metric, physical interpretation, or privileged instruction
    signature is supplied by this universal property. *)
