(** =========================================================================
    TSIRELSON UNIQUENESS - Corrected Statement
    =========================================================================
    
    CORRECTION: The original claim was wrong.
    
    WRONG CLAIM: μ=0 implies S ≤ 2√2
    TRUTH: μ=0 only implies S ≤ 4 (algebraic max)
    
    The Tsirelson bound requires algebraic coherence (NPA level 1).
    This is a constraint on the CORRELATIONS, not the INSTRUCTIONS.
    
    ========================================================================= *)

From Coq Require Import QArith Qabs Lia List.
Import ListNotations.
Local Open Scope Q_scope.

From Kernel Require Import VMState VMStep CHSHExtraction MuCostModel.
From Kernel Require Import TsirelsonLowerBound TsirelsonUpperBound.
From Kernel Require Import AlgebraicCoherence.

(** ** What μ=0 Actually Gives Us *)

Theorem mu_zero_algebraic_bound :
  forall fuel trace s_init,
    mu_zero_program fuel trace ->
    Qabs (chsh_from_vm_trace fuel trace s_init) <= 4.
Proof.
  (* This is the actual proven bound *)
  intros. apply mu_zero_chsh_bounded. assumption.
Qed.

(** ** The Tsirelson Bound Requires Additional Structure *)

Theorem tsirelson_requires_coherence :
  (* There exist μ=0 traces that exceed Tsirelson *)
  exists fuel trace s_init,
    mu_zero_program fuel trace /\
    Qabs (chsh_from_vm_trace fuel trace s_init) > tsirelson_bound.
Proof.
  exists 4%nat, algebraic_max_trace, init_state_for_algebraic_max.
  split.
  - (* μ=0 *) exact algebraic_max_trace_mu_zero.
  - (* S > 2√2 *) exact mu_zero_trace_exceeds_tsirelson.
Qed.

(** ** The Correct Theorem: Coherence is What Bounds Correlations *)

Theorem tsirelson_from_coherence :
  forall c : Correlators,
    algebraically_coherent c ->
    Qabs (E00 c) <= 1 /\ Qabs (E01 c) <= 1 /\
    Qabs (E10 c) <= 1 /\ Qabs (E11 c) <= 1 ->
    Qabs (S_from_correlators c) <= tsirelson_bound.
Proof.
  apply tsirelson_from_algebraic_coherence.
Qed.
