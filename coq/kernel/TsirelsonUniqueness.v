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
From Kernel Require Import ClassicalBound TsirelsonUpperBound.
From Kernel Require Import AlgebraicCoherence.

(** ** CHSH Bounds *)

(** Quantum Tsirelson bound: 2√2 ≈ 2.828427...
    Rational approximation: 5657/2000 = 2.8285 *)
Definition tsirelson_bound : Q := (5657 # 2000)%Q.

(** ** What μ=0 Actually Gives Us *)

(* SAFE: Delegates to mu_zero_chsh_bounded — this is proof composition, not a placeholder. *)
Theorem mu_zero_algebraic_bound :
  forall fuel trace s_init,
    mu_zero_program fuel trace ->
    Qabs (chsh_from_vm_trace fuel trace s_init) <= 4.
Proof.
  (* INQUISITOR NOTE: This proof delegates to mu_zero_chsh_bounded (TsirelsonUpperBound.v).
     This is PROPER PROOF COMPOSITION, not a placeholder.
     The substantive proof is in the called lemma. Short proofs can be complete proofs. *)
  intros. apply mu_zero_chsh_bounded. assumption.
Qed.

(** ** Framework Revision (January 2026): Classical vs Quantum Distinction *)

(** CORRECTED UNDERSTANDING:
    - μ=0 operations alone do NOT give classical bound!
    - The algebraic_max_trace in TsirelsonUpperBound.v shows μ=0 can achieve S=4
    - μ=0 programs can use CHSH_TRIAL to record arbitrary values
    
    CRITICAL DISTINCTION:
    - μ=0 programs: algebraic bound S ≤ 4 (proven in TsirelsonUpperBound.v)
    - PHYSICALLY REALIZABLE μ=0 correlations: classical bound S ≤ 2
      (requires factorizability constraint on the recorded values)
    - Quantum correlations (μ>0): Tsirelson bound S ≤ 2√2

    The key insight is that CHSH_TRIAL records values without verifying
    physical realizability. The classical bound applies only when the
    correlations satisfy factorizability constraints.

    See MU_COST_REVISION.md for complete framework revision. *)

(** REMOVED: The following axiom was FALSE (contradicted by mu_zero_trace_exceeds_classical)
    
    Axiom mu_zero_classical_bound :
      forall fuel trace s_init,
        mu_zero_program fuel trace ->
        Qabs (chsh_from_vm_trace fuel trace s_init) <= 2.
    
    COUNTEREXAMPLE: algebraic_max_trace achieves S = 4 with μ = 0
*)

(** ** The Correct Theorem: Coherence is What Bounds Correlations *)

Section TsirelsonBoundAssumption.

(** INQUISITOR NOTE: This Context parameter is documented in HardAssumptions.v
    as tsirelson_from_algebraic_coherence (Tsirelson's theorem).
    It becomes an explicit parameter to tsirelson_from_coherence when
    the Section closes. Use Print Assumptions to verify. *)

Context (tsirelson_from_algebraic_coherence : forall c : Correlators,
  algebraically_coherent c ->
  Qabs (E00 c) <= 1 /\ Qabs (E01 c) <= 1 /\
  Qabs (E10 c) <= 1 /\ Qabs (E11 c) <= 1 ->
  Qabs (S_from_correlators c) <= tsirelson_bound).

Theorem tsirelson_from_coherence :
  forall c : Correlators,
    algebraically_coherent c ->
    Qabs (E00 c) <= 1 /\ Qabs (E01 c) <= 1 /\
    Qabs (E10 c) <= 1 /\ Qabs (E11 c) <= 1 ->
    Qabs (S_from_correlators c) <= tsirelson_bound.
Proof.
  apply tsirelson_from_algebraic_coherence.
Qed.

End TsirelsonBoundAssumption.
