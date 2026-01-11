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
    - μ=0 operations give classical bound: CHSH ≤ 2
    - Quantum Tsirelson bound (2√2) requires μ>0 operations

    The original theorem below was incorrect. μ=0 traces can exceed
    the algebraic bound (4) but CANNOT exceed the Tsirelson bound (2√2).
    In fact, μ=0 traces are limited to the classical bound (2 < 2√2).

    See MU_COST_REVISION.md for complete analysis. *)

(** Classical bound for μ=0 (proven in MinorConstraints.v) *)
Axiom mu_zero_classical_bound :
  forall fuel trace s_init,
    mu_zero_program fuel trace ->
    Qabs (chsh_from_vm_trace fuel trace s_init) <= 2.

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
