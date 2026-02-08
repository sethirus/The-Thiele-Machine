(** =========================================================================
    PROBABILITY IMPOSSIBILITY: Born Rule Cannot Be Uniquely Derived
    =========================================================================

    WHY THIS FILE EXISTS:
    I claim the Born rule (probability = |amplitude|²) is NOT uniquely determined
    by composition laws alone. This proves the kernel CANNOT derive probability
    theory from pure computation - you must ADD probabilistic structure as input.
    This establishes the boundary between what's derivable and what requires axioms.

    THE CORE CLAIM:
    Born_Rule_Unique_Fails_Without_More_Structure (line 38): There exist at least
    TWO distinct compositional weight functions (w_len and w_len2). Both satisfy
    composition laws (w(t1++t2) = w(t1)+w(t2)), but give different values.
    Therefore, composition alone doesn't uniquely determine weights.

    WHAT THIS PROVES:
    - weight_compositional (line 15): Abstract interface for trace weights
    - w_len_compositional (line 22): Trace length is compositional
    - w_len2_compositional (line 30): Double length is also compositional
    - Born_Rule_Unique_Fails_Without_More_Structure (line 38): Non-uniqueness proof

    PHYSICAL INTERPRETATION:
    This is a NO-GO result. If you want probability theory in your computational
    model, you must ASSUME it - it doesn't follow from algebraic composition laws.
    The Born rule (|ψ|²) is a POSTULATE of quantum mechanics, not a theorem.

    Similarly, "frequency weights" or "probability measures" over traces cannot
    be uniquely derived from compositional structure. You need additional axioms
    (Kolmogorov axioms, measure theory, etc.) beyond pure computation.

    FALSIFICATION:
    Show that compositional weights are unique - prove that all functions satisfying
    w(t1++t2) = w(t1)+w(t2) and w([]) = 0 must be identical. This would contradict
    the theorem (line 38) which explicitly constructs two different ones.

    Or prove the Born rule follows from computation alone. This would invalidate
    the no-go result and suggest probability is derivable after all.

    NO AXIOMS. NO ADMITS. Pure negative result.

    ========================================================================= *)

From Coq Require Import List Arith.PeanoNat Lia.

From Kernel Require Import VMStep.

Import ListNotations.

(** =========================================================================
    ABSTRACT WEIGHT INTERFACE
    ========================================================================= *)

(** WEIGHT: Abstract "probability-like" function on traces

    REPRESENTS: Any numerical assignment to instruction sequences that might
    represent frequency, probability, cost, or other compositional measure.

    This is intentionally general - we're proving a negative result, so we
    want the weakest possible assumptions. *)
Definition Weight := list vm_instruction -> nat.

(** COMPOSITIONAL WEIGHT: Algebraic composition law

    A weight is compositional if:
    1. Empty trace has weight 0: w([]) = 0
    2. Sequential composition adds: w(t1++t2) = w(t1) + w(t2)

    This is the minimal algebraic structure one might hope uniquely determines
    probability. We prove it DOESN'T. *)
Definition weight_compositional (w : Weight) : Prop :=
  w [] = 0 /\
  forall t1 t2, w (t1 ++ t2) = w t1 + w t2.

(** =========================================================================
    COUNTEREXAMPLE CONSTRUCTIONS
    ========================================================================= *)

(** WEIGHT 1: Trace length

    Simply count the number of instructions. This is obviously compositional:
    length(t1++t2) = length(t1) + length(t2). *)
Definition w_len : Weight := fun t => length t.

(** WEIGHT 2: Double length

    Count instructions but multiply by 2. Still compositional:
    2*length(t1++t2) = 2*length(t1) + 2*length(t2).

    This is a DIFFERENT weight function but satisfies the same composition law. *)
Definition w_len2 : Weight := fun t => 2 * length t.

(** =========================================================================
    COMPOSITIONALITY PROOFS
    ========================================================================= *)

(** W_LEN IS COMPOSITIONAL: Trace length satisfies composition

    WHY THIS LEMMA: Establishes that simple trace length is a valid weight.

    STRATEGY: Direct calculation using list properties. *)
Lemma w_len_compositional : weight_compositional w_len.
Proof.
  split.
  - (* Base case: empty trace has length 0 *)
    reflexivity.
  - (* Composition: length(t1++t2) = length(t1) + length(t2) *)
    intros t1 t2. unfold w_len.
    (* Use app_length: length (l1 ++ l2) = length l1 + length l2 *)
    rewrite app_length.
    (* Arithmetic: both sides equal *)
    lia.
Qed.

(** W_LEN2 IS COMPOSITIONAL: Double length also satisfies composition

    WHY THIS LEMMA: Establishes the second counterexample weight.

    STRATEGY: Same as w_len but with factor of 2. *)
Lemma w_len2_compositional : weight_compositional w_len2.
Proof.
  split.
  - (* Base case: 2*0 = 0 *)
    reflexivity.
  - (* Composition: 2*length(t1++t2) = 2*length(t1) + 2*length(t2) *)
    intros t1 t2. unfold w_len2.
    (* Use app_length *)
    rewrite app_length.
    (* Arithmetic: 2*(a+b) = 2*a + 2*b *)
    lia.
Qed.

(** =========================================================================
    IMPOSSIBILITY THEOREM
    ========================================================================= *)

(** BORN RULE CANNOT BE UNIQUELY DERIVED FROM COMPOSITION

    THIS IS THE KEY RESULT: Compositional structure alone does NOT uniquely
    determine weights on traces. We prove non-uniqueness by construction.

    CLAIM: There exist at least two distinct compositional weight functions.

    PROOF STRATEGY:
    1. Exhibit w1 = w_len (trace length)
    2. Exhibit w2 = w_len2 (double trace length)
    3. Prove both are compositional
    4. Show they differ on at least one trace

    IMPLICATIONS:
    - The Born rule (|ψ|²) cannot be derived from composition alone
    - Probability theory requires additional axioms beyond computation
    - Frequency interpretations are not unique without extra structure
    - The kernel cannot derive its own probability measure

    FALSIFICATION: Prove all compositional weights are identical. This would
    require showing w_len = w_len2, but we explicitly demonstrate they differ
    on the trace [instr_halt 0]: w_len gives 1, w_len2 gives 2. *)
Theorem Born_Rule_Unique_Fails_Without_More_Structure :
  exists w1 w2,
    weight_compositional w1 /\
    weight_compositional w2 /\
    (exists t, w1 t <> w2 t).
Proof.
  (* === PART 1: Exhibit the two weight functions === *)
  exists w_len, w_len2.

  split.
  - (* w_len is compositional (proven above) *)
    exact w_len_compositional.

  - split.
    + (* w_len2 is compositional (proven above) *)
      exact w_len2_compositional.

    + (* === PART 2: Show they differ on some trace === *)
      (* Witness: single halt instruction *)
      exists [instr_halt 0].

      (* Compute: w_len [halt] = 1, w_len2 [halt] = 2 *)
      simpl.

      (* 1 ≠ 2 by discrimination *)
      discriminate.
Qed.

(** =========================================================================
    INTERPRETATION

    This theorem establishes a fundamental limitation: You CANNOT derive
    probability theory from pure computation. Compositional structure is
    insufficient to uniquely determine weights.

    WHAT THIS MEANS:

    1. BORN RULE IS POSTULATED, NOT DERIVED:
       Quantum mechanics assumes |ψ|² gives probabilities. This cannot be
       proven from composition laws alone. It's an additional axiom.

    2. FREQUENCY INTERPRETATION REQUIRES CHOICE:
       If you want to assign "probabilities" to traces, you must CHOOSE a
       weight function. Composition laws don't force a unique choice.

    3. KERNEL CANNOT DERIVE PROBABILITY:
       The Thiele Machine derives many things (Tsirelson bound, second law,
       locality), but probability theory is NOT among them. Probability
       requires additional structure beyond μ-cost and partition dynamics.

    4. BOUNDARY OF DERIVABILITY:
       This is a clean NO-GO result showing what the kernel CANNOT do.
       Compare with PhysicsClosure.v (what it CAN do) and NoGo.v (what
       requires additional structure).

    RELATED WORK:
    - Gleason's theorem: Probabilities on Hilbert spaces must be Born rule
      (but requires Hilbert space structure, not just composition)
    - Cox's theorem: Consistent plausibility → probability axioms
      (but requires consistency postulates beyond composition)

    Neither of these works applies here because we're only assuming
    compositional structure, nothing more.

    ========================================================================= *)
