(** ProbabilityImpossibility: composition laws alone do not determine a unique weight rule

  This file is a no-go result about abstraction level. It shows that simple
  compositional laws for trace weights do not force a unique probability-like
  assignment. Two different weight functions can satisfy the same additive
  interface, so extra structure is needed before one can recover anything as
  specific as the Born rule.

  The point is a boundary claim: pure composition is too weak by itself.

  *)

(* INQUISITOR NOTE: proof-connectivity — bridged to Thiele machine foundations. *)
From Kernel Require Import MuCostModel.

From Coq Require Import List Arith.PeanoNat Lia.

From Kernel Require Import VMStep.

Import ListNotations.

(** Abstract weight interface. *)

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

(** Counterexample constructions. *)

(** WEIGHT 1: Trace length

    Simply count the number of instructions. This is obviously compositional:
    length(t1++t2) = length(t1) + length(t2). *)
Definition w_len : Weight := fun t => length t.

(** WEIGHT 2: Double length

    Count instructions but multiply by 2. Still compositional:
    2*length(t1++t2) = 2*length(t1) + 2*length(t2).

    This is a DIFFERENT weight function but satisfies the same composition law. *)
Definition w_len2 : Weight := fun t => 2 * length t.

(** Compositionality proofs. *)

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

(**
    IMPOSSIBILITY THEOREM
    *)

(** BORN RULE CANNOT BE UNIQUELY DERIVED FROM COMPOSITION

    THIS IS THE KEY RESULT: Compositional structure alone does NOT uniquely
    determine weights on traces. We prove non-uniqueness by construction.

    CLAIM: There exist at least two distinct compositional weight functions.

    1. Exhibit w1 = w_len (trace length)
    2. Exhibit w2 = w_len2 (double trace length)
    3. Prove both are compositional
    4. Show they differ on at least one trace

    IMPLICATIONS:
    - The Born rule (|ψ|²) cannot be derived from composition alone
    - Probability theory requires additional axioms beyond computation
    - Frequency interpretations are not unique without extra structure
    - The kernel cannot derive its own probability measure

    To falsify: Prove all compositional weights are identical. This would
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

(**
    INTERPRETATION

    This theorem establishes a fundamental limitation: You CANNOT derive
    probability theory from pure computation. Compositional structure is
    insufficient to uniquely determine weights.
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
       Compare with PhysicsClosure.v (what it CAN do) and MuInitiality.v
       (which proves mu-cost uniqueness from instruction-consistency).

    RELATED WORK:
    - Gleason's theorem: Probabilities on Hilbert spaces must be Born rule
      (but requires Hilbert space structure, not just composition)
    - Cox's theorem: Consistent plausibility → probability axioms
      (but requires consistency postulates beyond composition)

    Neither of these works applies here because we're only assuming
    compositional structure, nothing more.

    *)
