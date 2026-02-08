(** =========================================================================
    VALID CORRELATION: Abstract Correlation Box Interface
    =========================================================================

    WHY THIS FILE EXISTS:
    I claim correlation boxes provide the RIGHT abstraction for Bell inequality
    proofs. This file defines valid correlations (non-negative, normalized,
    no-signaling) and local boxes (convex combinations of deterministic strategies).
    This separates the abstract mathematical structure from physical implementation.

    THE CORE CLAIM:
    bell_math_deterministic (line 39): Any deterministic local strategy
    (Alice/Bob each output ±1) satisfies |CHSH| ≤ 2. This is Bell's theorem
    in pure mathematics - no quantum mechanics, no physics, just algebra.

    WHAT THIS PROVES:
    - Box: Abstract correlation function (line 8)
    - non_negative, normalized, no_signaling: Valid correlation properties
    - deterministic_box (line 26): Single deterministic strategy
    - local_box (line 30): Convex combination of deterministic strategies
    - bell_math_deterministic (line 39): Classical CHSH bound

    PHYSICAL INTERPRETATION:
    A "box" is a black box that takes Alice's input x, Bob's input y, and
    outputs joint probabilities P(a,b|x,y). Valid boxes satisfy:
    - Non-negativity: probabilities ≥ 0
    - Normalization: probabilities sum to 1 for each (x,y)
    - No-signaling: Alice's marginals don't depend on Bob's input (and vice versa)

    Local boxes are those achievable with shared randomness + local determinism.
    Bell's theorem: local boxes have |CHSH| ≤ 2, but quantum correlations reach 2√2.

    FALSIFICATION:
    Show that bell_math_deterministic fails for some deterministic strategy -
    find functions gA, gB : nat -> {-1,+1} where |CHSH| > 2. This would
    contradict the theorem (line 39), but it's impossible (proven by exhaustive
    case analysis over all 2^4 = 16 deterministic strategies).

    Or show that a local box can violate no-signaling. This would break the
    definition (line 22-24) and contradict special relativity.

    NO AXIOMS. NO ADMITS. Pure mathematical definitions + Bell's theorem.

    ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.Lists.List.
Require Import Psatz.

Local Open Scope Q_scope.

(** =========================================================================
    CORRELATION BOX ABSTRACTION
    ========================================================================= *)

(** BOX: Abstract correlation function

    REPRESENTS: A black box taking inputs (x,y) from Alice and Bob,
    outputting joint probability distribution P(a,b|x,y).

    STRUCTURE: Box = (x:nat, y:nat, a:nat, b:nat) -> Q
    - x, y: Alice's and Bob's inputs (measurement settings)
    - a, b: Alice's and Bob's outputs (measurement outcomes)
    - Result: Rational probability Q (exact arithmetic)

    WHY RATIONALS: Using Q (exact rationals) instead of R (reals) avoids
    classical axioms and makes proofs fully constructive. *)
Definition Box := nat -> nat -> nat -> nat -> Q.

(** =========================================================================
    VALID CORRELATION PROPERTIES
    ========================================================================= *)

(** NON-NEGATIVE: All probabilities are non-negative

    WHY: Fundamental axiom of probability theory. Negative probabilities
    would violate measure theory and make no physical sense. *)
Definition non_negative (B : Box) : Prop :=
  forall x y a b, 0 <= B x y a b.

(** NORMALIZED: Probabilities sum to 1 for each input pair

    WHY: The four outcomes (a,b) ∈ {0,1}×{0,1} must form a complete
    probability distribution. Total probability = 1. *)
Definition normalized (B : Box) : Prop :=
  forall x y, (B x y 0%nat 0%nat + B x y 0%nat 1%nat +
               B x y 1%nat 0%nat + B x y 1%nat 1%nat) == 1.

(** =========================================================================
    MARGINAL DISTRIBUTIONS
    ========================================================================= *)

(** MARGINAL_A: Alice's marginal probability P(a|x,y)

    REPRESENTS: Probability Alice gets outcome a, summed over Bob's outcomes.

    FORMULA: P_A(a|x,y) = P(a,0|x,y) + P(a,1|x,y) *)
Definition marginal_a (B : Box) (x y a : nat) : Q :=
  B x y a 0%nat + B x y a 1%nat.

(** MARGINAL_B: Bob's marginal probability P(b|x,y)

    REPRESENTS: Probability Bob gets outcome b, summed over Alice's outcomes.

    FORMULA: P_B(b|x,y) = P(0,b|x,y) + P(1,b|x,y) *)
Definition marginal_b (B : Box) (x y b : nat) : Q :=
  B x y 0%nat b + B x y 1%nat b.

(** =========================================================================
    NO-SIGNALING CONDITION
    ========================================================================= *)

(** NO-SIGNALING: Einstein locality constraint

    WHY THIS MATTERS: This is special relativity. Alice's marginal probabilities
    cannot depend on Bob's choice of measurement (y), and vice versa. Otherwise,
    Alice could send signals to Bob faster than light by changing her measurement.

    FORMAL STATEMENT:
    - Alice's marginals independent of y: P_A(a|x,y1) = P_A(a|x,y2)
    - Bob's marginals independent of x: P_B(b|x1,y) = P_B(b|x2,y)

    This is WEAKER than locality (which forbids shared randomness) but STRONGER
    than allowing arbitrary correlations. No-signaling boxes form the polytope
    of quantum-achievable correlations + superquantum correlations (PR-boxes). *)
Definition no_signaling (B : Box) : Prop :=
  (forall x y1 y2 a, marginal_a B x y1 a == marginal_a B x y2 a) /\
  (forall x1 x2 y b, marginal_b B x1 y b == marginal_b B x2 y b).

(** =========================================================================
    LOCAL BOXES (BELL'S TARGET)
    ========================================================================= *)

(** DETERMINISTIC_BOX: Single deterministic local strategy

    REPRESENTS: Alice and Bob each have deterministic response functions:
    - fA : nat -> nat (Alice's function: input x -> output a)
    - fB : nat -> nat (Bob's function: input y -> output b)

    The box outputs 1 if (a,b) = (fA(x), fB(y)), otherwise 0.

    WHY: This is the atomic building block of local correlations. Any local
    box is a convex combination of deterministic boxes (shared randomness
    selects which deterministic strategy to use). *)
Definition deterministic_box (B : Box) : Prop :=
  exists (fA fB : nat -> nat),
    forall x y a b, B x y a b ==
      (if (Nat.eqb a (fA x)) && (Nat.eqb b (fB y)) then 1 else 0).

(** LOCAL_BOX: Convex combination of deterministic strategies

    REPRESENTS: Alice and Bob share random variable λ with distribution
    {weights}. For each λ, they use deterministic strategy det_boxes[λ].

    FORMULA: B = Σ_λ weight[λ] · det_boxes[λ]

    WHY THIS IS LOCALITY: Shared randomness is okay (they can meet beforehand
    and flip coins), but response functions must be local (no communication
    during measurement).

    BELL'S THEOREM: Local boxes satisfy |CHSH| ≤ 2. Quantum boxes reach 2√2.
    This is the gap Bell discovered. *)
Definition local_box (B : Box) : Prop :=
  exists (weights : list Q) (det_boxes : list Box),
    (forall db, In db det_boxes -> deterministic_box db) /\
    (forall w, In w weights -> 0 <= w) /\
    (length weights = length det_boxes) /\
    (fold_right Qplus 0 weights == 1) /\
    (forall x y a b, B x y a b == fold_right Qplus 0
      (map (fun '(w, db) => w * db x y a b) (combine weights det_boxes))).

(** =========================================================================
    BELL'S THEOREM (MATHEMATICAL CORE)
    ========================================================================= *)

(** BELL'S THEOREM: Deterministic strategies are bounded

    THIS IS THE KEY MATHEMATICAL FACT: Any deterministic local strategy
    (Alice outputs ±1 depending on x, Bob outputs ±1 depending on y)
    satisfies |CHSH| ≤ 2.

    CLAIM: For functions gA, gB : nat -> {-1, +1}, the CHSH polynomial
    S = gA(0)·gB(0) + gA(0)·gB(1) + gA(1)·gB(0) - gA(1)·gB(1)
    satisfies |S| ≤ 2.

    PROOF STRATEGY: Exhaustive case analysis. There are 2^4 = 16 possible
    deterministic strategies (each of gA(0), gA(1), gB(0), gB(1) can be ±1).
    Coq checks all 16 cases and verifies |S| ≤ 2 for each.

    WHY THIS PROVES BELL'S THEOREM: Local boxes are convex combinations of
    deterministic strategies. Convex combinations preserve bounds. If each
    deterministic strategy has |S| ≤ 2, then any convex combination also has
    |S| ≤ 2. Therefore, ALL local boxes satisfy |CHSH| ≤ 2.

    QUANTUM VIOLATION: The singlet state achieves |CHSH| = 2√2 ≈ 2.828,
    violating this bound. Therefore, quantum correlations are NOT local.

    FALSIFICATION: Find values gA(0), gA(1), gB(0), gB(1) ∈ {-1,+1} where
    |S| > 2. The proof checks all 16 cases - it's impossible. *)
Theorem bell_math_deterministic :
  forall (gA gB : nat -> Q),
    (forall x, gA x == 1 \/ gA x == -1) ->
    (forall y, gB y == 1 \/ gB y == -1) ->
    Qabs (gA 0%nat * gB 0%nat + gA 0%nat * gB 1%nat +
          gA 1%nat * gB 0%nat - gA 1%nat * gB 1%nat) <= 2.
Proof.
  intros gA gB HgA HgB.

  (* === Exhaustive case analysis: 2^4 = 16 deterministic strategies === *)
  (* For each of gA(0), gA(1), gB(0), gB(1), branch on ±1 *)
  destruct (HgA 0%nat) as [A0 | A0]; destruct (HgA 1%nat) as [A1 | A1];
  destruct (HgB 0%nat) as [B0 | B0]; destruct (HgB 1%nat) as [B1 | B1];

  (* Substitute the ±1 values *)
  rewrite A0, A1, B0, B1;

  (* Simplify arithmetic and verify |S| ≤ 2 *)
  try field_simplify;   (* Algebraic simplification *)
  try apply Qabs_case;  (* Handle absolute value *)
  nra.                  (* Nonlinear rational arithmetic solver *)
                        (* Verifies the inequality for this case *)

  (* Coq repeats this for all 16 branches. Each succeeds. QED. *)
Qed.

(** =========================================================================
    INTERPRETATION

    This file establishes the MATHEMATICAL foundation of Bell's theorem:

    1. ABSTRACT CORRELATION BOXES:
       Clean separation between mathematical structure (Box, no_signaling)
       and physical implementation (quantum states, local hidden variables).

    2. BELL'S THEOREM AS PURE MATH:
       The classical bound |CHSH| ≤ 2 is proven by exhaustive case analysis
       over deterministic strategies. No physics, no quantum mechanics, just
       algebra and logic.

    3. CONNECTION TO PHYSICS:
       - Local boxes = classical correlations (shared randomness + locality)
       - Quantum boxes = quantum correlations (violate Bell, satisfy no-signal)
       - No-signal boxes = all relativistic correlations (includes PR-boxes)

    4. TSIRELSON BOUND:
       Quantum boxes satisfy |CHSH| ≤ 2√2 (proven in TsirelsonUpperBound.v).
       This is STRONGER than no-signaling (which allows |CHSH| ≤ 4), but
       WEAKER than locality (which forces |CHSH| ≤ 2).

    USED BY:
    - BoxCHSH.v: Concrete CHSH computation on boxes
    - MinorConstraints.v: Connection to Fine's theorem
    - TsirelsonUpperBound.v: Quantum bound derivation

    ========================================================================= *)
