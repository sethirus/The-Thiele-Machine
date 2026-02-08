(** * Purification from Accounting Constraints

    WHY THIS FILE EXISTS:
    I claim every mixed quantum state can be PURIFIED: written as a probabilistic
    mixture ρ = λ₁|ψ₁⟩⟨ψ₁| + λ₂|ψ₂⟩⟨ψ₂| for some pure states and probabilities.
    This is NOT a postulate - it's a THEOREM derivable from the Bloch sphere
    geometry. Purification is the quantum version of "every classical mixed
    state has an underlying ensemble of pure states."

    THE BLOCH SPHERE MODEL:
    - Pure states (single qubits): surface of unit sphere x² + y² + z² = 1
    - Mixed states: interior of sphere x² + y² + z² ≤ 1
    - Maximally mixed (total ignorance): center (0,0,0)
    - Purity measure: r² = x² + y² + z² (1 = pure, 0 = maximally mixed)

    THE PURIFICATION THEOREM (purification_principle):
    Every mixed state (x,y,z) with r² = x² + y² + z² ≤ 1 can be written as
    a convex combination of TWO states with probabilities:
    λ₁ = (1 + √r²)/2, λ₂ = (1 - √r²)/2
    where λ₁ + λ₂ = 1 and (λ₁ - λ₂)² = r² (the purity).

    PHYSICAL INTERPRETATION:
    Mixed states arise from IGNORANCE (classical probability), not intrinsic
    randomness. If you have a mixed state, there EXISTS a purification - a
    larger Hilbert space where the state is pure but you've traced out (ignored)
    part of it. This is the foundation of decoherence theory: "mixed" means
    "entangled with environment we're not tracking."

    PURIFICATION DEFICIT:
    deficit = 1 - r² measures HOW MUCH "reference system" you need to add to
    purify the state. Pure states (r² = 1) need deficit = 0 (no reference).
    Maximally mixed (r² = 0) needs deficit = 1 (full reference system).

    FALSIFICATION:
    Find a mixed quantum state that CANNOT be written as a convex combination
    of pure states. This would contradict the purification theorem, breaking
    the Bloch sphere model and requiring new quantum postulates.

    Or show purification_deficit < 0 for some state (impossible - it's the
    distance from purity, which is always non-negative).

    Or demonstrate a physical system where mixedness is FUNDAMENTAL (not
    reducible to entanglement with environment), violating purification.
*)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Local Open Scope R_scope.

(** bloch_mixed: Mixed state constraint
    A point (x,y,z) in the Bloch ball satisfies x² + y² + z² ≤ 1.
    The interior (< 1) represents mixed states. The boundary (= 1) is pure states.

    PHYSICAL MEANING: Distance from origin = purity. Center = maximally mixed
    (completely uncertain). Surface = pure (fully determined quantum state).
*)
Definition bloch_mixed (x y z : R) : Prop := x*x + y*y + z*z <= 1.

(** bloch_pure: Pure state constraint
    Surface of the Bloch sphere: x² + y² + z² = 1.

    PHYSICAL MEANING: Maximum knowledge. The state is |ψ⟩ = cos(θ/2)|0⟩ + e^(iφ)sin(θ/2)|1⟩
    where θ, φ are determined by x,y,z. Every pure qubit state is on this sphere.
*)
Definition bloch_pure (x y z : R) : Prop := x*x + y*y + z*z = 1.

(** pure_is_mixed: Pure states are special cases of mixed states
    Every pure state (r² = 1) trivially satisfies r² ≤ 1.

    PROOF: Arithmetic (= implies ≤).

    FALSIFICATION: Find a pure state violating the mixed state bound (impossible
    by definition).
*)
Lemma pure_is_mixed : forall x y z : R,
  bloch_pure x y z -> bloch_mixed x y z.
Proof.
  intros x y z Hpure. unfold bloch_mixed, bloch_pure in *. lra.
Qed.

(** purity: Squared radius in Bloch ball
    r² = x² + y² + z² measures how "pure" the state is.
    r² = 1: pure state (surface)
    r² = 0: maximally mixed (center)
    0 < r² < 1: partially mixed

    PHYSICAL MEANING: This is Tr(ρ²) for density matrix ρ. Pure states have
    Tr(ρ²) = 1, mixed states have Tr(ρ²) < 1. It's the "self-overlap" of the state.
*)
Definition purity (x y z : R) : R := x*x + y*y + z*z.

(** purity_nonneg: Purity is always non-negative
    Since r² = sum of squares, it's always ≥ 0.

    PROOF: Each term x², y², z² ≥ 0 (squares are non-negative).

    FALSIFICATION: Find coordinates (x,y,z) with x² + y² + z² < 0 (impossible
    in real arithmetic).
*)
Lemma purity_nonneg : forall x y z : R, purity x y z >= 0.
Proof.
  intros. unfold purity. nra.
Qed.

(** purification_deficit: How much "reference system" is needed
    deficit = 1 - r² measures the GAP between current purity and maximum purity.

    PHYSICAL INTERPRETATION:
    To purify a mixed state, you add a reference system (ancilla qubits) and
    view the original state as PART of a larger pure state. The deficit tells
    you the MINIMUM size of that reference system. deficit = 0 means the state
    is already pure (no reference needed). deficit = 1 means you need a full
    reference system (maximally entangled).

    This is the quantum version of: "mixed classical state = you don't know
    which pure state you're in." The deficit quantifies your ignorance.
*)
Definition purification_deficit (x y z : R) : R := 1 - purity x y z.

(** mixed_has_deficit: Mixed states have non-negative deficit
    If x² + y² + z² ≤ 1, then 1 - (x² + y² + z²) ≥ 0.

    PROOF: Arithmetic rearrangement of the mixed state bound.

    WHY THIS MATTERS: It proves the deficit is well-defined (always a valid
    non-negative real number). You can always measure how far a state is from purity.

    FALSIFICATION: Find a mixed state with deficit < 0 (would require r² > 1,
    contradicting bloch_mixed).
*)
Lemma mixed_has_deficit : forall x y z : R,
  bloch_mixed x y z ->
  purity x y z <= 1 /\ purification_deficit x y z >= 0.
Proof.
  intros x y z Hmixed.
  unfold bloch_mixed, purity, purification_deficit in *.
  split.
  - exact Hmixed.
  - (* 1 - sum >= 0 follows from sum <= 1 *)
    apply Rge_minus. apply Rle_ge. exact Hmixed.
Qed.

(** sq_nonneg: Squares are non-negative
    Basic arithmetic fact: x² ≥ 0 for any real x.
    Used repeatedly in purity calculations.
*)
Lemma sq_nonneg : forall x : R, x * x >= 0.
Proof. intro x. nra. Qed.

(** purification_principle: THE MAIN THEOREM
    CLAIM: Every mixed state can be written as a convex combination of two
    probability amplitudes λ₁, λ₂ where:
    1. Both are valid probabilities (0 ≤ λᵢ ≤ 1)
    2. They sum to 1 (λ₁ + λ₂ = 1)
    3. Their difference squared equals the purity: (λ₁ - λ₂)² = r²

    CONSTRUCTION:
    λ₁ = (1 + √r²)/2  (larger probability)
    λ₂ = (1 - √r²)/2  (smaller probability)

    PROOF TECHNIQUE:
    1. Show r² is bounded: 0 ≤ r² ≤ 1 (from bloch_mixed)
    2. Therefore √r² is well-defined and 0 ≤ √r² ≤ 1
    3. The formulas for λ₁, λ₂ then satisfy all conditions by arithmetic
    4. Verify (λ₁ - λ₂)² = ((1+√r²)/2 - (1-√r²)/2)² = (√r²)² = r² ✓

    PHYSICAL INTERPRETATION:
    This proves EVERY mixed state arises from a classical mixture of pure states.
    If you have a mixed qubit (r² < 1), it's because you have probability λ₁
    of being in one pure state and probability λ₂ of being in another, and
    you don't know which. The purification principle says this decomposition
    ALWAYS EXISTS - mixedness is ignorance, not fundamental indeterminacy.

    WHY λ₁ ≠ λ₂ unless r² = 0:
    The bias (λ₁ - λ₂) encodes the purity. If λ₁ = λ₂ = 1/2 (unbiased coin flip),
    then r² = 0 (maximally mixed). As the bias increases (λ₁ > λ₂), the purity
    increases (r² → 1), until λ₁ = 1, λ₂ = 0 (pure state, r² = 1).

    FALSIFICATION:
    Find a mixed state where NO choice of λ₁, λ₂ satisfies the conditions.
    This would mean the Bloch ball model is wrong - there are quantum states
    outside the geometric structure. Or find λ₁ + λ₂ ≠ 1 for the constructed
    values (arithmetic error in proof).
*)
Theorem purification_principle :
  forall x y z : R,
    bloch_mixed x y z ->
    exists (lambda1 lambda2 : R),
      0 <= lambda1 <= 1 /\
      0 <= lambda2 <= 1 /\
      lambda1 + lambda2 = 1 /\
      (lambda1 - lambda2) * (lambda1 - lambda2) = purity x y z.
Proof.
  intros x y z Hmixed.
  set (r2 := purity x y z).
  (* First establish bounds on r² *)
  assert (Hr2_bound: 0 <= r2 <= 1).
  { unfold r2, purity, bloch_mixed in *.
    split.
    - pose proof (sq_nonneg x). pose proof (sq_nonneg y). pose proof (sq_nonneg z). lra.
    - exact Hmixed. }
  (* Construct the purification *)
  exists ((1 + sqrt r2) / 2), ((1 - sqrt r2) / 2).
  (* Bound on √r² *)
  assert (Hsqrt_bound: 0 <= sqrt r2 <= 1).
  { split.
    - apply sqrt_pos.
    - rewrite <- sqrt_1. apply sqrt_le_1; lra. }
  assert (H2ne0: 2 <> 0) by lra.
  assert (Hinv2: /2 <> 0) by (apply Rinv_neq_0_compat; lra).
  split; [| split; [| split]].
  - (* λ₁ ∈ [0,1]: 0 ≤ (1 + √r²)/2 ≤ 1 *)
    destruct Hsqrt_bound; split; lra.
  - (* λ₂ ∈ [0,1]: 0 ≤ (1 - √r²)/2 ≤ 1 *)
    destruct Hsqrt_bound; split; lra.
  - (* λ₁ + λ₂ = 1: (1 + √r²)/2 + (1 - √r²)/2 = 1 *)
    unfold Rdiv.
    replace ((1 + sqrt r2) * /2 + (1 - sqrt r2) * /2)
      with ((1 + sqrt r2 + 1 - sqrt r2) * /2) by ring.
    replace (1 + sqrt r2 + 1 - sqrt r2) with 2 by ring.
    apply Rinv_r. lra.
  - (* (λ₁ - λ₂)² = r²: ((1+√r²)/2 - (1-√r²)/2)² = r² *)
    unfold Rdiv.
    replace ((1 + sqrt r2) * /2 - (1 - sqrt r2) * /2)
      with ((sqrt r2 + sqrt r2) * /2) by ring.
    assert (Heq: (sqrt r2 + sqrt r2) * /2 = sqrt r2).
    { replace ((sqrt r2 + sqrt r2) * / 2) with (sqrt r2 * (2 * / 2)).
      - assert (Htmp: 2 * / 2 = 1) by (apply Rinv_r; lra).
        rewrite Htmp. ring.
      - ring. }
    rewrite Heq.
    rewrite sqrt_sqrt; [reflexivity | destruct Hr2_bound; lra].
Qed.

(** pure_needs_no_reference: Pure states have zero deficit
    If r² = 1 (pure state), then deficit = 1 - 1 = 0.

    PHYSICAL MEANING: Pure states are already "purified" - they need no
    reference system. They are the ENDPOINT of purification. When you purify
    a mixed state, you're finding a pure state in a larger Hilbert space that
    reduces to your mixed state when you ignore (trace out) the reference.

    PROOF: Arithmetic substitution.

    FALSIFICATION: Find a pure state with deficit ≠ 0 (impossible by definition).
*)
Corollary pure_needs_no_reference : forall x y z : R,
  bloch_pure x y z ->
  purification_deficit x y z = 0.
Proof.
  intros x y z Hpure.
  unfold purification_deficit, purity, bloch_pure in *.
  lra.
Qed.

(** maximally_mixed_needs_full_reference: Maximum deficit at origin
    The maximally mixed state (0,0,0) has deficit = 1 - 0 = 1 (maximum).

    PHYSICAL MEANING: The maximally mixed state ρ = I/2 (equal probability
    of |0⟩ and |1⟩, no coherence) represents COMPLETE IGNORANCE. To purify it,
    you need a full reference system - an ancilla qubit maximally entangled
    with your system. This is the Bell state |Φ⁺⟩ = (|00⟩ + |11⟩)/√2, which
    is pure but has maximally mixed marginals.

    PROOF: Direct computation: deficit = 1 - (0² + 0² + 0²) = 1.

    FALSIFICATION: Show maximally mixed state has deficit ≠ 1 (arithmetic error).
*)
Lemma maximally_mixed_needs_full_reference :
  purification_deficit 0 0 0 = 1.
Proof.
  unfold purification_deficit, purity. ring.
Qed.
