(** * MinimalE: Minimal Correlation Bound Proof

    WHY THIS FILE EXISTS:
    I claim correlation values E = ⟨AB⟩ must satisfy |E| ≤ 1 by probability
    theory alone, no quantum mechanics required. This file proves it from first
    principles using only arithmetic on rational probabilities.

    THE THEOREM (minimal_normalized_E_bound, line 20):
    For any probability distribution {p00, p01, p10, p11} (non-negative, sum to 1),
    the correlation E = p00 - p01 - p10 + p11 satisfies |E| ≤ 1.

    PROOF STRATEGY:
    1. Use Qabs_Qle_condition: |E| ≤ 1 ⟺ -1 ≤ E ≤ 1 (two inequalities)
    2. Lower bound (-1 ≤ E): Add (E + 1) = 2p00 + 2p11 ≥ 0 using non-negativity
    3. Upper bound (E ≤ 1): Show E ≤ p00 + p11 ≤ 1 using sum constraint

    WHY THIS MATTERS:
    This is the foundation for CHSH bounds. Before proving CHSH ≤ 2 (classical)
    or CHSH ≤ 2√2 (quantum), we need |E_xy| ≤ 1 for each correlation term.
    This is purely mathematical - no physics assumptions.

    PHYSICAL INTERPRETATION:
    E = ⟨AB⟩ is the expectation value of a measurement with outcomes ±1.
    Since outcomes are bounded by ±1, expectation must also be bounded by ±1.
    This is independent of quantum vs classical - it's just probability theory.

    FALSIFICATION:
    Find a valid probability distribution {p00, p01, p10, p11} (non-negative,
    summing to 1) where |p00 - p01 - p10 + p11| > 1. This would require
    violating either non-negativity or the sum-to-one constraint, breaking
    the definition of probability.

    TECHNICAL NOTE:
    Uses Coq's QArith (rationals) with ring tactics for arithmetic. Setoid
    rewriting handles rational equality (==) vs definitional equality (=).
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qring.
Require Import Coq.Setoids.Setoid.

Local Open Scope Q_scope.

(** bit_sign: Map outcome bits to ±1 sign values
    Maps 0 → +1, 1 → -1, other → 0 (invalid)

    PHYSICAL MEANING: In CHSH experiments, Alice and Bob each output a single
    bit (0 or 1), which we encode as ±1 for correlation calculations. This
    function performs that encoding.

    WHY ±1 NOT 0/1: Correlations E = ⟨AB⟩ are computed as expectations of
    products. With ±1 encoding: E = (+1)(+1)·p00 + (+1)(-1)·p01 + ...
    = p00 - p01 - p10 + p11. This gives the natural correlation formula.

    FALSIFICATION: Use different outcome encoding (e.g., {0,1} or {0,2}) and
    verify correlation bounds still hold. The ±1 choice is conventional but
    not unique.
*)
Definition bit_sign (n : nat) : Q :=
  if Nat.eqb n 0%nat then 1#1 else if Nat.eqb n 1%nat then (-1)#1 else 0#1.

(** Qopp_0_le: Negation reverses inequality
    If 0 ≤ x then -x ≤ 0.

    PROOF TECHNIQUE: Use Qle_minus_iff to convert to subtraction form, then
    simplify using ring arithmetic (0 + -(-x) = x).

    WHY THIS MATTERS: Used repeatedly in correlation bound proofs when we need
    to flip signs of inequalities. Fundamental property of ordered rings.

    FALSIFICATION: Find x where 0 ≤ x but -x > 0 (violates additive inverses).
*)
Lemma Qopp_0_le: forall x : Q, 0 <= x -> - x <= 0.
Proof.
  intros.
  apply <- Qle_minus_iff.
  assert (Hrw: 0 + - (- x) == x) by ring.
  setoid_rewrite Hrw.
  exact H.
Qed.

(** minimal_normalized_E_bound: THE MAIN THEOREM
    CLAIM: For any probability distribution p = {p00, p01, p10, p11} where:
    - All probabilities are non-negative: p_ab ≥ 0
    - Probabilities sum to one: Σ p_ab = 1
    The correlation E = p00 - p01 - p10 + p11 satisfies |E| ≤ 1.

    PROOF STRUCTURE (two parts):
    1. LOWER BOUND (-1 ≤ E):
       Add 1 to E: E + 1 = (p00 - p01 - p10 + p11) + 1
       Use sum constraint: Σp = 1, so E + 1 = E + Σp = 2p00 + 2p11
       Since p00, p11 ≥ 0, we have 2p00 + 2p11 ≥ 0, thus E + 1 ≥ 0, thus E ≥ -1 ✓

    2. UPPER BOUND (E ≤ 1):
       Show E ≤ p00 + p11 (since -p01 - p10 ≤ 0 from non-negativity)
       Show p00 + p11 ≤ 1 (since p00 + p11 ≤ p00 + p01 + p10 + p11 = 1)
       Chain inequalities: E ≤ p00 + p11 ≤ 1, thus E ≤ 1 ✓

    PHYSICAL INTERPRETATION:
    This proves that expectation values of dichotomic measurements (outcomes ±1)
    are bounded by ±1, regardless of the underlying probability distribution.
    This is the foundation for ALL CHSH inequalities - both classical (≤2) and
    quantum (≤2√2) bounds build on |E_xy| ≤ 1.

    WHY RATIONAL ARITHMETIC:
    Uses Q (rationals) not R (reals) to stay computational. All probabilities
    in our VM are rational (finite precision). Coq's `ring` tactic simplifies
    rational polynomial expressions automatically.

    SETOID REWRITING:
    Rationals use setoid equality (==) not definitional equality (=). The
    `setoid_rewrite` tactic handles this, converting between == and Leibniz =.

    FALSIFICATION:
    Find probabilities {p00, p01, p10, p11} with:
    - All p_ab ≥ 0
    - p00 + p01 + p10 + p11 = 1
    - |p00 - p01 - p10 + p11| > 1
    This would violate probability axioms (no such distribution exists).

    Or show the ring simplifications are incorrect (check with SMT solver).
*)
Lemma minimal_normalized_E_bound:
  forall p00 p01 p10 p11 : Q,
    0#1 <= p00 -> 0#1 <= p01 -> 0#1 <= p10 -> 0#1 <= p11 ->
    p00 + p01 + p10 + p11 == 1#1 ->
    Qabs (p00 - p01 - p10 + p11) <= 1#1.
Proof.
  intros p00 p01 p10 p11 Hp00 Hp01 Hp10 Hp11 Hsum.
  (* Use Qabs_Qle_condition: |E| <= 1 iff -1 <= E <= 1 (decompose absolute value) *)
  setoid_rewrite Qabs_Qle_condition.
  split.
  - (* PART 1: Show -1 <= p00 - p01 - p10 + p11 (lower bound) *)
    (* Strategy: prove E + 1 ≥ 0, which implies E ≥ -1 *)
    (* Key insight: E + 1 = E + Σp = 2p00 + 2p11 ≥ 0 (from non-negativity) *)
    assert (Heq: (p00 - p01 - p10 + p11) + 1 == (p00 - p01 - p10 + p11) + (p00 + p01 + p10 + p11)).
    { setoid_rewrite Hsum. ring. }
    (* Prove E + 1 ≥ 0 by showing it equals 2p00 + 2p11 (both non-negative terms) *)
    assert (H_pos: 0 <= (p00 - p01 - p10 + p11) + 1).
    { setoid_rewrite Heq.
      (* Ring simplification: (E + Σp) = 2p00 + 2p11 *)
      assert (Hrw2: (p00 - p01 - p10 + p11) + (p00 + p01 + p10 + p11) == (p00 + p00) + (p11 + p11)) by ring.
      setoid_rewrite Hrw2.
      (* Show 2p00 ≥ 0 *)
      assert (H00: 0 <= p00 + p00).
      { assert (Hrw: 0 == 0 + 0) by ring. setoid_rewrite Hrw.
        apply Qplus_le_compat; [exact Hp00 | exact Hp00]. }
      (* Show 2p11 ≥ 0 *)
      assert (H11: 0 <= p11 + p11).
      { assert (Hrw: 0 == 0 + 0) by ring. setoid_rewrite Hrw.
        apply Qplus_le_compat; [exact Hp11 | exact Hp11]. }
      (* Combine: 0 ≤ 2p00 + 2p11 *)
      assert (Hrw3: 0 == 0 + 0) by ring.
      setoid_rewrite Hrw3.
      apply Qplus_le_compat; [exact H00 | exact H11]. }
    (* Convert E + 1 ≥ 0 to -1 ≤ E using subtraction lemma *)
    assert (Hrw_final: forall a b, 0 <= a - b -> b <= a).
    { intros. apply <- Qle_minus_iff. exact H. }
    apply (Hrw_final (p00 - p01 - p10 + p11) (-1)).
    assert (Heq2: (p00 - p01 - p10 + p11) - (-1) == (p00 - p01 - p10 + p11) + 1) by ring.
    setoid_rewrite Heq2. exact H_pos.
  - (* PART 2: Show p00 - p01 - p10 + p11 <= 1 (upper bound) *)
    (* Strategy: E = p00 + p11 - (p01 + p10) ≤ p00 + p11 (since p01, p10 ≥ 0)
       Then show p00 + p11 ≤ 1 (since they're part of a sum equaling 1) *)
    (* First prove p00 + p11 ≤ 1 *)
    assert (H_bound: p00 + p11 <= 1).
    { apply (Qle_trans _ (p00 + p01 + p10 + p11) _).
      - (* Show p00 + p11 ≤ p00 + p01 + p10 + p11 (adding non-negative terms) *)
        assert (H0: 0 <= p01 + p10).
        { assert (Hrw: 0 == 0 + 0) by ring. setoid_rewrite Hrw.
          apply Qplus_le_compat; [exact Hp01 | exact Hp10]. }
        assert (H_prep: (p00 + p11) + 0 <= (p00 + p11) + (p01 + p10)).
        { apply Qplus_le_compat; [apply Qle_refl | exact H0]. }
        assert (Hrw1: (p00 + p11) + 0 == p00 + p11) by ring.
        assert (Hrw2: (p00 + p11) + (p01 + p10) == p00 + p01 + p10 + p11) by ring.
        setoid_rewrite Hrw1 in H_prep.
        setoid_rewrite Hrw2 in H_prep.
        exact H_prep.
      - (* Use sum constraint: Σp = 1 *)
        setoid_rewrite Hsum. apply Qle_refl. }
    (* Now show E ≤ p00 + p11 using E = (p00 + p11) - (p01 + p10) *)
    apply (Qle_trans _ (p00 + p11) _); [|exact H_bound].
    (* Show E ≤ p00 + p11, i.e., (p00 + p11) - E ≥ 0 *)
    assert (H0: 0 <= p01 + p10).
    { assert (Hrw: 0 == 0 + 0) by ring. setoid_rewrite Hrw.
      apply Qplus_le_compat; [exact Hp01 | exact Hp10]. }
    apply <- Qle_minus_iff.
    (* Ring simplification: (p00 + p11) - E = p01 + p10 ≥ 0 *)
    assert (Hrw: p00 + p11 - (p00 - p01 - p10 + p11) == p01 + p10) by ring.
    setoid_rewrite Hrw.
    exact H0.
Qed.

Close Scope Q_scope.
