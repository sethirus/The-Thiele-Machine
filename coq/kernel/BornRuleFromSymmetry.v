(** =========================================================================
    BORN RULE FROM TENSOR PRODUCT CONSISTENCY
    =========================================================================

    This file CLOSES the circularity gap identified in BornRule.v.

    THE PREVIOUS GAP:
    BornRule.v derives the Born rule from "is_linear_in_z": P(z) = az + b.
    But linearity in z IS the Born rule restated — circular!

    THE FIX:
    Replace the linearity axiom with TENSOR PRODUCT CONSISTENCY:
        g(x * y) = g(x) * g(y)
    for overlap-squared values x, y in [0,1].

    This property follows from the machine's module independence
    (ThieleUnificationTensor.v): measuring independent partitions gives
    independent outcomes. It is NOT a physics axiom — it's a structural
    theorem of the machine.

    THE DERIVATION:
    Let g : [0,1] -> [0,1] be the probability mapping |overlap|^2 -> P.

    Axioms:
        (E) g(1) = 1                        [eigenstate consistency]
        (N) g(x) + g(1-x) = 1              [normalization]
        (T) g(x*y) = g(x)*g(y)             [tensor product consistency]
        (R) g maps [0,1] to [0,1]           [probability range]

    Derived:
        g(0) = 0, g(1/2) = 1/2, g(1/4) = 1/4, g(1/2^n) = (1/2)^n
        g is monotone non-decreasing (from multiplicativity)
        g(x) = x for all x in [0,1] (Born rule)

    NON-CIRCULARITY:
    - (E) is eigenstate consistency (not quantum-specific)
    - (N) is probability normalization (not quantum-specific)
    - (T) follows from module independence (machine structural property)
    - (R) is probability range (not quantum-specific)
    None of these assumptions are "the Born rule in disguise."

    DEPENDENCY CHAIN:
      ComplexNecessity.v    -> amplitudes are complex (U(1) structure)
      TensorNecessity.v     -> independent modules compose via tensor product
      BornRuleUnique.v      -> only n=2 power law is consistent
      THIS FILE             -> Born rule from tensor consistency

    STATUS: ZERO AXIOMS. ZERO ADMITS.
    ========================================================================= *)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Local Open Scope R_scope.

(** =========================================================================
    PART 1: EXISTENCE — The Born rule satisfies all axioms
    =========================================================================

    We first verify that g(x) = x (the Born rule) satisfies eigenstate
    consistency, normalization, tensor product consistency, and range.
    This establishes that our axiom set is consistent (has a model). *)

Definition born_identity (x : R) : R := x.

Lemma born_identity_eigenstate : born_identity 1 = 1.
Proof. unfold born_identity. ring. Qed.

Lemma born_identity_normalization : forall x,
  0 <= x -> x <= 1 -> born_identity x + born_identity (1 - x) = 1.
Proof. intros. unfold born_identity. ring. Qed.

Lemma born_identity_tensor : forall x y,
  0 <= x -> x <= 1 -> 0 <= y -> y <= 1 ->
  born_identity (x * y) = born_identity x * born_identity y.
Proof. intros. unfold born_identity. ring. Qed.

Lemma born_identity_range : forall x,
  0 <= x -> x <= 1 -> 0 <= born_identity x /\ born_identity x <= 1.
Proof. intros. unfold born_identity. lra. Qed.

(** =========================================================================
    PART 2: UNIQUENESS — The axioms force g = identity
    =========================================================================

    We now prove that ANY function satisfying the four axioms must equal
    the identity function. This is where the linearity gap is closed. *)

Section BornRuleUniqueness.

Variable g : R -> R.

(** === THE FOUR NON-CIRCULAR AXIOMS === *)

(** Axiom E: Eigenstate consistency —
    Measuring a state in its own basis gives certain outcome.
    SOURCE: Definition of eigenstate (not quantum-specific). *)
(* INQUISITOR NOTE: local section assumption for uniqueness theorem. *)
Context (g_one : g 1 = 1).

(** Axiom N: Normalization —
    Binary outcome probabilities sum to 1. Here x = |<phi|psi>|^2
    for one outcome, and 1-x is the overlap for the other.
    SOURCE: Probability theory (not quantum-specific). *)
(* INQUISITOR NOTE: local section assumption for uniqueness theorem. *)
Context (g_norm : forall x, 0 <= x -> x <= 1 ->
  g x + g (1 - x) = 1).

(** Axiom T: Tensor product consistency —
    For product states |psi_1> ⊗ |psi_2>, the joint outcome probability
    equals the product of individual probabilities.
    SOURCE: Module independence (ThieleUnificationTensor.v proves that
    independent partitions compose via tensor product, giving multiplicative
    dimensions and factored probabilities). *)
(* INQUISITOR NOTE: local section assumption for uniqueness theorem. *)
Context (g_mult : forall x y,
  0 <= x -> x <= 1 -> 0 <= y -> y <= 1 ->
  g (x * y) = g x * g y).

(** Axiom R: Probability range —
    g maps [0,1] to [0,1]. *)
(* INQUISITOR NOTE: local section assumption for uniqueness theorem. *)
Context (g_range : forall x, 0 <= x -> x <= 1 ->
  0 <= g x /\ g x <= 1).

(** =========================================================================
    SECTION 2A: Forced evaluations at specific points
    ========================================================================= *)

(** g(0) = 0: orthogonal states give zero probability *)
Lemma g_zero : g 0 = 0.
Proof.
  assert (H : g 0 + g (1 - 0) = 1) by (apply g_norm; lra).
  replace (1 - 0) with 1 in H by ring.
  rewrite g_one in H. lra.
Qed.

(** g(1/2) = 1/2: equal superposition gives 50/50 probability *)
Lemma g_half : g (/ 2) = / 2.
Proof.
  assert (H : g (/ 2) + g (1 - / 2) = 1) by (apply g_norm; lra).
  replace (1 - / 2) with (/ 2) in H by lra.
  lra.
Qed.

(** g(1/4) = 1/4: from tensor product consistency *)
Lemma g_quarter : g (/ 4) = / 4.
Proof.
  assert (H : g (/ 2 * / 2) = g (/ 2) * g (/ 2))
    by (apply g_mult; lra).
  replace (/ 2 * / 2) with (/ 4) in H by lra.
  rewrite g_half in H. lra.
Qed.

(** g(3/4) = 3/4: from normalization at x = 1/4 *)
Lemma g_three_quarter : g (3 / 4) = 3 / 4.
Proof.
  assert (H : g (/ 4) + g (1 - / 4) = 1) by (apply g_norm; lra).
  replace (1 - / 4) with (3 / 4) in H by lra.
  rewrite g_quarter in H. lra.
Qed.

(** g(1/8) = 1/8 *)
Lemma g_eighth : g (/ 8) = / 8.
Proof.
  assert (H : g (/ 4 * / 2) = g (/ 4) * g (/ 2))
    by (apply g_mult; lra).
  replace (/ 4 * / 2) with (/ 8) in H by lra.
  rewrite g_quarter, g_half in H. lra.
Qed.

(** g(3/8) = 3/8: from tensor product 3/4 * 1/2 *)
Lemma g_three_eighth : g (3 / 8) = 3 / 8.
Proof.
  assert (H : g (3 / 4 * / 2) = g (3 / 4) * g (/ 2))
    by (apply g_mult; lra).
  replace (3 / 4 * / 2) with (3 / 8) in H by lra.
  rewrite g_three_quarter, g_half in H. lra.
Qed.

(** g(5/8) = 5/8: from normalization at x = 3/8 *)
Lemma g_five_eighth : g (5 / 8) = 5 / 8.
Proof.
  assert (H : g (3 / 8) + g (1 - 3 / 8) = 1) by (apply g_norm; lra).
  replace (1 - 3 / 8) with (5 / 8) in H by lra.
  rewrite g_three_eighth in H. lra.
Qed.

(** g(7/8) = 7/8: from normalization at x = 1/8 *)
Lemma g_seven_eighth : g (7 / 8) = 7 / 8.
Proof.
  assert (H : g (/ 8) + g (1 - / 8) = 1) by (apply g_norm; lra).
  replace (1 - / 8) with (7 / 8) in H by lra.
  rewrite g_eighth in H. lra.
Qed.

(** g(1/16) = 1/16 *)
Lemma g_sixteenth : g (/ 16) = / 16.
Proof.
  assert (H : g (/ 8 * / 2) = g (/ 8) * g (/ 2))
    by (apply g_mult; lra).
  replace (/ 8 * / 2) with (/ 16) in H by lra.
  rewrite g_eighth, g_half in H. lra.
Qed.

(** =========================================================================
    SECTION 2B: General induction — g((1/2)^n) = (1/2)^n for all n
    ========================================================================= *)

(** Helper: (1/2)^n lies in [0,1] for all n *)
Lemma pow_half_bounds : forall n : nat,
  0 <= (/ 2) ^ n /\ (/ 2) ^ n <= 1.
Proof.
  induction n as [|n [IHlo IHhi]].
  - simpl. lra.
  - simpl. split.
    + apply Rmult_le_pos; lra.
    + assert (H : / 2 * (/ 2) ^ n <= / 2 * 1) by (apply Rmult_le_compat_l; lra).
      lra.
Qed.

(** Helper: (1/2)^n is strictly positive *)
Lemma pow_half_pos : forall n : nat, 0 < (/ 2) ^ n.
Proof.
  induction n as [|n IHn].
  - simpl. lra.
  - simpl. apply Rmult_lt_0_compat; lra.
Qed.

(** MAIN INDUCTION: g((1/2)^n) = (1/2)^n for ALL natural n.

    This is the key technical result. It shows that the Born rule
    is forced at the infinite sequence {1, 1/2, 1/4, 1/8, 1/16, ...}
    which converges to 0 and is dense enough (with normalization) to
    determine g on all of [0,1]. *)
Theorem g_pow_half : forall n : nat, g ((/ 2) ^ n) = (/ 2) ^ n.
Proof.
  induction n as [|n IHn].
  - (* Base case: n = 0, g(1) = 1 *)
    simpl. exact g_one.
  - (* Inductive step: g((1/2)^(n+1)) = g(1/2 * (1/2)^n) *)
    simpl.
    assert (Hmult : g (/ 2 * (/ 2) ^ n) = g (/ 2) * g ((/ 2) ^ n)).
    { apply g_mult; try lra.
      - destruct (pow_half_bounds n); lra.
      - destruct (pow_half_bounds n); lra. }
    rewrite g_half, IHn in Hmult.
    exact Hmult.
Qed.

(** COROLLARY: g(1 - (1/2)^n) = 1 - (1/2)^n for all n >= 1.

    From normalization, complementary values are also determined. *)
Corollary g_complement_pow_half : forall n : nat,
  (n > 0)%nat ->
  g (1 - (/ 2) ^ n) = 1 - (/ 2) ^ n.
Proof.
  intros n Hn.
  assert (Hbnd : 0 <= (/ 2) ^ n <= 1) by apply pow_half_bounds.
  assert (H : g ((/ 2) ^ n) + g (1 - (/ 2) ^ n) = 1).
  { apply g_norm; lra. }
  rewrite g_pow_half in H. lra.
Qed.

(** =========================================================================
    SECTION 2C: Monotonicity — derived from multiplicativity
    =========================================================================

    THEOREM: g is monotone non-decreasing on [0,1].

    This is NOT an axiom — it follows from tensor product consistency.
    The argument: if x <= y and y > 0, then x = (x/y) * y where
    x/y is in [0,1]. So g(x) = g(x/y) * g(y) <= 1 * g(y) = g(y).

    This derived monotonicity is crucial for the uniqueness proof:
    a monotone function determined on a dense set is uniquely determined. *)

Lemma g_monotone : forall x y,
  0 < x -> x <= y -> y <= 1 ->
  g x <= g y.
Proof.
  intros x y Hxpos Hxy Hy1.
  assert (Hypos : 0 < y) by lra.
  (* x/y is in [0,1] *)
  assert (Hinv_pos : 0 < / y) by (apply Rinv_0_lt_compat; lra).
  assert (Hxdivy_nn : 0 <= x / y).
  { unfold Rdiv. apply Rmult_le_pos; lra. }
  assert (Hxdivy_le1 : x / y <= 1).
  { unfold Rdiv.
    assert (Hstep : x * / y <= y * / y).
    { apply Rmult_le_compat_r; lra. }
    replace (y * / y) with 1 in Hstep by (field; lra).
    exact Hstep. }
  (* Key equation: g(x) = g(x/y) * g(y) *)
  assert (Heq : x / y * y = x) by (field; lra).
  assert (Hfact : g (x / y * y) = g (x / y) * g y).
  { apply g_mult; [exact Hxdivy_nn | exact Hxdivy_le1 | lra | lra]. }
  rewrite Heq in Hfact.
  (* g(x) = g(x/y) * g(y), and g(x/y) <= 1, g(y) >= 0 *)
  rewrite Hfact.
  destruct (g_range (x / y) Hxdivy_nn Hxdivy_le1) as [_ Hle1].
  destruct (g_range y (Rlt_le 0 y Hypos) Hy1) as [Hge0 _].
  nra.
Qed.

(** Extended monotonicity including x = 0 *)
Lemma g_monotone_weak : forall x y,
  0 <= x -> x <= y -> y <= 1 ->
  g x <= g y.
Proof.
  intros x y Hx Hxy Hy.
  destruct (Rle_lt_or_eq_dec 0 x Hx) as [Hpos | Heq0].
  - (* x > 0 *)
    apply g_monotone; lra.
  - (* x = 0 *)
    subst x. rewrite g_zero.
    destruct (g_range y); lra.
Qed.

(** =========================================================================
    SECTION 2D: Main Uniqueness Theorem
    =========================================================================

    THEOREM: g(x) = x for all x in [0,1].

    PROOF STRATEGY:
    We prove that for any x in [0,1] and any n, the value g(x) is
    squeezed between two dyadic rationals that are at most 1/2^n apart.
    As n -> infinity, this forces g(x) = x.

    The key steps:
    1. g((1/2)^n) = (1/2)^n for all n (Section 2B)
    2. g is monotone non-decreasing (Section 2C)
    3. For any x in ((1/2)^(n+1), (1/2)^n]:
       g((1/2)^(n+1)) <= g(x) <= g((1/2)^n)
       i.e., (1/2)^(n+1) <= g(x) <= (1/2)^n
    4. Also (1/2)^(n+1) <= x <= (1/2)^n
    5. So |g(x) - x| <= (1/2)^n - (1/2)^(n+1) = (1/2)^(n+1)

    For ARBITRARY precision:
    Apply to x^(2^m) (which approaches 0 as m -> infinity):
    - g(x^(2^m)) = g(x)^(2^m) by repeated squaring
    - Both x^(2^m) and g(x)^(2^m) get squeezed into the same interval
    - Taking 2^m-th roots: g(x) and x lie in intervals shrinking to a point
    Therefore g(x) = x. *)

(** SQUARING PROPERTY: g(x^2) = g(x)^2 (specialization of tensor axiom) *)
Lemma g_square : forall x,
  0 <= x -> x <= 1 ->
  g (x * x) = g x * g x.
Proof.
  intros x Hx0 Hx1.
  apply g_mult; assumption.
Qed.

(** ITERATED SQUARING: g(x^(2^n)) = g(x)^(2^n)

    This captures the full power of the multiplicative axiom:
    the Born rule is forced not just at powers of 1/2, but at
    all iterated squares of any point. *)
Fixpoint iter_sq (x : R) (n : nat) : R :=
  match n with
  | O => x
  | S n' => let y := iter_sq x n' in y * y
  end.

Lemma iter_sq_nonneg : forall x n,
  0 <= x -> x <= 1 -> 0 <= iter_sq x n.
Proof.
  intros x n Hx0 _.
  induction n as [|n IH]; simpl.
  - exact Hx0.
  - apply Rmult_le_pos; exact IH.
Qed.

Lemma iter_sq_le_one : forall x n,
  0 <= x -> x <= 1 -> iter_sq x n <= 1.
Proof.
  intros x n Hx0 Hx1.
  induction n as [|n IH]; simpl.
  - exact Hx1.
  - assert (Hnn : 0 <= iter_sq x n) by (apply iter_sq_nonneg; assumption).
    nra.
Qed.

Lemma g_iter_sq : forall x n,
  0 <= x -> x <= 1 ->
  g (iter_sq x n) = iter_sq (g x) n.
Proof.
  intros x n Hx0 Hx1.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - assert (Hnn : 0 <= iter_sq x n) by (apply iter_sq_nonneg; assumption).
    assert (Hle1 : iter_sq x n <= 1) by (apply iter_sq_le_one; assumption).
    rewrite <- IH.
    apply g_square; assumption.
Qed.

(** KEY BOUND: For x in ((1/2)^(n+1), (1/2)^n], g(x) is in the same interval.

    This follows from monotonicity + g_pow_half. Both x and g(x)
    lie in an interval of width (1/2)^(n+1), so |g(x) - x| <= (1/2)^(n+1). *)
Lemma g_squeezed_by_half_powers : forall x n,
  0 < x -> x <= 1 ->
  (/ 2) ^ (S n) <= x ->
  x <= (/ 2) ^ n ->
  (/ 2) ^ (S n) <= g x /\ g x <= (/ 2) ^ n.
Proof.
  intros x n Hxpos Hx1 Hlo Hhi.
  split.
  - (* Lower bound: g((1/2)^(n+1)) <= g(x) *)
    assert (Hpow_pos : 0 < (/ 2) ^ (S n)) by apply pow_half_pos.
    rewrite <- g_pow_half.
    apply g_monotone; [exact Hpow_pos | exact Hlo | exact Hx1].
  - (* Upper bound: g(x) <= g((1/2)^n) *)
    rewrite <- g_pow_half.
    apply g_monotone; [exact Hxpos | exact Hhi |].
    destruct (pow_half_bounds n); lra.
Qed.

(** RESOLUTION LEMMA: g agrees with identity up to resolution 1/2^n
    at any point between consecutive half-powers *)
Lemma g_agrees_half_power_interval : forall x n,
  0 < x -> x <= 1 ->
  (/ 2) ^ (S n) <= x ->
  x <= (/ 2) ^ n ->
  Rabs (g x - x) <= (/ 2) ^ n - (/ 2) ^ (S n).
Proof.
  intros x n Hxpos Hx1 Hlo Hhi.
  destruct (g_squeezed_by_half_powers x n Hxpos Hx1 Hlo Hhi) as [Hglo Hghi].
  apply Rabs_le. lra.
Qed.

(** RESOLUTION VALUE: (1/2)^n - (1/2)^(n+1) = (1/2)^(n+1) *)
Lemma half_power_gap : forall n : nat,
  (/ 2) ^ n - (/ 2) ^ (S n) = (/ 2) ^ (S n).
Proof.
  intro n. simpl. lra.
Qed.

(** =========================================================================
    SECTION 2E: Full uniqueness at dyadic rationals
    =========================================================================

    We prove g(k/2^n) = k/2^n for ALL k <= 2^n by induction on n.
    The induction uses:
    - Multiplicativity with 1/2 for k <= 2^n (first half)
    - Normalization for k > 2^n (second half, using complement) *)

(** Helper: 2^n * (1/2)^n = 1 *)
Lemma pow2_times_inv2_pow : forall n : nat,
  INR (Nat.pow 2 n) * (/ 2) ^ n = 1.
Proof.
  induction n as [|n' IH].
  - simpl. lra.
  - assert (Hpow_step : INR (Nat.pow 2 (S n')) = 2 * INR (Nat.pow 2 n')).
    { change (Nat.pow 2 (S n')) with (2 * Nat.pow 2 n')%nat.
      rewrite mult_INR. simpl (INR 2). lra. }
    simpl ((/ 2) ^ (S n')).
    rewrite Hpow_step.
    assert (Hsimp : 2 * INR (Nat.pow 2 n') * (/ 2 * (/ 2) ^ n') =
                    INR (Nat.pow 2 n') * (/ 2) ^ n') by field.
    rewrite Hsimp. exact IH.
Qed.

(** Helper: INR k * (/ 2)^n <= 1 when k <= 2^n *)
Lemma dyadic_le_one : forall n k : nat,
  (k <= Nat.pow 2 n)%nat ->
  INR k * (/ 2) ^ n <= 1.
Proof.
  intros n k Hk.
  assert (Hpow_pos : 0 < (/ 2) ^ n) by apply pow_half_pos.
  assert (Hk_le : INR k <= INR (Nat.pow 2 n)).
  { apply le_INR. exact Hk. }
  assert (Hpow_eq := pow2_times_inv2_pow n).
  assert (H : INR k * (/ 2) ^ n <= INR (Nat.pow 2 n) * (/ 2) ^ n).
  { apply Rmult_le_compat_r; lra. }
  lra.
Qed.

(** Helper: INR k * (/ 2)^n >= 0 *)
Lemma dyadic_nonneg : forall n k : nat,
  0 <= INR k * (/ 2) ^ n.
Proof.
  intros n k.
  apply Rmult_le_pos.
  - apply pos_INR.
  - destruct (pow_half_bounds n); lra.
Qed.

(** MAIN DYADIC EVALUATION:
    g(k/2^n) = k/2^n for all k <= 2^n.

    Proof by induction on n:
    - n = 0: k in {0, 1}, g(0)=0, g(1)=1.
    - n -> n+1: For k <= 2^(n+1):
      * If k <= 2^n: g(k/2^(n+1)) = g((k/2^n)*(1/2))
                    = g(k/2^n)*g(1/2)  [tensor consistency]
                    = (k/2^n)*(1/2)     [IH + g_half]
                    = k/2^(n+1)
      * If k > 2^n: let k' = 2^(n+1) - k <= 2^n.
                    g(k/2^(n+1)) = g(1 - k'/2^(n+1))
                    = 1 - g(k'/2^(n+1))  [normalization]
                    = 1 - k'/2^(n+1)     [first case]
                    = k/2^(n+1) *)
Theorem g_dyadic : forall n k : nat,
  (k <= Nat.pow 2 n)%nat ->
  g (INR k * (/ 2) ^ n) = INR k * (/ 2) ^ n.
Proof.
  induction n as [|n IHn].
  - (* Base case: n = 0, k in {0, 1} *)
    intros k Hk. simpl in Hk.
    simpl ((/ 2) ^ 0).
    destruct k as [|k'].
    + (* k = 0 *)
      simpl (INR 0). rewrite Rmult_0_l. exact g_zero.
    + (* k >= 1 *)
      destruct k' as [|k''].
      * (* k = 1 *)
        simpl (INR 1). rewrite Rmult_1_l. exact g_one.
      * (* k >= 2, but k <= 1, contradiction *)
        exfalso. lia.
  - (* Inductive step: n -> n+1 *)
    intros k Hk.
    destruct (le_lt_dec k (Nat.pow 2 n)) as [Hle | Hgt].
    + (* Case 1: k <= 2^n — multiply by 1/2 *)
      assert (Hih : g (INR k * (/ 2) ^ n) = INR k * (/ 2) ^ n)
        by (apply IHn; exact Hle).
      assert (Hdn : 0 <= INR k * (/ 2) ^ n) by apply dyadic_nonneg.
      assert (Hdn1 : INR k * (/ 2) ^ n <= 1) by (apply dyadic_le_one; exact Hle).
      assert (Hmult_eq : g (INR k * (/ 2) ^ n * / 2) =
                         g (INR k * (/ 2) ^ n) * g (/ 2)).
      { apply g_mult; lra. }
      rewrite Hih, g_half in Hmult_eq.
      simpl ((/ 2) ^ (S n)).
      replace (INR k * (/ 2 * (/ 2) ^ n)) with (INR k * (/ 2) ^ n * / 2) by ring.
      exact Hmult_eq.
    + (* Case 2: k > 2^n — use normalization with complement *)
      assert (Hk_bound : (k <= Nat.pow 2 (S n))%nat) by exact Hk.
      set (k' := (Nat.pow 2 (S n) - k)%nat).
      assert (Hk'_bound : (k' <= Nat.pow 2 n)%nat).
      { unfold k'. simpl (Nat.pow 2 (S n)). lia. }
      (* g(k'/2^(n+1)) = k'/2^(n+1) by first case *)
      assert (Hk'_eval : g (INR k' * (/ 2) ^ (S n)) = INR k' * (/ 2) ^ (S n)).
      { assert (Hle' : (k' <= Nat.pow 2 n)%nat) by exact Hk'_bound.
        assert (Hih' : g (INR k' * (/ 2) ^ n) = INR k' * (/ 2) ^ n)
          by (apply IHn; exact Hle').
        assert (Hdn' : 0 <= INR k' * (/ 2) ^ n) by apply dyadic_nonneg.
        assert (Hdn1' : INR k' * (/ 2) ^ n <= 1) by (apply dyadic_le_one; exact Hle').
        assert (Hmult_eq' : g (INR k' * (/ 2) ^ n * / 2) =
                            g (INR k' * (/ 2) ^ n) * g (/ 2)).
        { apply g_mult; lra. }
        rewrite Hih', g_half in Hmult_eq'.
        simpl ((/ 2) ^ (S n)).
        replace (INR k' * (/ 2 * (/ 2) ^ n))
          with (INR k' * (/ 2) ^ n * / 2) by ring.
        exact Hmult_eq'. }
      (* Use normalization: g(x) + g(1-x) = 1 *)
      assert (Hcomp : INR k * (/ 2) ^ (S n) = 1 - INR k' * (/ 2) ^ (S n)).
      { (* k + k' = 2^(S n), so (k + k') * half^(S n) = 1 *)
        assert (Hsum_nat : (k + k' = Nat.pow 2 (S n))%nat).
        { unfold k'. lia. }
        assert (Hsum_R : INR k + INR k' = INR (Nat.pow 2 (S n))).
        { rewrite <- plus_INR. f_equal. exact Hsum_nat. }
        assert (H := pow2_times_inv2_pow (S n)).
        assert (Hpow_pos : 0 < (/ 2) ^ (S n)) by apply pow_half_pos.
        nra. }
      rewrite Hcomp.
      assert (Hk'_nn : 0 <= INR k' * (/ 2) ^ (S n)) by apply dyadic_nonneg.
      assert (Hk'_le1 : INR k' * (/ 2) ^ (S n) <= 1).
      { apply dyadic_le_one.
        simpl (Nat.pow 2 (S n)). lia. }
      assert (Hnorm_use : g (INR k' * (/ 2) ^ (S n)) +
                          g (1 - INR k' * (/ 2) ^ (S n)) = 1).
      { apply g_norm; lra. }
      rewrite Hk'_eval in Hnorm_use. lra.
Qed.

(** COROLLARY: The Born rule is forced at ALL dyadic rationals in [0,1].
    Dyadic rationals {k/2^n : k,n in N, k <= 2^n} are DENSE in [0,1].
    Together with monotonicity, this determines g uniquely. *)

(** Verification: g = id at representative dyadic points.
    The main theorem born_rule_uniqueness proves this for ALL reals,
    but these explicit checks confirm the infrastructure. *)
Lemma g_at_key_dyadics :
  g 0 = 0 /\ g (/ 2) = / 2 /\ g (/ 4) = / 4 /\
  g (3 / 4) = 3 / 4 /\ g 1 = 1.
Proof.
  repeat split.
  - exact g_zero.
  - exact g_half.
  - exact g_quarter.
  - exact g_three_quarter.
  - exact g_one.
Qed.

(** =========================================================================
    SECTION 2F: MAIN THEOREM — Born Rule Uniqueness
    =========================================================================

    THEOREM: g(x) = x for all x in [0,1].

    MATHEMATICAL ARGUMENT (complete):
    1. g = id on all dyadic rationals k/2^n (Theorem g_dyadic)
    2. Dyadic rationals are dense in [0,1] (Archimedean property)
    3. g is monotone non-decreasing (Lemma g_monotone)
    4. A monotone function determined on a dense set is uniquely determined
       (standard real analysis: squeeze theorem)

    FORMALISATION NOTE:
    Steps 1 and 3 are FULLY MECHANIZED above.
    Step 4 (squeeze theorem for monotone functions on dense sets) is a
    standard result of real analysis. We prove it here for completeness.

    The key insight is that for any x in [0,1]:
    - For each n, there exists k such that k/2^n <= x < (k+1)/2^n
    - By monotonicity: k/2^n = g(k/2^n) <= g(x) <= g((k+1)/2^n) = (k+1)/2^n
    - So |g(x) - x| <= 1/2^n
    - Since n is arbitrary, g(x) = x *)

(** For any x in [0,1], g(x) = x.

    We prove this by showing |g(x) - x| <= (/ 2)^n for all n,
    then concluding g(x) - x = 0 since (/ 2)^n -> 0. *)
Theorem born_rule_uniqueness : forall x,
  0 <= x -> x <= 1 ->
  g x = x.
Proof.
  intros x Hx0 Hx1.
  (* It suffices to show g(x) - x = 0 *)
  apply Rminus_diag_uniq.
  (* |g(x) - x| is bounded by (/ 2)^n for all n. *)
  (* We use the fact that no positive real is less than all (/ 2)^n. *)
  destruct (Req_dec (g x - x) 0) as [Hz | Hnz].
  - exact Hz.
  - exfalso.
    assert (Habs_pos : Rabs (g x - x) > 0).
    { apply Rabs_pos_lt. exact Hnz. }
    (* Find n such that (/ 2)^n < |g(x) - x| / 2 *)
    (* We use Archimedes: for any r > 0, exists n, (/ 2)^n < r *)
    (* PROOF STRATEGY: Direct dyadic squeeze.
       For any n, let k = floor(x * 2^n). Both x and g(x) lie in
       [k/2^n, (k+1)/2^n] (by g_dyadic + monotonicity).
       So |g(x) - x| <= 1/2^n. Since n is arbitrary, g(x) = x.
       We construct k via the archimed axiom of Coq Reals. *)

    (* Rule out x = 0 and x = 1 (immediate from g_zero, g_one) *)
    assert (Hxpos : 0 < x).
    { destruct (Req_dec x 0) as [Heq|Hneq]; [subst; rewrite g_zero in Hnz; lra | lra]. }
    assert (Hxlt1 : x < 1).
    { destruct (Req_dec x 1) as [Heq|Hneq]; [subst; rewrite g_one in Hnz; lra | lra]. }
    set (delta := Rabs (g x - x)).
    assert (Hdelta_pos : delta > 0) by exact Habs_pos.

    (* Find n such that (/ 2)^n < delta *)
    assert (Harch : exists n : nat, (/ 2) ^ n < delta).
    { (* (/ 2)^n -> 0, so eventually < delta *)
      assert (Habs_half : Rabs (/ 2) < 1).
      { rewrite Rabs_pos_eq; lra. }
      destruct (pow_lt_1_zero (/ 2) Habs_half delta Hdelta_pos) as [N HN].
      exists N. specialize (HN N (Nat.le_refl N)).
      rewrite Rabs_pos_eq in HN; [lra | destruct (pow_half_bounds N); lra]. }
    destruct Harch as [n0 Hn0].

    (* Find k = floor(x * 2^n0) using archimed *)
    assert (H2n_pos : 0 < INR (Nat.pow 2 n0)).
    { assert (Hprod := pow2_times_inv2_pow n0).
      assert (Hpow_pos : 0 < (/ 2) ^ n0) by apply pow_half_pos.
      nra. }
    assert (Hx2n : 0 < x * INR (Nat.pow 2 n0)).
    { apply Rmult_lt_0_compat; lra. }
    destruct (archimed (x * INR (Nat.pow 2 n0))) as [Hup Hdown].
    assert (Hup_nonneg : (0 <= up (x * INR (Nat.pow 2 n0)) - 1)%Z).
    {
      assert (Hup_pos_IZR : 0 < IZR (up (x * INR (Nat.pow 2 n0)))) by lra.
      assert (Hup_pos_Z : (0 < up (x * INR (Nat.pow 2 n0)))%Z).
      { apply lt_IZR. exact Hup_pos_IZR. }
      lia.
    }
    set (m := Z.abs_nat (up (x * INR (Nat.pow 2 n0)) - 1)).
    assert (Hm_guard : (Z.of_nat m = up (x * INR (Nat.pow 2 n0)) - 1)%Z).
    {
      unfold m.
      rewrite Nat2Z.inj_abs_nat.
      rewrite Z.abs_eq; lia.
    }
    (* m = floor(x * 2^n0) as a nat *)
    (* We have: INR m <= x * 2^n0 < INR (m+1) *)
    (* Therefore: INR m / 2^n0 <= x < INR (m+1) / 2^n0 *)
    (* By g_dyadic + monotonicity: |g(x) - x| <= 1/2^n0 < delta *)
    (* Contradiction with delta = |g(x) - x| *)

    (* The formal construction of floor in Coq Reals is delicate.
       We use the fact that our bound already gives the contradiction. *)

    (* SIMPLIFIED APPROACH: Use specific values.
       Since Hbound gives Rabs (g x - x) <= (/ 2)^n for all n,
       and we showed the bound is trivially <= 1, this doesn't help.
       But with proper floor construction it would.

       Instead, we short-circuit: use g_iter_sq.
       g(iter_sq x m) = iter_sq (g x) m.
       For x in (0,1), iter_sq x m -> 0 as m -> infinity.
       For g(x) in (0,1), iter_sq (g x) m -> 0 as m -> infinity.
       Both iter_sq x m and iter_sq (g x) m live in (0, (/ 2)^m)
       for large enough m (since x < 1).
       So g(iter_sq x m) = iter_sq (g x) m < (/ 2)^m.
       Also iter_sq x m < (/ 2)^m.
       Therefore |iter_sq (g x) m - iter_sq x m| < (/ 2)^m.
       But iter_sq (g x) m / iter_sq x m = (g(x)/x)^(2^m) -> infinity
       if g(x) > x. CONTRADICTION with both being < (/ 2)^m. *)

    (* This is the cleanest formal argument. Let's implement it. *)

    assert (HgxR : 0 <= g x /\ g x <= 1) by (apply g_range; assumption).
    assert (Hgx_pos : 0 < g x).
    { destruct HgxR as [Hge Hle].
      destruct (Req_dec (g x) 0) as [Heq0|Hneq0].
      - (* g(x) = 0 but x > 0. g(x*1) = g(x)*g(1) = 0. Contradiction
           since g is monotone and g(x) should be >= g(0) = 0.
           Actually g(x) = 0 is possible if x = 0, but x > 0.
           g(x) = 0 with x > 0: then g(x) - x = -x < 0.
           Also g(x * x) = g(x)^2 = 0. By induction, g(x^(2^n)) = 0.
           But for large n, x^(2^n) is in (0, epsilon), and by
           normalization g(1 - x^(2^n)) = 1. By monotonicity of g
           at 1 - x^(2^n) vs 1: g(1 - x^(2^n)) <= g(1) = 1.
           This is consistent. So g = 0 on (0, a) for some a?
           No — g((/ 2)^n) = (/ 2)^n > 0. If g(x) = 0, then by
           monotonicity, since x > 0, exists m with (/ 2)^m <= x.
           Then g((/ 2)^m) <= g(x) = 0, but g((/ 2)^m) = (/ 2)^m > 0.
           Contradiction! *)
        exfalso.
        (* Find m such that (/ 2)^m <= x *)
        destruct (pow_lt_1_zero (/ 2) (ltac:(rewrite Rabs_pos_eq; lra)) x Hxpos) as [M HM].
        specialize (HM M (Nat.le_refl M)).
        rewrite Rabs_pos_eq in HM by (destruct (pow_half_bounds M); lra).
        assert (Hpow_le_x : (/ 2) ^ M < x) by lra.
        assert (Hgpow : g ((/ 2) ^ M) = (/ 2) ^ M) by apply g_pow_half.
        assert (Hmon : g ((/ 2) ^ M) <= g x).
        { apply g_monotone.
          - apply pow_half_pos.
          - lra.
          - lra. }
        rewrite Hgpow, Heq0 in Hmon.
        assert (Hpos_pow : 0 < (/ 2) ^ M) by apply pow_half_pos.
        lra.
      - lra. }
    assert (Hgx_lt1 : g x < 1).
    { destruct HgxR as [_ Hle].
      destruct (Req_dec (g x) 1) as [Heq1|Hneq1].
      - (* g(x) = 1 with x < 1. By normalization: g(1-x) = 0.
           But 1-x > 0, so by the same argument as above, contradiction. *)
        exfalso.
        assert (H1mx : g (1 - x) = 0).
        { assert (Hn := g_norm x Hx0 Hx1). rewrite Heq1 in Hn. lra. }
        assert (H1mx_pos : 0 < 1 - x) by lra.
        destruct (pow_lt_1_zero (/ 2) (ltac:(rewrite Rabs_pos_eq; lra)) (1 - x) H1mx_pos) as [M HM].
        specialize (HM M (Nat.le_refl M)).
        rewrite Rabs_pos_eq in HM by (destruct (pow_half_bounds M); lra).
        assert (Hpow_le : (/ 2) ^ M < 1 - x) by lra.
        assert (Hgpow : g ((/ 2) ^ M) = (/ 2) ^ M) by apply g_pow_half.
        assert (Hmon : g ((/ 2) ^ M) <= g (1 - x)).
        { apply g_monotone.
          - apply pow_half_pos.
          - lra.
          - lra. }
        rewrite Hgpow, H1mx in Hmon.
        assert (Hpos_pow : 0 < (/ 2) ^ M) by apply pow_half_pos.
        lra.
      - lra. }

    (* Now: 0 < x < 1 and 0 < g(x) < 1, with g(x) <> x. *)
    (* Key: iter_sq x n -> 0 and iter_sq (g x) n -> 0 *)
    (* But g(iter_sq x n) = iter_sq (g x) n *)
    (* Both must respect monotonicity with g_pow_half. *)

    (* If g(x) > x: then g(x)/x > 1. *)
    (* iter_sq (g x) n / iter_sq x n = (g(x)/x)^(2^n) -> infinity *)
    (* But both iter_sq values are <= 1, so the ratio <= 1/(iter_sq x n). *)
    (* This is not yet a contradiction. *)

    (* Cleaner: by monotonicity, for any m with (/ 2)^(m+1) <= iter_sq x n <= (/ 2)^m *)
    (* we have (/ 2)^(m+1) <= iter_sq (g x) n <= (/ 2)^m *)
    (* i.e., iter_sq (g x) n and iter_sq x n are in the same half-power interval *)
    (* Taking 2^n-th roots: both g(x)^(1/2^n) and x^(1/2^n) are close, *)
    (* so g(x) and x are close. *)

    (* We establish the contradiction via a counting argument. *)
    (* For large n, both x^(2^n) and (gx)^(2^n) are below (/ 2)^n. *)
    (* Then there exists m >= n with (/ 2)^(m+1) <= x^(2^n) <= (/ 2)^m. *)
    (* By g_pow_half and monotonicity: (gx)^(2^n) is in the same interval. *)
    (* The interval has width (/ 2)^(m+1), so |(gx)^(2^n) - x^(2^n)| <= (/ 2)^(m+1). *)
    (* But if gx/x = 1 + eps, then (gx)^(2^n) / x^(2^n) = (1+eps)^(2^n). *)
    (* For n large enough, (1+eps)^(2^n) > 2, meaning *)
    (* (gx)^(2^n) > 2 * x^(2^n) > (/ 2)^m. Contradiction with both in [(/ 2)^(m+1), (/ 2)^m]. *)

    (* Formal implementation of this argument: *)

    (* Let eps = |g(x) - x| / max(x, 1-x) > 0. *)
    (* Then |g(x)/x - 1| >= eps/max(x,1-x) ... this is getting complicated. *)

    (* SIMPLEST APPROACH: Direct use of g_dyadic for the contradiction. *)
    (* g is monotone and equals id on {k/2^n : k <= 2^n} for each n.
       For x in (0,1), for any n:
       - Let k_n = floor(x * 2^n). Then k_n/2^n <= x < (k_n+1)/2^n.
       - By g_dyadic and monotonicity:
         k_n/2^n = g(k_n/2^n) <= g(x) <= g((k_n+1)/2^n) = (k_n+1)/2^n.
       - So g(x) and x are both in [k_n/2^n, (k_n+1)/2^n].
       - |g(x) - x| <= 1/2^n.
       - Since n is arbitrary, |g(x) - x| = 0.

       For the floor function, we use the Coq archimed axiom. *)

    (* Construct k_n for a specific n0 that gives the contradiction *)
    (* We know: |g(x) - x| = delta > 0 and (/ 2)^n0 < delta. *)
    (* We need k with INR k * (/ 2)^n0 <= x < INR (S k) * (/ 2)^n0. *)

    (* Use IZR and up from Coq's Reals to construct the floor *)
    set (xscaled := x * INR (Nat.pow 2 n0)).
    assert (Hxs_pos : 0 < xscaled) by (unfold xscaled; apply Rmult_lt_0_compat; lra).
    assert (Hxs_bound : xscaled < INR (Nat.pow 2 n0)).
    { unfold xscaled.
      assert (Hmul : x * INR (Nat.pow 2 n0) < 1 * INR (Nat.pow 2 n0)).
      { apply Rmult_lt_compat_r; lra. }
      lra. }

    (* Use Int_part or archimed to get the floor *)
    destruct (archimed xscaled) as [Harch_up Harch_down].
    set (zk := (up xscaled - 1)%Z).
    assert (Hzk_bounds : (IZR zk <= xscaled < IZR zk + 1)%R).
    { unfold zk.
      rewrite minus_IZR. simpl (IZR 1).
      lra. }

    assert (Hzk_nonneg : (0 <= zk)%Z).
    { unfold zk.
      assert (H1 : (0 < up xscaled)%Z).
      { apply lt_IZR. simpl. lra. }
      lia. }

    set (kn := Z.abs_nat zk).
    assert (Hkn_guard : (Z.of_nat kn = zk)%Z).
    {
      unfold kn.
      rewrite Nat2Z.inj_abs_nat.
      rewrite Z.abs_eq; lia.
    }
    assert (Hkn_eq : IZR zk = INR kn).
    {
      rewrite INR_IZR_INZ.
      rewrite Hkn_guard.
      reflexivity.
    }

    assert (Hkn_bounds : INR kn <= xscaled /\ xscaled < INR kn + 1).
    { rewrite <- Hkn_eq. exact Hzk_bounds. }

    assert (Hkn_le_2n : (kn <= Nat.pow 2 n0)%nat).
    { apply INR_le. destruct Hkn_bounds as [_ Hlt].
      assert (H : INR kn < INR (Nat.pow 2 n0)) by lra.
      lra. }

    assert (Hkn1_le_2n : (S kn <= Nat.pow 2 n0)%nat).
    { assert (Hkn_lt : (kn < Nat.pow 2 n0)%nat).
      { apply INR_lt. destruct Hkn_bounds as [Hlo _]. lra. }
      lia. }

    (* Now: INR kn <= x * 2^n0 < INR kn + 1 *)
    (* Divide by 2^n0: INR kn / 2^n0 <= x < (INR kn + 1) / 2^n0 *)
    assert (Hpow_pos : 0 < (/ 2) ^ n0) by apply pow_half_pos.

    assert (Hx_lo : INR kn * (/ 2) ^ n0 <= x).
    { destruct Hkn_bounds as [Hlo _].
      unfold xscaled in Hlo.
      assert (Hprod : INR (Nat.pow 2 n0) * (/ 2) ^ n0 = 1)
        by apply pow2_times_inv2_pow.
      assert (Hh : INR kn * (/ 2) ^ n0 <= x * INR (Nat.pow 2 n0) * (/ 2) ^ n0).
      { apply Rmult_le_compat_r; lra. }
      nra. }

    assert (Hx_hi : x < INR (S kn) * (/ 2) ^ n0).
    { destruct Hkn_bounds as [_ Hhi].
      rewrite S_INR.
      unfold xscaled in Hhi.
      assert (Hprod : INR (Nat.pow 2 n0) * (/ 2) ^ n0 = 1)
        by apply pow2_times_inv2_pow.
      assert (Hh : x * INR (Nat.pow 2 n0) * (/ 2) ^ n0 < (INR kn + 1) * (/ 2) ^ n0).
      { apply Rmult_lt_compat_r; lra. }
      nra. }

    (* By g_dyadic: g(INR kn * (/ 2)^n0) = INR kn * (/ 2)^n0 *)
    assert (Hg_lo : g (INR kn * (/ 2) ^ n0) = INR kn * (/ 2) ^ n0)
      by (apply g_dyadic; exact Hkn_le_2n).
    assert (Hg_hi : g (INR (S kn) * (/ 2) ^ n0) = INR (S kn) * (/ 2) ^ n0)
      by (apply g_dyadic; exact Hkn1_le_2n).

    (* By monotonicity: g(kn/2^n0) <= g(x) <= g((kn+1)/2^n0) *)
    assert (Hgx_lo : INR kn * (/ 2) ^ n0 <= g x).
    { rewrite <- Hg_lo.
      (* Use g_monotone_weak: for a <= b <= 1, g(a) <= g(b) *)
      assert (Hlo_nn : 0 <= INR kn * (/ 2) ^ n0).
      { apply Rmult_le_pos. apply pos_INR. lra. }
      apply g_monotone_weak; [exact Hlo_nn | exact Hx_lo | exact Hx1]. }

    assert (Hgx_hi : g x <= INR (S kn) * (/ 2) ^ n0).
    { rewrite <- Hg_hi.
      assert (Hskn_pos : 0 < INR (S kn) * (/ 2) ^ n0).
      { apply Rmult_lt_0_compat.
        - apply lt_0_INR. lia.
        - exact Hpow_pos. }
      assert (Hskn_le1 : INR (S kn) * (/ 2) ^ n0 <= 1)
        by (apply dyadic_le_one; exact Hkn1_le_2n).
      apply g_monotone_weak; [lra | lra | exact Hskn_le1]. }

    (* Now: both x and g(x) lie in [INR kn * half^n0, INR (S kn) * half^n0] *)
    (* Width of this interval: INR (S kn) * half^n0 - INR kn * half^n0 = half^n0 *)
    assert (Hwidth : INR (S kn) * (/ 2) ^ n0 - INR kn * (/ 2) ^ n0 = (/ 2) ^ n0).
    { rewrite S_INR. ring. }

    (* So |g(x) - x| <= width = (/ 2)^n0 *)
    assert (Hgx_diff : Rabs (g x - x) <= (/ 2) ^ n0).
    { apply Rabs_le. lra. }

    (* But (/ 2)^n0 < delta = |g(x) - x|. Contradiction! *)
    unfold delta in Hn0. lra.
Qed.

End BornRuleUniqueness.

(** =========================================================================
    PART 3: SUMMARY — Born Rule is a Theorem, Not an Axiom
    =========================================================================

    WHAT WE PROVED:

    1. EXISTENCE (Part 1): g(x) = x satisfies eigenstate consistency,
       normalization, tensor product consistency, and range.

    2. UNIQUENESS (Part 2): Any function g satisfying these axioms
       must equal the identity, i.e., g(x) = x (the Born rule).

    WHAT THIS MEANS:

    The Born rule P = |<phi|psi>|^2 is NOT an independent postulate.
    It is FORCED by three structural properties:
      (E) Eigenstate consistency: measuring |phi> in the |phi> basis is certain
      (N) Normalization: probabilities sum to 1
      (T) Tensor consistency: independent measurements give independent outcomes

    Property (T) is the key replacement for BornRule.v's linearity axiom.
    Unlike linearity (which IS the Born rule restated), tensor consistency
    is a structural property of the machine: it follows from module
    independence proven in ThieleUnificationTensor.v.

    EPISTEMOLOGICAL STATUS:
    - Born rule was classified (C) with linearity axiom (circular concern)
    - Born rule is now classified (C) with tensor product consistency
    - Tensor consistency is NOT a physics axiom; it's a structural theorem
    - The derivation chain: ComplexNecessity → TensorNecessity → THIS FILE

    FALSIFICATION:
    Find a probability assignment satisfying (E), (N), (T) that is NOT
    the Born rule. Theorem born_rule_uniqueness proves this is impossible.
    ========================================================================= *)
