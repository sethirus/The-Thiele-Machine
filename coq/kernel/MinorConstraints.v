(** =========================================================================
    MINOR CONSTRAINTS AND FINE'S THEOREM - Classical CHSH Bound
    =========================================================================

    THEOREM: Factorizable correlations satisfy 3×3 minor constraints,
    which by Fine's theorem imply CHSH ≤ 2 (classical bound).

    This establishes the CLASSICAL BOUND:
      max{CHSH : factorizable correlations} = 2

    Combined with TsirelsonUpperBound.v:
      μ=0 → LOCC → factorizable → minor constraints → CHSH ≤ 2

    STATUS: COMPLETE (Zero admits in critical proof path)
    DATE: February 7, 2026

    CRITICAL PROOF PATH (COMPLETE):
      deterministic_strategy_chsh_bounded → fine_theorem →
      factorizable_CHSH_classical_bound → local_box_CHSH_bound

    NON-CRITICAL ADMITS: NONE

    ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.
Require Import Coq.Logic.FunctionalExtensionality.

Import ListNotations.

From Kernel Require Import BoxCHSH ValidCorrelation ConstructivePSD.

(** =========================================================================
    PART 1: HELPER FUNCTIONS (before opening R_scope)
    ========================================================================= *)

(** sum_n: Finite summation Σ_{i=0}^n f(i)

    WHY: Need explicit finite sums for probability distributions p(λ) and
    expectation values. Standard library doesn't provide the exact interface
    required for factorizable correlations.

    ALGORITHM:
    - Base case: sum_n 0 f = f 0
    - Recursive case: sum_n (S n') f = sum_n n' f + f (S n')
    - Computes Σ_{i=0}^n f(i) by accumulation

    CLAIM: sum_n computes finite sums correctly.

    PROPERTIES:
    - sum_n n (fun _ => 0) = 0 (sum of zeros is zero)
    - sum_n n (fun _ => c) = c * (n+1) (sum of constants)
    - Linearity: sum_n n (fun i => a*f(i) + b*g(i)) = a*sum_n n f + b*sum_n n g

    PHYSICAL MEANING: Probability normalization Σ p(λ) = 1 and expectation
    values E[X] = Σ p(λ)·X(λ) require finite sums over hidden variable states.

    EXAMPLE: sum_n 2 (fun i => R_of_nat i) = 0 + 1 + 2 = 3

    FALSIFICATION: If sum_n gives wrong values for standard sums (arithmetic
    series, geometric series), the factorization proofs break.

    DEPENDENCIES: Coq.Reals.Reals (R type)

    USED BY: is_factorizable, factorizable_cauchy_schwarz *)
Fixpoint sum_n (n : nat) (f : nat -> R) : R :=
  match n with
  | 0 => f 0
  | Datatypes.S n' => (sum_n n' f + f (Datatypes.S n'))%R
  end.

(** Now open R_scope *)
Open Scope R_scope.

(** =========================================================================
    PART 2: FACTORIZABILITY DEFINITION
    ========================================================================= *)

(** is_factorizable: Local hidden variable model (LOCC correlations)

    WHY: Bell's theorem claims NO local hidden variable model reproduces quantum
    correlations. This definition formalizes exactly what "local hidden variable"
    means: Alice and Bob share randomness λ, then respond deterministically.

    STRUCTURE: E(a,b|x,y) = Σ_λ p(λ) · A(a|x,λ) · B(b|y,λ)

    WHERE:
    - E: Correlation function (x=Alice's setting, y=Bob's setting, a,b=outcomes)
    - λ: Hidden variable (shared randomness, e.g., coin flips before measurement)
    - p(λ): Probability distribution over λ (normalized to 1)
    - A(a|x,λ): Alice's deterministic response (given x and λ, output a ∈ {-1,+1})
    - B(b|y,λ): Bob's deterministic response (given y and λ, output b ∈ {-1,+1})

    CLAIM: Factorizable correlations are EXACTLY the classical (local) correlations.
    They satisfy CHSH ≤ 2. Quantum correlations (CHSH ≤ 2√2) are NOT factorizable.

    PHYSICAL MEANING: Alice and Bob can meet beforehand, flip coins to generate
    shared randomness λ, then separate. During measurement, they use local
    deterministic strategies A(·|·,λ) and B(·|·,λ). No faster-than-light signaling,
    no spooky action at a distance. Pure locality + randomness.

    EXAMPLE: Perfect correlation with shared bit λ ∈ {0,1}:
    - p(0) = p(1) = 1/2
    - A(a|x,λ) = +1 if a=λ⊕x, else -1
    - B(b|y,λ) = +1 if b=λ⊕y, else -1
    - Result: E(0,0|0,0) = 1 (perfect agreement when x=y=0)

    FALSIFICATION: Show quantum singlet state |ψ⁻⟩ = (|01⟩-|10⟩)/√2 is factorizable.
    Bell's theorem proves this is IMPOSSIBLE - quantum correlations violate CHSH,
    so they can't be factorizable (by Fine's theorem).

    DEPENDENCIES: sum_n, R (reals), deterministic strategies (±1 outcomes)

    USED BY: factorizable_satisfies_minors, fine_theorem, factorizable_CHSH_classical_bound *)

Definition is_factorizable (E : nat -> nat -> nat -> nat -> R) : Prop :=
  exists (A : nat -> nat -> R)  (* Alice's response function: x,λ *)
         (B : nat -> nat -> R)  (* Bob's response function: y,λ *)
         (p : nat -> R)          (* Shared randomness distribution *)
         (lambda_max : nat),     (* Number of hidden variable states *)
    (* Probability distribution *)
    (forall λ, (λ <= lambda_max)%nat -> 0 <= p λ <= 1) /\
    (sum_n lambda_max p = 1) /\
    (* Response functions are valid *)
    (forall x λ, A x λ = -1 \/ A x λ = 1) /\
    (forall y λ, B y λ = -1 \/ B y λ = 1) /\
    (* Factorization condition (outcome indices are dummy for correlations) *)
    (forall a b x y,
      E a b x y = sum_n lambda_max (fun λ => p λ * A x λ * B y λ)).

(** =========================================================================
    PART 3: MINOR CONSTRAINTS (3×3 POSITIVITY)
    =========================================================================

    A correlation box satisfies minor constraints if all 3×3 submatrices
    of the correlation matrix have non-negative determinant.

    For CHSH, the key minor constraint is:

    | 1         E(00)     E(01)   |
    | E(00)     1         E(00,01)|  >= 0
    | E(01)     E(01,00)  1        |

    Where E(xy) = correlation E(a,b|x,y) and
          E(xy,x'y') = joint correlation E(a,b,a',b'|x,y,x',y')
    ========================================================================= *)

(** inner_prod: Weighted inner product over hidden-variable states *)
Definition inner_prod (lambda_max : nat) (p f g : nat -> R) : R :=
  sum_n lambda_max (fun λ => p λ * f λ * g λ).

(** minor_3x3_det: Determinant of a true 3×3 correlation minor

    WHY: For three observables X, Y, Z with |X|=|Y|=|Z|=1, the correlation
    matrix
        | 1  E[XY]  E[XZ] |
        | E[XY]  1  E[YZ] |
        | E[XZ] E[YZ]  1  |
    has non-negative determinant. This is the standard 3×3 minor constraint.

    In the factorizable model we take X=A0, Y=B0, Z=B1, so we need the
    same-party correlation E[B0B1], which is defined from the hidden-variable
    witnesses rather than from E alone.

    USED BY: satisfies_minor_constraints, factorizable_satisfies_minors *)
Definition minor_3x3_det
  (A : nat -> nat -> R)
  (B : nat -> nat -> R)
  (p : nat -> R)
  (lambda_max : nat) : R :=
  let r12 := inner_prod lambda_max p (fun λ => A 0%nat λ) (fun λ => B 0%nat λ) in
  let r13 := inner_prod lambda_max p (fun λ => A 0%nat λ) (fun λ => B 1%nat λ) in
  let r23 := inner_prod lambda_max p (fun λ => B 0%nat λ) (fun λ => B 1%nat λ) in
  1 - r12^2 - r13^2 - r23^2 + 2 * r12 * r13 * r23.

(** satisfies_minor_constraints: 3×3 minor constraint with full witnesses

    WHY: The 3×3 minor uses same-party correlations (like E[B0B1]) that are
    not derivable from E alone, so we define the constraint using the
    factorization witnesses explicitly.

    CLAIM: is_factorizable E ⟹ satisfies_minor_constraints E (proven below)

    USED BY: factorizable_satisfies_minors *)
Definition satisfies_minor_constraints (E : nat -> nat -> nat -> nat -> R) : Prop :=
  exists (A : nat -> nat -> R)
         (B : nat -> nat -> R)
         (p : nat -> R)
         (lambda_max : nat),
    (forall λ, (λ <= lambda_max)%nat -> 0 <= p λ <= 1) /\
    (sum_n lambda_max p = 1) /\
    (forall x λ, A x λ = -1 \/ A x λ = 1) /\
    (forall y λ, B y λ = -1 \/ B y λ = 1) /\
    (forall a b x y,
      E a b x y = sum_n lambda_max (fun λ => p λ * A x λ * B y λ)) /\
    0 <= minor_3x3_det A B p lambda_max.

(** =========================================================================
    PART 4A: SUMMATION LEMMAS (convex combinations)
    ========================================================================= *)

(** sum_n_le: Pointwise inequality implies sum inequality

    WHY: Convex combination reasoning requires comparing sums term-by-term.
    If each term f(λ) ≤ g(λ), then Σ f(λ) ≤ Σ g(λ).

    CLAIM: (∀λ ≤ n. f(λ) ≤ g(λ)) ⟹ sum_n n f ≤ sum_n n g

    PROOF STRATEGY: Induction on n. Base case: f(0) ≤ g(0) immediate.
    Step: If Σ_{i≤n'} f(i) ≤ Σ_{i≤n'} g(i) and f(S n') ≤ g(S n'), then
    Σ_{i≤S n'} f(i) = (Σ_{i≤n'} f(i)) + f(S n') ≤ (Σ_{i≤n'} g(i)) + g(S n').

    USED BY: fine_theorem (bounding CHSH by deterministic bounds) *)
Lemma sum_n_le :
  forall n f g,
    (forall λ, (λ <= n)%nat -> f λ <= g λ) ->
    sum_n n f <= sum_n n g.
Proof.
  induction n as [|n' IH]; intros f g Hle; simpl.
  - apply Hle. lia.
  - apply Rplus_le_compat.
    + apply IH. intros λ Hλ. apply Hle. lia.
    + apply Hle. lia.
Qed.

(** sum_n_scale: Scalar multiplication factors out of sums

    WHY: Expectation values E[c·X] = c·E[X] require distributivity of
    constants over probability sums.

    CLAIM: sum_n n (λ ↦ c·f(λ)) = c · sum_n n f

    PROOF STRATEGY: Induction + ring algebra.

    USED BY: fine_theorem (factoring out CHSH bounds ±2 from probability) *)
Lemma sum_n_scale :
  forall n (c : R) f,
    sum_n n (fun λ => c * f λ) = c * sum_n n f.
Proof.
  induction n as [|n' IH]; intro c; intro f; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(** sum_n_plus: Linearity - sum distributes over addition

    WHY: CHSH polynomial S = E₀₀ + E₀₁ + E₁₀ - E₁₁ requires splitting
    sums of combined terms into sums of individual terms.

    CLAIM: sum_n n (λ ↦ f(λ) + g(λ)) = sum_n n f + sum_n n g

    PROOF STRATEGY: Induction + ring algebra.

    USED BY: fine_theorem (expanding CHSH factorization) *)
Lemma sum_n_plus :
  forall n f g,
    sum_n n (fun λ => f λ + g λ) = sum_n n f + sum_n n g.
Proof.
  induction n as [|n' IH]; intros f g; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(** sum_n_minus: Linearity - sum distributes over subtraction

    WHY: The CHSH term "- E₁₁" requires sum_n (λ ↦ ... - p(λ)·A₁·B₁).

    CLAIM: sum_n n (λ ↦ f(λ) - g(λ)) = sum_n n f - sum_n n g

    PROOF STRATEGY: Induction + ring algebra.

    USED BY: fine_theorem (handling minus sign in CHSH) *)
Lemma sum_n_minus :
  forall n f g,
    sum_n n (fun λ => f λ - g λ) = sum_n n f - sum_n n g.
Proof.
  induction n as [|n' IH]; intros f g; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

(** sum_n_nonneg: Nonnegative terms give a nonnegative sum *)
Lemma sum_n_nonneg :
  forall n f,
    (forall λ, (λ <= n)%nat -> 0 <= f λ) ->
    0 <= sum_n n f.
Proof.
  induction n as [|n' IH]; intros f Hf; simpl.
  - apply Hf. lia.
  - apply Rplus_le_le_0_compat.
    + apply IH. intros λ Hλ. apply Hf. lia.
    + apply Hf. lia.
Qed.

(** sum_n_cauchy_schwarz: Weighted Cauchy-Schwarz for finite sums *)
Lemma sum_n_cauchy_schwarz :
  forall n p f g,
    (forall λ, (λ <= n)%nat -> 0 <= p λ) ->
    (sum_n n (fun λ => p λ * f λ * g λ))^2 <=
    (sum_n n (fun λ => p λ * f λ * f λ)) *
    (sum_n n (fun λ => p λ * g λ * g λ)).
Proof.
  intros n p f g Hp.
  set (a := sum_n n (fun λ => p λ * g λ * g λ)).
  set (b := sum_n n (fun λ => p λ * f λ * g λ)).
  set (c := sum_n n (fun λ => p λ * f λ * f λ)).
  assert (Hquad: forall t, a + 2 * b * t + c * t * t >= 0).
  {
    intro t.
    set (h := fun λ => g λ + t * f λ).
    assert (Hnonneg : 0 <= sum_n n (fun λ => p λ * h λ * h λ)).
    {
      apply sum_n_nonneg. intros λ Hλ. unfold h.
      specialize (Hp λ Hλ).
      replace (p λ * (g λ + t * f λ) * (g λ + t * f λ))
        with (p λ * ((g λ + t * f λ) * (g λ + t * f λ))) by ring.
      apply Rmult_le_pos; [exact Hp | apply Rle_0_sqr].
    }
    assert (Hexpand :
      sum_n n (fun λ => p λ * h λ * h λ) =
      a + (2 * t) * b + (t * t) * c).
    {
      unfold a, b, c, h.
      replace (fun λ => p λ * (g λ + t * f λ) * (g λ + t * f λ))
        with (fun λ => (p λ * g λ * g λ + (2 * t) * (p λ * f λ * g λ)) + (t * t) * (p λ * f λ * f λ)).
      2:{ apply functional_extensionality; intro λ; ring. }
      rewrite sum_n_plus.
      rewrite sum_n_plus.
      rewrite (sum_n_scale n (2 * t) (fun λ => p λ * f λ * g λ)).
      rewrite (sum_n_scale n (t * t) (fun λ => p λ * f λ * f λ)).
      ring.
    }
    rewrite Hexpand in Hnonneg.
    replace (a + 2 * b * t + c * t * t)
      with (a + (2 * t) * b + (t * t) * c) by ring.
    apply Rle_ge. exact Hnonneg.
  }
  pose proof (quadratic_nonneg_discriminant a b c Hquad) as Hdisc.
  replace ((sum_n n (fun λ => p λ * f λ * g λ)) ^ 2) with (b * b) by (unfold b; ring).
  replace (sum_n n (fun λ => p λ * f λ * f λ) * sum_n n (fun λ => p λ * g λ * g λ))
    with (c * a) by (unfold a, c; ring).
  replace (c * a) with (a * c) by ring.
  replace (b ^ 2) with (b * b) by ring.
  exact Hdisc.
Qed.

(** =========================================================================
    PART 4: FACTORIZABLE → MINOR CONSTRAINTS
    ========================================================================= *)

(** factorizable_cauchy_schwarz: Correlation bound from factorization

    WHY: Weighted Cauchy-Schwarz implies |E| ≤ 1 for deterministic ±1 outputs.

    CLAIM: For factorizable E, (E(a,b|x,y))² ≤ 1

    DEPENDENCIES: is_factorizable, sum_n_cauchy_schwarz

    USED BY: factorizable_satisfies_minors (as a supporting bound) *)
(** Lemma: Factorizable correlations satisfy Cauchy-Schwarz *)
Lemma factorizable_cauchy_schwarz :
  forall E : nat -> nat -> nat -> nat -> R,
    is_factorizable E ->
    forall a b x y,
      (E a b x y)^2 <= 1.
Proof.
  intros E [A [B [p [lambda_max [Hprob [Hsum [HA [HB Hfactor]]]]]]]].
  intros a b x y.
  rewrite (Hfactor a b x y).
  set (f := fun λ => A x λ).
  set (g := fun λ => B y λ).
  assert (Hcs := sum_n_cauchy_schwarz lambda_max p f g).
  specialize (Hcs (fun λ Hλ => (proj1 (Hprob λ Hλ)))).
  unfold f, g in Hcs.
  replace (fun λ => p λ * A x λ * A x λ) with (fun λ => p λ) in Hcs.
  2:{
    apply functional_extensionality; intro λ.
    destruct (HA x λ); nra.
  }
  replace (fun λ => p λ * B y λ * B y λ) with (fun λ => p λ) in Hcs.
  2:{
    apply functional_extensionality; intro λ.
    destruct (HB y λ); nra.
  }
  repeat (change (sum_n lambda_max (fun λ => p λ)) with (sum_n lambda_max p) in Hcs).
  rewrite Hsum in Hcs.
  replace (1 * 1) with 1 in Hcs by ring.
  unfold f, g in Hcs.
  exact Hcs.
Qed.

(** factorizable_satisfies_minors: Factorization implies matrix positivity

    CLAIM: is_factorizable E → satisfies_minor_constraints E *)
(** Main theorem: Factorizable correlations satisfy minor constraints *)
Theorem factorizable_satisfies_minors :
  forall E : nat -> nat -> nat -> nat -> R,
    is_factorizable E ->
    satisfies_minor_constraints E.
Proof.
  intros E [A [B [p [lambda_max [Hprob [Hsum [HA [HB Hfactor]]]]]]]].
  unfold satisfies_minor_constraints.
  exists A, B, p, lambda_max.
  refine (conj Hprob (conj Hsum (conj HA (conj HB (conj Hfactor _))))).
  unfold minor_3x3_det, inner_prod.
  set (r12 := sum_n lambda_max (fun λ => p λ * A 0%nat λ * B 0%nat λ)).
  set (r13 := sum_n lambda_max (fun λ => p λ * A 0%nat λ * B 1%nat λ)).
  set (r23 := sum_n lambda_max (fun λ => p λ * B 0%nat λ * B 1%nat λ)).
  set (f := fun λ => B 0%nat λ - r12 * A 0%nat λ).
  set (g := fun λ => B 1%nat λ - r13 * A 0%nat λ).

  assert (HA_sq : forall x λ, A x λ * A x λ = 1).
  {
    intros x l. destruct (HA x l); nra.
  }
  assert (HB_sq : forall y λ, B y λ * B y λ = 1).
  {
    intros y l. destruct (HB y l); nra.
  }

  assert (Hfg :
    sum_n lambda_max (fun λ => p λ * f λ * g λ) = r23 - r12 * r13).
  {
    unfold f, g.
    replace (fun λ => p λ * (B 0%nat λ - r12 * A 0%nat λ) *
                        (B 1%nat λ - r13 * A 0%nat λ))
      with (fun λ =>
        ((p λ * B 0%nat λ * B 1%nat λ +
          (- r13) * (p λ * A 0%nat λ * B 0%nat λ)) +
         (- r12) * (p λ * A 0%nat λ * B 1%nat λ)) +
        (r12 * r13) * (p λ * A 0%nat λ * A 0%nat λ)).
    2:{ apply functional_extensionality; intro l; ring. }
    rewrite sum_n_plus.
    rewrite sum_n_plus.
    rewrite sum_n_plus.
    rewrite (sum_n_scale lambda_max (- r13) (fun λ => p λ * A 0%nat λ * B 0%nat λ)).
    rewrite (sum_n_scale lambda_max (- r12) (fun λ => p λ * A 0%nat λ * B 1%nat λ)).
    rewrite (sum_n_scale lambda_max (r12 * r13) (fun λ => p λ * A 0%nat λ * A 0%nat λ)).
    replace (fun λ => p λ * A 0%nat λ * A 0%nat λ) with (fun λ => p λ).
    2:{
      apply functional_extensionality; intro l.
      rewrite Rmult_assoc, HA_sq. ring.
    }
    unfold r12, r13, r23.
    repeat (change (sum_n lambda_max (fun λ => p λ)) with (sum_n lambda_max p)).
    rewrite Hsum.
    ring.
  }

  assert (Hff :
    sum_n lambda_max (fun λ => p λ * f λ * f λ) = 1 - r12^2).
  {
    unfold f.
    replace (fun λ => p λ * (B 0%nat λ - r12 * A 0%nat λ) *
                        (B 0%nat λ - r12 * A 0%nat λ))
      with (fun λ =>
        (p λ * B 0%nat λ * B 0%nat λ +
         (- (2 * r12)) * (p λ * A 0%nat λ * B 0%nat λ)) +
        (r12 * r12) * (p λ * A 0%nat λ * A 0%nat λ)).
    2:{ apply functional_extensionality; intro l; ring. }
    rewrite sum_n_plus.
    rewrite sum_n_plus.
    rewrite (sum_n_scale lambda_max (- (2 * r12)) (fun λ => p λ * A 0%nat λ * B 0%nat λ)).
    rewrite (sum_n_scale lambda_max (r12 * r12) (fun λ => p λ * A 0%nat λ * A 0%nat λ)).
    replace (fun λ => p λ * B 0%nat λ * B 0%nat λ) with (fun λ => p λ).
    2:{
      apply functional_extensionality; intro l.
      rewrite Rmult_assoc, HB_sq. ring.
    }
    replace (fun λ => p λ * A 0%nat λ * A 0%nat λ) with (fun λ => p λ).
    2:{
      apply functional_extensionality; intro l.
      rewrite Rmult_assoc, HA_sq. ring.
    }
    unfold r12.
    repeat (change (sum_n lambda_max (fun λ => p λ)) with (sum_n lambda_max p)).
    rewrite Hsum.
    ring.
  }

  assert (Hgg :
    sum_n lambda_max (fun λ => p λ * g λ * g λ) = 1 - r13^2).
  {
    unfold g.
    replace (fun λ => p λ * (B 1%nat λ - r13 * A 0%nat λ) *
                        (B 1%nat λ - r13 * A 0%nat λ))
      with (fun λ =>
        (p λ * B 1%nat λ * B 1%nat λ +
         (- (2 * r13)) * (p λ * A 0%nat λ * B 1%nat λ)) +
        (r13 * r13) * (p λ * A 0%nat λ * A 0%nat λ)).
    2:{ apply functional_extensionality; intro l; ring. }
    rewrite sum_n_plus.
    rewrite sum_n_plus.
    rewrite (sum_n_scale lambda_max (- (2 * r13)) (fun λ => p λ * A 0%nat λ * B 1%nat λ)).
    rewrite (sum_n_scale lambda_max (r13 * r13) (fun λ => p λ * A 0%nat λ * A 0%nat λ)).
    replace (fun λ => p λ * B 1%nat λ * B 1%nat λ) with (fun λ => p λ).
    2:{
      apply functional_extensionality; intro l.
      rewrite Rmult_assoc, HB_sq. ring.
    }
    replace (fun λ => p λ * A 0%nat λ * A 0%nat λ) with (fun λ => p λ).
    2:{
      apply functional_extensionality; intro l.
      rewrite Rmult_assoc, HA_sq. ring.
    }
    unfold r13.
    repeat (change (sum_n lambda_max (fun λ => p λ)) with (sum_n lambda_max p)).
    rewrite Hsum.
    ring.
  }

  assert (Hcs :
    (sum_n lambda_max (fun λ => p λ * f λ * g λ))^2 <=
    (sum_n lambda_max (fun λ => p λ * f λ * f λ)) *
    (sum_n lambda_max (fun λ => p λ * g λ * g λ))).
  {
    apply sum_n_cauchy_schwarz.
    intros l Hl. destruct (Hprob l Hl) as [Hp _]. exact Hp.
  }

  rewrite Hfg in Hcs.
  rewrite Hff in Hcs.
  rewrite Hgg in Hcs.

  replace (1 - r12 ^ 2 - r13 ^ 2 - r23 ^ 2 + 2 * r12 * r13 * r23)
    with ((1 - r12 ^ 2) * (1 - r13 ^ 2) - (r23 - r12 * r13) ^ 2) by ring.
  nra.
Qed.

(** =========================================================================
    PART 5: CHSH FROM CORRELATIONS
    ========================================================================= *)

(** CHSH_from_correlations: The Bell-CHSH polynomial

    WHY: The CHSH inequality is the SIMPLEST Bell inequality. It's the minimal
    test to distinguish quantum from classical: if |S| > 2, correlations are
    nonlocal (not factorizable).

    STRUCTURE: S = E(A₀,B₀) + E(A₀,B₁) + E(A₁,B₀) - E(A₁,B₁)

    WHERE:
    - A₀, A₁: Alice's two measurement settings
    - B₀, B₁: Bob's two measurement settings
    - E(Aₓ,Bᵧ): Correlation ⟨Aₓ·Bᵧ⟩ = Σ_{a,b} a·b·P(a,b|x,y)

    CLAIM: For factorizable correlations, -2 ≤ S ≤ 2 (proven by fine_theorem).
    For quantum correlations, -2√2 ≤ S ≤ 2√2 (Tsirelson's bound).

    PROOF STRATEGY: This is just a DEFINITION. The bound S ≤ 2 comes from
    fine_theorem (factorizable ⟹ S ≤ 2).

    PHYSICAL MEANING: S measures "total correlation" across four measurement
    combinations. Classical physics (local realism) predicts |S| ≤ 2. Quantum
    mechanics achieves |S| = 2√2 with entangled states. The gap (2 to 2√2) is
    the signature of quantum nonlocality.

    EXAMPLE: Perfect classical strategy (deterministic):
    - A₀ = B₀ = +1, A₁ = B₁ = +1 ⟹ S = 1+1+1-1 = 2 (saturates classical bound)
    Quantum singlet |ψ⁻⟩ with optimal angles:
    - θ₀ = 0°, θ₁ = 45°, φ₀ = 22.5°, φ₁ = -22.5° ⟹ S = 2√2 ≈ 2.828

    FALSIFICATION: Find factorizable E with |S| > 2. This would contradict
    fine_theorem and Bell's theorem (proven impossible).

    DEPENDENCIES: E (correlation function), R (reals)

    USED BY: fine_theorem, factorizable_CHSH_classical_bound, local_box_CHSH_bound *)
(** CHSH polynomial S = E(A0B0) + E(A0B1) + E(A1B0) - E(A1B1)
    where E(AxBy) is correlation for Alice measuring on axis x, Bob on axis y.
    The first two arguments (a,b) are outcome indices (dummy for correlations).
    The last two arguments (x,y) are measurement indices. *)
Definition CHSH_from_correlations (E : nat -> nat -> nat -> nat -> R) : R :=
  E 0%nat 0%nat 0%nat 0%nat + E 0%nat 0%nat 0%nat 1%nat +
  E 0%nat 0%nat 1%nat 0%nat - E 0%nat 0%nat 1%nat 1%nat.

(** =========================================================================
    PART 6: FINE'S THEOREM - THE CRITICAL PROOF
    ========================================================================= *)

(** deterministic_strategy_chsh_bounded: Exhaustive case analysis for classical bound

    WHY: This is the ATOMIC BUILDING BLOCK of Bell's theorem. Every local
    correlation is a convex combination of deterministic strategies. If every
    deterministic strategy has |S| ≤ 2, then ALL local correlations have |S| ≤ 2.

    CLAIM: For ANY deterministic functions A, B : {0,1} → {-1,+1}, the CHSH
    polynomial S = A(0)·B(0) + A(0)·B(1) + A(1)·B(0) - A(1)·B(1) satisfies -2 ≤ S ≤ 2.

    PROOF STRATEGY (Complete - exhaustive case analysis):
    1. There are 2^8 = 256 deterministic strategies:
       A(0), A(1), B(0), B(1) each ∈ {-1, +1}
    2. For each configuration, compute S explicitly:
       S = A(0)·B(0) + A(0)·B(1) + A(1)·B(0) - A(1)·B(1)
    3. Verify |S| ≤ 2 for all 256 cases (automated tactic or brute force)
    4. Key insight: ALGEBRAIC simplification shows S ∈ {-4,-2,0,+2,+4} but only
       -2,0,+2 are achievable (±4 would require E00=E01=E10=E11=±1 simultaneously,
       which contradicts no-signaling)

    PHYSICAL MEANING: This is Bell's original insight (1964). Local realism means
    Alice and Bob use deterministic functions A(x,λ), B(y,λ) where λ is shared
    randomness. For CHSH, λ selects which deterministic strategy to use. Since
    every deterministic strategy has |S| ≤ 2, so does their convex combination.

    EXAMPLE: Deterministic strategy A(0)=A(1)=+1, B(0)=+1, B(1)=-1:
    S = (+1)·(+1) + (+1)·(-1) + (+1)·(+1) - (+1)·(-1) = 1 - 1 + 1 + 1 = 2 ✓

    COUNTEREXAMPLE: Try A(0)=A(1)=B(0)=B(1)=+1:
    S = (+1)·(+1) + (+1)·(+1) + (+1)·(+1) - (+1)·(+1) = 1 + 1 + 1 - 1 = 2 ✓

    FALSIFICATION: Find deterministic A,B with |S| > 2. This is proven IMPOSSIBLE
    by exhaustive enumeration (2^8 = 256 cases, all satisfy |S| ≤ 2).

    DEPENDENCIES: R (reals), deterministic functions A,B : nat → nat → R

    USED BY: fine_theorem (convex combination argument)

    STATUS: COMPLETE (Proven with exhaustive case analysis, ~8 lines) *)
(** Lemma: For each deterministic strategy, CHSH value is bounded *)
Lemma deterministic_strategy_chsh_bounded :
  forall (A : nat -> R) (B : nat -> R),
    (forall x, A x = -1 \/ A x = 1) ->
    (forall y, B y = -1 \/ B y = 1) ->
    -2 <=
      (A 0%nat * B 0%nat +
       A 0%nat * B 1%nat +
       A 1%nat * B 0%nat -
       A 1%nat * B 1%nat) <= 2.
Proof.
  intros A B HA HB.
  (* Exhaustive case analysis over the 4 relevant ±1 values. *)
  destruct (HA 0%nat) as [HA0 | HA0];
  destruct (HA 1%nat) as [HA1 | HA1];
  destruct (HB 0%nat) as [HB0 | HB0];
  destruct (HB 1%nat) as [HB1 | HB1];
  subst; simpl;
  rewrite HA0, HA1, HB0, HB1;
  split; cbv; nra.
Qed.

(** fine_theorem: CHSH bound from factorizability and minor constraints

    WHY: This is Fine's theorem (1982) - the CLASSICAL version of Bell's theorem.
    It proves that factorizable correlations (local hidden variables) ALWAYS
    satisfy CHSH ≤ 2, WITHOUT assuming specific probability distributions.

    CLAIM: is_factorizable E ⟹ -2 ≤ CHSH(E) ≤ 2

    PROOF STRATEGY (COMPLETE - convex combination argument):
    1. Factorizable correlations decompose as: E = Σ_λ p(λ) · [A(λ) ⊗ B(λ)]
    2. For each λ, apply deterministic_strategy_chsh_bounded:
       -2 ≤ S_λ ≤ 2 where S_λ = A(0,0,λ)·B(0,0,λ) + ... - A(1,1,λ)·B(1,1,λ)
    3. Expand CHSH(E) using factorization:
       CHSH(E) = Σ_λ p(λ) · S_λ
    4. Since p(λ) ≥ 0 and Σ p(λ) = 1, this is a CONVEX COMBINATION:
       -2 ≤ Σ_λ p(λ)·S_λ ≤ 2 (convex comb of [-2,2] stays in [-2,2])
    5. Both bounds proven explicitly using sum_n_le and sum_n_scale lemmas

    PHYSICAL MEANING: This theorem establishes the CLASSICAL LIMIT. Any experiment
    that can be explained by local hidden variables (shared randomness + local
    determinism) MUST satisfy |CHSH| ≤ 2. Violations mean either:
    (a) Nature is not local (spooky action at a distance), OR
    (b) Nature is not deterministic (irreducible randomness), OR
    (c) Both (quantum mechanics: local + irreducible randomness)

    HISTORICAL CONTEXT: Arthur Fine (1982) proved this as a simplification of
    Bell's theorem. Instead of hidden variables, use OPERATIONAL constraints
    (minor positivity). This makes Bell's theorem TESTABLE without knowing the
    hidden variable model.

    EXAMPLE: Suppose experiment measures CHSH = 2.5. By fine_theorem, this
    correlation is NOT factorizable. Therefore, either:
    - Quantum entanglement (most likely), or
    - Measurement apparatus malfunction, or
    - Loophole exploitation (detection loophole, locality loophole)

    FALSIFICATION: Find factorizable E with |CHSH(E)| > 2. This would require
    a deterministic strategy with |S| > 2 (impossible by deterministic_strategy_chsh_bounded)
    or a convex combination that escapes the [-2,2] interval (impossible by convexity).

    DEPENDENCIES: is_factorizable, CHSH_from_correlations,
    deterministic_strategy_chsh_bounded, sum_n lemmas

    USED BY: factorizable_CHSH_classical_bound, local_box_CHSH_bound

    STATUS: COMPLETE (Zero admits, ~120 lines with both bounds proven) *)
(** Fine's Theorem: Factorizability implies CHSH ≤ 2 *)
Theorem fine_theorem :
  forall E : nat -> nat -> nat -> nat -> R,
    is_factorizable E ->
    -2 <= CHSH_from_correlations E <= 2.
Proof.
  intros E Hfact.
  unfold CHSH_from_correlations.
  split.

  (** Lower bound: S >= -2 *)
  - destruct Hfact as [A [B [p [lambda_max [Hprob [Hsum [HA [HB Hfactor]]]]]]]].
    (* Expand correlations using factorization *)
    repeat rewrite Hfactor.
    set (Sλ := fun λ =>
      A 0%nat λ * B 0%nat λ +
      A 0%nat λ * B 1%nat λ +
      A 1%nat λ * B 0%nat λ -
      A 1%nat λ * B 1%nat λ).
    (* Each deterministic strategy is bounded *)
    assert (Hbounds: forall λ, -2 <= Sλ λ <= 2).
    { intro λ.
      pose proof (deterministic_strategy_chsh_bounded
                    (fun x => A x λ)
                    (fun y => B y λ)
                    (fun x => HA x λ)
                    (fun y => HB y λ)) as Hdet.
      exact Hdet.
    }
    (* Use convex combination with nonnegative weights *)
    set (f00 := fun λ => p λ * A 0%nat λ * B 0%nat λ).
    set (f01 := fun λ => p λ * A 0%nat λ * B 1%nat λ).
    set (f10 := fun λ => p λ * A 1%nat λ * B 0%nat λ).
    set (f11 := fun λ => p λ * A 1%nat λ * B 1%nat λ).
    assert (HsumS :
      sum_n lambda_max (fun λ => p λ * Sλ λ) =
      sum_n lambda_max f00 +
      sum_n lambda_max f01 +
      sum_n lambda_max f10 -
      sum_n lambda_max f11).
    { unfold f00, f01, f10, f11.
      replace (fun λ => p λ * Sλ λ) with
        (fun λ =>
          p λ * A 0%nat λ * B 0%nat λ +
          (p λ * A 0%nat λ * B 1%nat λ +
           (p λ * A 1%nat λ * B 0%nat λ -
            p λ * A 1%nat λ * B 1%nat λ))).
      2:{
        apply functional_extensionality; intro λ.
        unfold Sλ. ring.
      }
      rewrite sum_n_plus.
      rewrite sum_n_plus.
      rewrite sum_n_minus.
      ring.
    }
    rewrite <- HsumS.
    assert (Hle: sum_n lambda_max (fun λ => (-2) * p λ)
                <= sum_n lambda_max (fun λ => p λ * Sλ λ)).
    { apply sum_n_le. intros λ Hλ.
      destruct (Hprob λ Hλ) as [Hp _].
      specialize (Hbounds λ) as [Hlower _].
      nra.
    }
    rewrite (sum_n_scale lambda_max (-2) p) in Hle.
    rewrite Hsum in Hle.
    rewrite Rmult_1_r in Hle.
    exact Hle.

  (** Upper bound: S <= 2 *)
  - destruct Hfact as [A [B [p [lambda_max [Hprob [Hsum [HA [HB Hfactor]]]]]]]].
    repeat rewrite Hfactor.
    set (Sλ := fun λ =>
      A 0%nat λ * B 0%nat λ +
      A 0%nat λ * B 1%nat λ +
      A 1%nat λ * B 0%nat λ -
      A 1%nat λ * B 1%nat λ).
    set (f00 := fun λ => p λ * A 0%nat λ * B 0%nat λ).
    set (f01 := fun λ => p λ * A 0%nat λ * B 1%nat λ).
    set (f10 := fun λ => p λ * A 1%nat λ * B 0%nat λ).
    set (f11 := fun λ => p λ * A 1%nat λ * B 1%nat λ).
    assert (HsumS :
      sum_n lambda_max (fun λ => p λ * Sλ λ) =
      sum_n lambda_max f00 +
      sum_n lambda_max f01 +
      sum_n lambda_max f10 -
      sum_n lambda_max f11).
    { unfold f00, f01, f10, f11.
      replace (fun λ => p λ * Sλ λ) with
        (fun λ =>
          p λ * A 0%nat λ * B 0%nat λ +
          (p λ * A 0%nat λ * B 1%nat λ +
           (p λ * A 1%nat λ * B 0%nat λ -
            p λ * A 1%nat λ * B 1%nat λ))).
      2:{
        apply functional_extensionality; intro λ.
        unfold Sλ. ring.
      }
      rewrite sum_n_plus.
      rewrite sum_n_plus.
      rewrite sum_n_minus.
      ring.
    }
    rewrite <- HsumS.
    assert (Hbounds: forall λ, -2 <= Sλ λ <= 2).
    { intro λ.
      pose proof (deterministic_strategy_chsh_bounded
                    (fun x => A x λ)
                    (fun y => B y λ)
                    (fun x => HA x λ)
                    (fun y => HB y λ)) as Hdet.
      exact Hdet.
    }
    assert (Hle: sum_n lambda_max (fun λ => p λ * Sλ λ)
                <= sum_n lambda_max (fun λ => 2 * p λ)).
    { apply sum_n_le. intros λ Hλ.
      destruct (Hprob λ Hλ) as [Hp _].
      specialize (Hbounds λ) as [_ Hupper].
      nra.
    }
    rewrite (sum_n_scale lambda_max 2 p) in Hle.
    rewrite Hsum in Hle.
    rewrite Rmult_1_r in Hle.
    exact Hle.
Qed.

(** =========================================================================
    PART 7: COMPLETE PROOF CHAIN
    ========================================================================= *)

(** Corollary: Factorizable correlations satisfy CHSH ≤ 2 *)
Corollary factorizable_CHSH_classical_bound :
  forall E : nat -> nat -> nat -> nat -> R,
    is_factorizable E ->
    -2 <= CHSH_from_correlations E <= 2.
Proof.
  intros E Hfact.
  apply fine_theorem.
  exact Hfact.
Qed.

(** Connecting to BoxCHSH.v using Q2R conversion *)
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qreals.
Require Import Coq.QArith.Qabs.

(** Note: BoxCHSH.E has signature (B : Box) (x y : nat) : Q
    BoxCHSH.E computes correlation for Alice's measurement x, Bob's measurement y.
    For CHSH, only correlations matter, not individual outcome probabilities.
    The parameters a,b are dummy parameters to match the signature of CHSH_from_correlations. *)

Definition box_correlations (B : Box) : nat -> nat -> nat -> nat -> R :=
  fun a b x y => Q2R (BoxCHSH.E B x y).

(** local_box_CHSH_bound: Connection to BoxCHSH.v via Q2R conversion

    WHY: This theorem bridges the gap between our real-valued Fine's theorem
    and BoxCHSH.v's rational-valued CHSH inequality. It establishes that
    factorizable boxes (local correlations) satisfy |S| ≤ 2.

    CLAIM: For any Box B, if box_correlations B is factorizable,
    then Q2R(|S(B)|) ≤ 2.

    PROOF STRATEGY:
    1. Apply factorizable_CHSH_classical_bound to get -2 ≤ S ≤ 2 in reals
    2. Show Q2R(S(B)) = CHSH_from_correlations via distributivity of Q2R
    3. Prove Q2R(Qabs(x)) = Rabs(Q2R(x)) by case analysis on sign
    4. Conclude Rabs(Q2R(S(B))) ≤ 2 from bounds

    PHYSICAL MEANING: Any experimentally measured correlation box that can be
    explained by local hidden variables (factorizability) must satisfy the
    classical CHSH bound. Violations of this bound prove nonlocality.

    EXAMPLE: If experimental Box B yields S = 2.5, then box_correlations B
    is NOT factorizable, proving quantum entanglement or nonlocality.

    FALSIFICATION: Find factorizable Box with |S| > 2. Impossible by fine_theorem.

    DEPENDENCIES: fine_theorem, BoxCHSH.v, Q2R/Qabs conversion lemmas

    USED BY: Bridge to TsirelsonUpperBound.v for μ=0 → CHSH ≤ 2 *)
(** The critical theorem connecting to TsirelsonUpperBound.v *)
Theorem local_box_CHSH_bound :
  forall B : Box,
    is_factorizable (box_correlations B) ->
    (Q2R (Qabs (BoxCHSH.S B)) <= 2)%R.
Proof.
  intros B Hfact.
  unfold box_correlations in Hfact.
  pose proof (factorizable_CHSH_classical_bound (box_correlations B) Hfact) as [Hlower Hupper].

  (* S(B) is the CHSH polynomial from BoxCHSH.v *)
  (* S B = E B 0 0 + E B 0 1 + E B 1 0 - E B 1 1 *)

  (* Show this matches CHSH_from_correlations *)
  assert (Heq : Q2R (BoxCHSH.S B) = CHSH_from_correlations (box_correlations B)).
  {
    unfold CHSH_from_correlations, box_correlations, BoxCHSH.S.
    (* Q2R is distributive over +/- *)
    (* S B = E 0 0 + E 0 1 + E 1 0 - E 1 1 *)
    (* Structure: ((E00 + E01) + E10) - E11 *)
    rewrite Q2R_minus.  (* Q2R(a - b) = Q2R(a) - Q2R(b) *)
    rewrite Q2R_plus.   (* Q2R((E00 + E01) + E10) = Q2R(E00 + E01) + Q2R(E10) *)
    rewrite Q2R_plus.   (* Q2R(E00 + E01) = Q2R(E00) + Q2R(E01) *)
    (* Now both sides are: Q2R(E00) + Q2R(E01) + Q2R(E10) - Q2R(E11) *)
    reflexivity.
  }

  (* Apply bounds *)
  rewrite <- Heq in Hlower, Hupper.

  (* From Hlower/Hupper: -2 <= Q2R(S B) <= 2 *)
  (* Need to show: Q2R(Qabs(S B)) <= 2 *)
  (* This follows from |x| <= 2 when -2 <= x <= 2 *)
  (* The key lemma: Q2R preserves absolute value *)
  assert (Habs: Q2R (Qabs (BoxCHSH.S B)) = Rabs (Q2R (BoxCHSH.S B))).
  { (* Q2R commutes with Qabs via case analysis on the sign of the rational. *)
    destruct (Qlt_le_dec (BoxCHSH.S B) 0) as [Hneg | Hnonneg].
    - (* negative case *)
      assert (Heq_abs: Qabs (BoxCHSH.S B) == - BoxCHSH.S B).
      { apply Qabs_neg. apply Qlt_le_weak. exact Hneg. }
      rewrite (Qeq_eqR _ _ Heq_abs).
      rewrite Q2R_opp.
      symmetry.
      apply Rabs_left.
      assert (Hlt : (Q2R (BoxCHSH.S B) < Q2R 0)%R) by (apply Qlt_Rlt; exact Hneg).
      lra.
    - (* nonnegative case *)
      assert (Heq_abs: Qabs (BoxCHSH.S B) == BoxCHSH.S B) by (apply Qabs_pos; exact Hnonneg).
      rewrite (Qeq_eqR _ _ Heq_abs).
      symmetry.
      apply Rabs_pos_eq.
      assert (HnonnegR : (Q2R 0 <= Q2R (BoxCHSH.S B))%R) by (apply Qle_Rle; exact Hnonneg).
      lra.
  }
  rewrite Habs.
  apply Rabs_le.
  split; assumption.
Qed.

(** =========================================================================
    PART 8: VERIFICATION SUMMARY
    ========================================================================= *)

(** Summary of what is PROVEN:

    ✅ is_factorizable: Definition of LOCC correlations (COMPLETE)
    ✅ satisfies_minor_constraints: 3×3 minor constraint with witnesses (COMPLETE)
    ✅ CHSH_from_correlations: CHSH polynomial definition (COMPLETE)
    ✅ deterministic_strategy_chsh_bounded: Exhaustive ±1 case analysis (COMPLETE)
    ✅ fine_theorem: Convex-combination bound for factorizable correlations (COMPLETE)
    ✅ local_box_CHSH_bound: Q2R/Qabs alignment and absolute-value bound (COMPLETE)

    NOTE: The 3×3 minor constraints remain defined here for compatibility with
    other algebraic files. The classical CHSH bound (fine_theorem) is proven
    directly from factorizability via convex combinations, WITHOUT needing the
    minor constraint machinery.
 *)

(** Verification certificate *)
Definition fine_theorem_proven : Prop :=
  forall E, is_factorizable E -> (-2 <= CHSH_from_correlations E <= 2)%R.

Theorem fine_theorem_holds : fine_theorem_proven.
Proof.
  unfold fine_theorem_proven.
  intros E Hfact.
  apply factorizable_CHSH_classical_bound.
  exact Hfact.
Qed.

(** =========================================================================
    PART 9: AXIOM VERIFICATION
    ========================================================================= *)

(** Verify what axioms the critical theorems depend on.
    Expected: functional_extensionality (used in fine_theorem for lambda equality)
              plus standard real analysis axioms from Coq.Reals *)

Print Assumptions deterministic_strategy_chsh_bounded.
(** Expected: Real axioms only (Rplus, Rmult commutativity from reals) *)

Print Assumptions fine_theorem.
(** Expected: functional_extensionality + real axioms *)

Print Assumptions factorizable_CHSH_classical_bound.
(** Expected: Same as fine_theorem (it's a direct corollary) *)

Print Assumptions local_box_CHSH_bound.
(** Expected: functional_extensionality + real axioms + Q2R axioms *)

Print Assumptions fine_theorem_holds.
(** Expected: Same as fine_theorem *)

(** END OF FILE - All proofs complete (no admits remain) *)
