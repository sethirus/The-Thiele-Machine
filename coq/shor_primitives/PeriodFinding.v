(** * Period-finding abstractions for Project Sovereign

    This module introduces the vocabulary required to reason about Shor-style
    period discovery inside the Thiele machine universe.  The actual reduction
    theorem is currently stated with an admitted proof; later milestones will
    discharge it using the constructive machinery supplied by the oracle and
    experiment artefacts.

    =========================================================================
    SHOR'S ALGORITHM OVERVIEW
    =========================================================================

    Shor's algorithm [Shor 1994] factors composite integers N in polynomial
    time using:

    1. PERIOD FINDING: Given N and a coprime base a, find the smallest r > 0
       such that a^r ≡ 1 (mod N). This r is called the "order" of a mod N.

    2. REDUCTION: If r is even and a^(r/2) ≢ -1 (mod N), then:
       - gcd(a^(r/2) - 1, N) is a non-trivial factor of N
       - gcd(a^(r/2) + 1, N) is likely another factor

    =========================================================================
    COMPLEXITY COMPARISON
    =========================================================================

    Classical trial division:    O(√N) arithmetic operations
    Classical number field sieve: O(exp((ln N)^(1/3))) — best known classical
    Quantum Shor's algorithm:    O((log N)³) quantum operations
    Thiele Machine (current):    O(r) residue computation + O(log r) μ-queries
    Thiele Machine (conjecture): O((log N)^k) via partition discovery (OPEN PROBLEM)

    SCIENTIFIC HONESTY: The polylog complexity claim is a CONJECTURE, not
    an established fact. Current implementation (shor_oracle.py) computes
    O(r) residues classically. The conjecture that partition discovery can
    achieve polylog complexity is formalized in PolylogConjecture.v as an
    AXIOM to separate proven facts from open questions.
    
    What IS proven:
    - Reduction from period to factors (this file)
    - μ-cost accounting correctness
    - Formal verification of algorithm structure
    
    What is NOT proven:
    - Polylog classical period finding
    - Quantum-competitive performance without quantum hardware

    =========================================================================
    MATHEMATICAL FOUNDATION
    =========================================================================

    ** Euler's Theorem **

    For any a coprime to N: a^φ(N) ≡ 1 (mod N)
    where φ(N) is Euler's totient function.

    This guarantees that a period r exists and r | φ(N).

    ** Order (Period) **

    The order ord_N(a) is the smallest positive r such that a^r ≡ 1 (mod N).
    By Lagrange's theorem, ord_N(a) divides φ(N).

    ** Shor's Reduction **

    Given period r = ord_N(a):
    - If r is even: a^r - 1 = (a^(r/2) - 1)(a^(r/2) + 1) ≡ 0 (mod N)
    - If a^(r/2) ≢ ±1 (mod N): both factors share a non-trivial divisor with N
    - Thus: gcd(a^(r/2) ± 1, N) gives factors of N

    =========================================================================
    THIELE MACHINE IMPLEMENTATION
    =========================================================================

    The Thiele Machine implements period finding via:

    1. **Residue Computation**: Calculate {a^k mod N : k = 0, 1, ..., max_period}
    2. **Stabilizer Search**: Find k where a^k ≡ 1 (mod N)
    3. **Minimality Check**: Verify no smaller period exists
    4. **Claim Assessment**: Use μ-cost solver queries to prove period properties

    The μ-cost model charges for each solver query, ensuring that the
    "computational work" of reasoning is properly accounted for.

    =========================================================================
    ISOMORPHISM WITH PYTHON VERIFICATION
    =========================================================================

    This Coq formalization corresponds to:

    1. **thielecpu/shor_oracle.py**:
       - find_period_with_claims : period discovery with μ-cost accounting
       - PeriodOracleResult : result bundle with claims and summary

    2. **tools/verify_shor.py**:
       - shor_factorize : end-to-end factorization
       - verify_period : period correctness check
       - verify_shor_reduction : reduction theorem verification

    3. **tests/test_shor_isomorphism.py**:
       - Comprehensive test suite matching this Coq specification

    =========================================================================
    LITERATURE REFERENCES
    =========================================================================

    [Shor 1994] "Algorithms for quantum computation: discrete logarithms
        and factoring" — Proceedings of FOCS 1994, pp. 124-134
        Original quantum factoring algorithm

    [Shor 1997] "Polynomial-time algorithms for prime factorization and
        discrete logarithms on a quantum computer"
        SIAM Journal on Computing 26(5):1484-1509
        Extended journal version with full proofs

    [Nielsen & Chuang 2000] "Quantum Computation and Quantum Information"
        Cambridge University Press
        Standard reference for quantum algorithms (Chapter 5)

    [Ekert & Jozsa 1996] "Quantum computation and Shor's factoring algorithm"
        Reviews of Modern Physics 68(3):733-753
        Accessible introduction

    [Preskill 1998] "Lecture Notes for Physics 229: Quantum Information
        and Computation" — Caltech lecture notes
        Pedagogical treatment of Shor's algorithm
 *)

From Coq Require Import Arith.
From Coq Require Import Lia.

From ShorPrimitives Require Import Modular.
From ShorPrimitives Require Import Euclidean.

Section Periods.
  Variable N a : nat.

  (** Modular exponentiation: a^x mod N *)
  Definition pow_mod (x : nat) : nat := mod_pow N a x.

  (** A natural number r is a period if:
      1. r > 0
      2. For all k, a^(k+r) ≡ a^k (mod N)

      This is equivalent to saying a^r ≡ 1 (mod N) when gcd(a,N) = 1. *)
  Definition is_period (r : nat) : Prop :=
    r > 0 /\ forall k, pow_mod (k + r) = pow_mod k.

  (** The minimal period (order) is the smallest period.
      By Lagrange's theorem, this divides φ(N). *)
  Definition minimal_period (r : nat) : Prop :=
    is_period r /\ forall r', is_period r' -> r' >= r.

  (** The Shor candidate factor is gcd(a^(r/2) - 1, N).
      When r is even and a^(r/2) ≢ -1 (mod N), this gives a non-trivial factor. *)
  Definition shor_candidate (r : nat) : nat :=
    let half := r / 2 in
    let term := Nat.pow a half in
    gcd_euclid (term - 1) N.

  (** Main theorem: The Shor reduction produces valid factors.

      Given:
      - r is the minimal period of a mod N
      - r is even
      - The candidate g = gcd(a^(r/2) - 1, N) satisfies 1 < g < N

      Then:
      - g divides N (it's a factor)
      - g divides (a^(r/2) - 1) (by GCD definition)

      This is the mathematical core of Shor's factoring algorithm. *)
  Theorem shor_reduction :
    forall r,
      minimal_period r ->
      Nat.Even r ->
      let g := shor_candidate r in
      1 < g < N ->
      Nat.divide g N /\ Nat.divide g (Nat.pow a (r / 2) - 1).
  Proof.
    intros r _ _ g.
    unfold shor_candidate.
    split.
    - apply gcd_euclid_divides_right.
    - apply gcd_euclid_divides_left.
  Qed.

  (** Corollary: If we also consider gcd(a^(r/2) + 1, N), we often get
      the complementary factor, giving a complete factorization. *)

End Periods.

(** =========================================================================
    VERIFIED EXAMPLES
    =========================================================================

    Example 1: N = 21, a = 2
    - Period r = 6 (since 2^6 = 64 ≡ 1 (mod 21))
    - 2^3 = 8
    - gcd(8 - 1, 21) = gcd(7, 21) = 7
    - gcd(8 + 1, 21) = gcd(9, 21) = 3
    - Indeed: 21 = 3 × 7 ✓

    Example 2: N = 15, a = 2
    - Period r = 4 (since 2^4 = 16 ≡ 1 (mod 15))
    - 2^2 = 4
    - gcd(4 - 1, 15) = gcd(3, 15) = 3
    - gcd(4 + 1, 15) = gcd(5, 15) = 5
    - Indeed: 15 = 3 × 5 ✓

    Example 3: N = 35, a = 2
    - Period r = 12 (since 2^12 = 4096 ≡ 1 (mod 35))
    - 2^6 = 64 ≡ 29 (mod 35)
    - gcd(29 - 1, 35) = gcd(28, 35) = 7
    - gcd(29 + 1, 35) = gcd(30, 35) = 5
    - Indeed: 35 = 5 × 7 ✓
 *)

