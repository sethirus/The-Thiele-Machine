# TDD Analysis: PDISCOVER Complexity Claims vs. Proofs

**Date**: January 1, 2026  
**Status**: CRITICAL GAP IDENTIFIED

## Executive Summary

Through test-driven development, we discovered a fundamental gap between:
1. **What the Coq comments claim**: O(μ-cost × log N) for period finding
2. **What the implementation actually does**: O(r) residue computations where r is the period
3. **What the formal proofs actually prove**: Nothing about computational complexity of residue enumeration

## Test Results

### Test: `test_symbolic_period_finding.py`

```python
# Classical approach: Enumerate residues until finding period
period_classical, residues_computed = find_period_classical(n=3233, a=3)
# Result: period=260, residues_computed=260

# Symbolic approach: Let Z3 find period with partial sampling
period_symbolic, solver_queries = find_period_symbolic(n=3233, a=3, sample_size=20)
# Result: period=20, solver_queries=10
# WRONG ANSWER! (20 is not the minimal period)
```

**Finding**: Z3 cannot find periods without sufficient ground truth. Sampling only 20 values led to incorrect answer.

## What the Coq Files Actually Say

### `coq/shor_primitives/PeriodFinding.v` (Lines 27-30)

```coq
Classical trial division:    O(√N) arithmetic operations
Classical number field sieve: O(exp((ln N)^(1/3))) — best known classical
Quantum Shor's algorithm:    O((log N)³) quantum operations
Thiele Machine:              O(μ-cost × log N) reasoning operations  ← CLAIM
```

### `coq/shor_primitives/PeriodFinding.v` (Line 66)

```coq
1. **Residue Computation**: Calculate {a^k mod N : k = 0, 1, ..., max_period}  ← ACTUAL IMPLEMENTATION
```

**Contradiction**: Line 30 claims O(log N) but line 66 describes O(r) enumeration.

### `coq/thielemachine/coqproofs/EfficientDiscovery.v` (Lines 100-112)

```coq
Theorem discovery_polynomial_time :
  forall prob : Problem,
  exists c : nat,
    c > 0.
Proof.
  intros prob.
  exists 12.
  lia.
Qed.
```

**What it proves**: There exists a constant c > 0.  
**What it DOESN'T prove**: That discovery runs in O(n³) time.  
**What the comment claims**: "Discovery runs in O(n³) time"

### `coq/thielemachine/coqproofs/InfoTheory.v` (Lines 252-257)

```coq
(* For binary search: μ-cost is O(log n) queries × query_cost *)
Definition binary_search_mu_cost (n : nat) (query_bytes : nat) : Q :=
  let num_queries := Z.log2_up (Z.of_nat n) in
  inject_Z num_queries * question_cost query_bytes.
```

**Context**: This is about binary search with an ORACLE that can answer queries.  
**Does NOT apply to**: Period finding where you must compute residues arithmetically.

## The Critical Distinction

### What IS Proven (Correctly)

1. **μ-monotonicity**: μ-ledger never decreases ✓
2. **No Free Insight**: Supra-quantum correlations require revelation ✓
3. **Turing Subsumption**: Thiele Machine can simulate Turing machines ✓
4. **Shor Reduction**: If you HAVE the period r, you can extract factors ✓
5. **Binary search μ-cost**: O(log n) queries to narrow down a value ✓

### What is NOT Proven (Gap)

1. **Period finding complexity**: No theorem proves O(log N) arithmetic cost
2. **PDISCOVER complexity**: No theorem bounds computational steps for discovering structure
3. **Residue enumeration**: No proof that you can avoid O(r) residue computations
4. **Partition discovery scaling**: Theorem says "exists c > 0" not "c * n³"

## Information-Theoretic Argument

### Why O(r) Seems Unavoidable

**Shannon Entropy Argument**:
- To uniquely identify period r among {1, 2, ..., max_period}, you need log₂(max_period) bits of information
- Each residue value a^k mod N provides at most log₂(N) bits
- BUT: You need to find the PATTERN, not just identify r from a list
- Pattern recognition requires examining enough samples to distinguish periodicity

**Our Test Demonstrated**:
- With 20 samples: Z3 found r=20 (WRONG - not minimal period)
- With 260 samples: Would find r=260 (CORRECT)
- You cannot compress below O(r) samples without additional structure

### Why Z3 Cannot Replace Arithmetic

**Z3 Limitations**:
1. **Uninterpreted functions**: Z3 can reason symbolically, but needs ground truth
2. **Nonlinear integer arithmetic**: Decidability is limited - may timeout or fail
3. **Pattern extrapolation**: Z3 cannot "guess" periodicity from insufficient data

**What Z3 CAN Do**:
- Verify properties given concrete values (binary search over known data)
- Certify that discovered period is minimal (O(log r) queries)
- Prove divisibility properties (gcd, factorization)

**What Z3 CANNOT Do**:
- Discover period without computing residues
- Avoid O(r) arithmetic operations through symbolic reasoning alone

## Implications for Thesis Claims

### Current Implementation (shor_oracle.py)

```python
# Lines 86-93: O(r) arithmetic
for k in range(0, max_period + 1):
    residues[k] = pow(a, k, n)  # Classical exponentiation
    if residues[k] == 1 and k > 0:
        stabilisers.append(k)
        break

# Lines 150-230: O(log r) μ-queries
assess(statement="Period is even", predicate=r % 2 == 0)
assess(statement=f"Period equals {period}", predicate=r == period)
```

**Total Cost**:
- Arithmetic operations: O(r)
- μ-cost (Z3 queries): O(log r)
- **Bottleneck**: O(r) residue enumeration

### Extrapolation to RSA-2048

From `artifacts/rsa_extrapolation.txt`:
- For N ≈ 2^2048, period r ≈ φ(N) ≈ 2^2047
- O(r) operations = O(2^2047) ≈ 10^616 operations
- **This is exponential time**, not polynomial

### What Would Need to Be True for Quantum-Like Speedup

**Required**: Prove that PDISCOVER can find period in O(polylog(N)) arithmetic operations

**Approaches that might work**:
1. **Quantum Fourier Transform analogue**: Classical fast Fourier transform on residue sequence
2. **Algebraic structure exploitation**: Use ring homomorphisms to reduce problem size
3. **Lattice-based methods**: Reduce to shortest vector problem (still exponential)
4. **Order-finding oracle**: Assume access to a primitive that answers period queries in O(1)

**Problem**: None of these are implemented, and most are still exponential classically.

## Recommendations

### 1. Honest Documentation Update

Update `coq/shor_primitives/PeriodFinding.v` line 30:

```coq
-    Thiele Machine:              O(μ-cost × log N) reasoning operations
+    Thiele Machine:              O(r) residue computations + O(log r) μ-queries for certification
```

### 2. Complexity Theorem Statement

Add to `EfficientDiscovery.v`:

```coq
(** OPEN PROBLEM: Prove or disprove:
    Period finding via PDISCOVER requires Ω(r) arithmetic operations
    where r is the minimal period.
    
    Current implementation: O(r) residue enumeration (classical)
    Quantum algorithm: O((log N)³) via QFT
    
    Conjecture: Without quantum resources, period finding is Ω(r).
*)
```

### 3. Test-Driven Proof Search

Create tests that would PASS if quantum-like speedup exists:

```python
def test_period_finding_polylog_complexity():
    """Test if period finding scales polylogarithmically."""
    test_cases = [(15, 2), (3233, 3), (31313, 3)]
    
    for n, a in test_cases:
        period, ops = find_period_with_complexity_tracking(n, a)
        expected_max_ops = (math.log2(n) ** 3) * 100  # Generous constant
        
        assert ops <= expected_max_ops, \
            f"Period finding used {ops} ops, expected O((log N)³) ≈ {expected_max_ops}"
```

**Expected**: This test would FAIL with current implementation (O(r) ops)

### 4. Falsifiability Criteria

Define what would prove/disprove quantum-like advantage:

**Prove quantum-like**: Exhibit algorithm + proof that:
- Finds period r in O(polylog(N)) arithmetic operations
- Correctness verified (finds minimal period)
- No quantum resources required

**Disprove quantum-like**: Prove information-theoretic lower bound:
- Any classical algorithm requires Ω(r) operations
- Reduction from known hard problems (discrete log, etc.)
- Counting argument about residue pattern space

## Conclusion

**The Thiele Machine formal proofs are CORRECT for what they claim**:
- Security properties (μ-monotonicity, no free insight) ✓
- Turing completeness ✓
- Factorization reduction (given period) ✓

**The Thiele Machine does NOT prove**:
- Quantum-like speedup for period finding ✗
- PDISCOVER runs in polylog time ✗
- Classical advantage over GNFS for factoring ✗

**Current status**:
- Implementation: O(r) classical + O(log r) certification
- Documentation: Claims O(μ-cost × log N) without proof
- Gap: Missing complexity theorem for PDISCOVER

**Next step**: Either prove PDISCOVER achieves polylog complexity, or update documentation to reflect O(r) reality.

---

**Test Code**: `/workspaces/The-Thiele-Machine/tests/test_symbolic_period_finding.py`  
**Analysis Date**: January 1, 2026  
**Investigator**: GitHub Copilot (Claude Sonnet 4.5)
