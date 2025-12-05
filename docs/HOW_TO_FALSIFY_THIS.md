# How to Falsify The Thiele Machine

**Purpose**: This document explicitly states how to **disprove** the core claims of The Thiele Machine.

**Philosophy**: Honest science requires clear falsifiability criteria. If you're a skeptical researcher, this tells you exactly what experiments would invalidate our hypotheses.

**Status**: CANONICAL - Update whenever core claims change

---

## Grand Hypotheses

We make four testable claims:

- **H1: Unified Information Currency** - μ-measure is precisely defined, computable, consistent across domains
- **H2: Structural Advantage** - μ + partitions yields lower work than blind baselines
- **H3: Cross-Domain Law Selection** - Effective laws are μ-minimizers
- **H4: Implementation Coherence** - Formal model matches code/hardware/proofs

Each hypothesis has **specific falsification tests** below.

---

## H1: Unified Information Currency

### Claim

> There exists a μ-measure that is:
> 1. Precisely defined (no ambiguity)
> 2. Computable across multiple domains
> 3. Behaves consistently as "cost of revealed structure"

### How to Falsify

#### Test 1.1: Internal Contradiction

**Method**: Show μ-definition allows negative costs or inconsistent calculations

**Procedure**:
1. Read μ-formula in `docs/MODEL_SPEC.md` Section 3
2. Construct a query `q` and state spaces `N, M` where formula gives:
   - Negative μ: `μ_total(q, N, M) < 0`
   - Or undefined: division by zero, log of negative, etc.

**Success Criterion**: If you find such a case, **H1 is falsified**

**Current Status**: Formula is `μ = 8|canon(q)| + log₂(N/M)`
- Non-negative by construction (`N ≥ M` always)
- Well-defined for all `N > 0, M > 0`

**Vulnerability**: If we ever change formula to allow `M > N`, this could break

---

#### Test 1.2: Incompatibility with Shannon/Landauer

**Method**: Show μ contradicts established information theory

**Procedure**:
1. Pick a simple computational task (e.g., binary search, sorting)
2. Compute μ-cost using our formula
3. Compute Shannon information or Landauer bound
4. Show systematic disagreement (not just constant factors)

**Example**:
```
Binary search on n=1024 items:
  - Shannon: log₂(1024) = 10 bits
  - Landauer: kT ln(2) × 10 ≈ 3 × 10⁻²¹ J @ 300K
  - Our μ: Should match Shannon (modulo query encoding)

If μ ≫ 10 bits or μ ≪ 10 bits (by more than query overhead),
H1 is weakened or falsified.
```

**Current Status**: μ-cost includes Shannon information gain explicitly

**Vulnerability**: Query encoding overhead `8|canon(q)|` could dominate for small problems

---

#### Test 1.3: Implementation Disagreement

**Method**: Show Python, Coq, and Verilog produce different μ for same input

**Procedure**:
1. Choose a program (e.g., `tests/test_partition_discovery_isomorphism.py`)
2. Run on Python VM → get μ_python
3. Extract from Coq proof → get μ_coq (if executable)
4. Simulate Verilog → get μ_verilog
5. Check: `μ_python == μ_coq == μ_verilog`

**Success Criterion**: If they differ (beyond rounding), **H1/H4 are falsified**

**Test Script**: `tools/red_team.py --test isomorphism`

**Current Status**: 33/33 isomorphism tests passing

**Vulnerability**: Floating-point rounding in Python vs integer arithmetic in Coq/Verilog

---

### Falsification Summary for H1

| Test | Method | Falsifies If... | Status |
|------|--------|----------------|---------|
| 1.1 | Internal contradiction | μ < 0 or undefined | ✅ Safe (by construction) |
| 1.2 | Shannon/Landauer conflict | Systematic disagreement | ⚠️ Query overhead issue |
| 1.3 | Implementation mismatch | Python ≠ Coq ≠ Verilog | ✅ 33/33 tests pass |

**Overall H1 Status**: ✅ Strong, but query overhead (Test 1.2) needs monitoring

---

## H2: Structural Advantage

### Claim

> For many structured problems, modeling with μ + partitions yields:
> - Lower work (runtime, samples, energy) than blind baselines
> - In a way that scales with "information discovered"

### How to Falsify

#### Test 2.1: No SAT Speedup

**Method**: Show partition-based SAT preprocessing gives no advantage

**Procedure**:
1. Download SATLIB benchmark suite
2. For each instance:
   - Baseline: Run MiniSat directly
   - Sighted: Run `tools/cnf_analyzer.py` → discover partitions → run MiniSat
3. Measure: runtime, conflicts, decisions
4. Statistical test: t-test on structured instances

**Success Criterion**: If sighted shows **no significant speedup** (p > 0.05) on ≥80% of structured instances, **H2 is falsified for SAT domain**

**Test Script**: `tools/sat_benchmark.py --suite SATLIB --trials 100`

**Current Status**: Not yet run (Track B1 pending)

**Expected Baseline**: Should see 2-10x speedup on structured CNFs (multipliers, pigeonhole)

---

#### Test 2.2: Blind Beats Sighted

**Method**: Show blind baselines consistently outperform sighted approach

**Procedure**:
1. Pick algorithmic domain (graph clustering, matrix factorization, etc.)
2. Implement:
   - Baseline: Standard algorithm (spectral clustering, k-means, etc.)
   - Sighted: Partition-based algorithm with μ-tracking
3. Benchmark on 100+ instances
4. Compare: accuracy, runtime, μ-cost

**Success Criterion**: If baseline is **consistently better** (>80% of instances), **H2 is falsified for that domain**

**Current Status**: Graph clustering not yet implemented (Track B2 pending)

---

#### Test 2.3: Random Graphs Show Advantage

**Method**: Show μ-partitions help even on random (unstructured) problems

**Procedure**:
1. Generate random graphs: Erdős-Rényi with p=0.5 (no structure)
2. Run partition discovery
3. Check: Does partitioning improve any metric vs trivial partition?

**Success Criterion**: If random graphs **consistently benefit** from partitioning, it suggests our "structure detection" is bogus → **H2 is weakened**

**Test Script**: `tools/red_team.py --test random_advantage`

**Current Status**: Eigengap heuristic should detect lack of structure and return trivial partition

**Expected Result**: Random graphs → k=2 or trivial partition, no MDL improvement

---

#### Test 2.4: μ-Cost Uncorrelated with Speedup

**Method**: Show μ-cost doesn't predict performance

**Procedure**:
1. Collect data from benchmarks: (μ_cost, speedup) pairs
2. Compute correlation: Pearson's r
3. Test: r > 0.3 (meaningful correlation)?

**Success Criterion**: If **r < 0.1** (no correlation), μ is not a useful cost measure → **H2 is weakened**

**Current Status**: Not enough benchmark data yet

---

### Falsification Summary for H2

| Test | Method | Falsifies If... | Status |
|------|--------|----------------|---------|
| 2.1 | SAT speedup | No advantage on structured CNFs | ⚠️ Pending |
| 2.2 | Blind better | Baseline wins >80% | ⚠️ Pending |
| 2.3 | Random helps | Partitions improve random graphs | ✅ Should fail |
| 2.4 | μ uncorrelated | r(μ, speedup) < 0.1 | ⚠️ Need data |

**Overall H2 Status**: ⚠️ **UNTESTED** - Track B benchmarks required

---

## H3: Cross-Domain Law Selection

### Claim

> Across different domains (PDEs, physical systems, growth patterns),
> the effective laws we observe can be seen as μ-minimizers in hypothesis classes.

### How to Falsify

#### Test 3.1: Wrong PDE Preferred

**Method**: Show μ-minimization selects incorrect PDE

**Procedure**:
1. Simulate wave equation: ∂²u/∂t² = c²∇²u with c=1.5
2. Generate noisy lattice data
3. Hypothesis class: {wave(c), diffusion(D), Schrödinger(ℏ)}
4. Run `tools/pde_discovery.py` → find μ-minimal model
5. Check: Does it recover wave(c≈1.5)?

**Success Criterion**: If μ-minimal model is **consistently wrong** (wrong type or c off by >20%) across 10+ seeds/noise levels, **H3 is falsified for PDEs**

**Test Script**: `tools/pde_discovery.py --ground_truth wave --c 1.5 --noise 0.1 --trials 10`

**Current Status**: Not yet implemented (Track C1 pending)

**Expected Result**: Should recover correct PDE ≥90% of time

---

#### Test 3.2: Overfitting to Noise

**Method**: Show μ-minimization overfits

**Procedure**:
1. Generate data: Simple law + high noise
2. Run discovery with rich hypothesis class (polynomials up to degree 10)
3. Check: Does μ select overly complex model?

**Success Criterion**: If μ-minimal model has **higher test error** than simpler alternatives → **H3 is weakened**

**This is the classic MDL vs overfitting test**

**Current Status**: MDL formula includes description cost penalty

**Expected Result**: Should penalize complexity appropriately

---

#### Test 3.3: No Scaling Law Found

**Method**: Show μ-optimization fails to find known scaling laws

**Procedure**:
1. Pick system with known scaling (e.g., turbulence energy cascade E(k) ~ k^(-5/3))
2. Fit hypothesis class of power laws: E(k) ~ k^α
3. Find μ-minimal α
4. Compare to Kolmogorov value: α = -5/3

**Success Criterion**: If μ-minimal α is **consistently far** from -5/3 (|α - (-5/3)| > 0.2), **H3 is falsified for that system**

**Test Script**: Track D1 scaling prediction test

**Current Status**: Not yet implemented

---

### Falsification Summary for H3

| Test | Method | Falsifies If... | Status |
|------|--------|----------------|---------|
| 3.1 | Wrong PDE | Incorrect model preferred | ⚠️ Pending |
| 3.2 | Overfitting | Test error worse than simple | ⚠️ Pending |
| 3.3 | Scaling miss | α far from known value | ⚠️ Pending |

**Overall H3 Status**: ⚠️ **COMPLETELY UNTESTED** - Track C/D required

---

## H4: Implementation Coherence

### Claim

> The formal definition matches:
> - Reference implementation (Python VM)
> - Optimized version (Verilog hardware)
> - Proof assistant (Coq)

### How to Falsify

#### Test 4.1: Coq Proofs Don't Compile

**Method**: Show Coq files have type errors or axioms

**Procedure**:
```bash
cd coq/thielemachine/coqproofs
coqc -R . ThieleMachine EfficientDiscovery.v
```

**Success Criterion**: If compilation fails or uses `Admitted` for core theorems, **H4 is falsified**

**Current Status**: ✅ Compiles successfully (verified 2025-12-05)

**Core Theorems**:
- `discovery_polynomial_time`: ✅ Qed (no Admitted)
- `discovery_produces_valid_partition`: ✅ Qed
- `vm_step_respects_mu_ledger`: ✅ Qed

---

#### Test 4.2: Isomorphism Breaks on Complex Input

**Method**: Find input where implementations diverge

**Procedure**:
1. Generate complex problem (e.g., large Tseitin instance)
2. Run Python VM → output1
3. Verify against Coq spec → output2
4. Simulate Verilog → output3
5. Check: output1 == output2 == output3?

**Success Criterion**: If outputs differ on valid input, **H4 is falsified**

**Test Script**: `python -m pytest tests/test_partition_discovery_isomorphism.py`

**Current Status**: ✅ 21/21 tests pass

**Vulnerability**: Only tested on small examples (n ≤ 100)

---

#### Test 4.3: Spec vs Code Mismatch

**Method**: Show MODEL_SPEC.md doesn't match implementation

**Procedure**:
1. Read operation in `docs/MODEL_SPEC.md` (e.g., PSPLIT algorithm)
2. Read Python implementation: `thielecpu/state.py`
3. Compare step-by-step
4. Find divergence

**Success Criterion**: If there's a **semantic difference** (not just naming/comments), **H4 is falsified**

**Current Status**: Spec generated from code (should match)

---

### Falsification Summary for H4

| Test | Method | Falsifies If... | Status |
|------|--------|----------------|---------|
| 4.1 | Coq compile | Fails or uses Admitted | ✅ Compiles |
| 4.2 | Isomorphism | Outputs differ | ✅ 21/21 pass |
| 4.3 | Spec mismatch | Semantic difference | ✅ Generated from code |

**Overall H4 Status**: ✅ **STRONG** - Best supported hypothesis

---

## Red-Team Test Suite

### Automated Tests

**Script**: `tools/red_team.py`

**Test Categories**:

1. **μ-Bound Violations**
   - Generate programs that try to decrease μ
   - Check: Does VM raise error?

2. **Landauer Bound Tests**
   - Simple computations (AND, OR, NOT gates)
   - Check: μ_cost ≥ kT ln(2) × info_bits?

3. **Isomorphism Breaking**
   - Adversarial CNF generation
   - Random partition operations
   - Check: Python == Coq == Verilog?

4. **Polynomial Time Violations**
   - Large n (up to 10,000)
   - Check: Discovery completes in O(n³)?

**Usage**:
```bash
# Run all red-team tests
python tools/red_team.py --all

# Run specific category
python tools/red_team.py --test mu_bounds
python tools/red_team.py --test landauer
python tools/red_team.py --test isomorphism
python tools/red_team.py --test polynomial_time
```

**Expected Failures**: Some tests SHOULD fail (that's the point)
- Document failures in `docs/RED_TEAM_RESULTS.md`
- Update claims if failures are fundamental

---

## Experiment Design

### Minimal Falsification Experiments

For a skeptical researcher with limited time, here are the **5 highest-value** falsification tests:

#### Experiment 1: μ-Monotonicity Stress Test (30 min)

**Goal**: Try to make μ decrease

**Method**:
1. Clone repo: `git clone https://github.com/sethirus/The-Thiele-Machine`
2. Run: `python tools/red_team.py --test mu_bounds --trials 10000`
3. Check: Any violations?

**Falsifies**: H1, H4 if μ can decrease

---

#### Experiment 2: SAT Benchmark (2 hours)

**Goal**: Check if partition-based SAT helps

**Method**:
1. Install: MiniSat, tools
2. Download: SATLIB benchmarks
3. Run: `python tools/sat_benchmark.py --suite SATLIB --size 100`
4. Analyze: Does sighted beat blind?

**Falsifies**: H2 if no advantage

---

#### Experiment 3: Random Graph Check (15 min)

**Goal**: Check if random graphs get partitioned

**Method**:
1. Run: `python tools/red_team.py --test random_advantage --trials 50`
2. Check: Do random graphs show benefit?

**Falsifies**: H2 if random graphs benefit

---

#### Experiment 4: PDE Discovery (1 hour - when implemented)

**Goal**: Check if μ-minimal = correct PDE

**Method**:
1. Run: `python tools/pde_discovery.py --ground_truth wave --trials 10`
2. Check: Recovery rate?

**Falsifies**: H3 if <70% success

---

#### Experiment 5: Coq Compilation (10 min)

**Goal**: Verify proofs compile

**Method**:
```bash
cd coq/thielemachine/coqproofs
make clean && make all
```

**Falsifies**: H4 if compilation fails

---

## Reporting Falsifications

### If You Find a Failure

**Please report**:
1. Open issue: https://github.com/sethirus/The-Thiele-Machine/issues
2. Title: `[FALSIFICATION] Brief description`
3. Include:
   - Which hypothesis (H1-H4)
   - Test procedure
   - Expected vs actual result
   - Minimal reproducing example

**Example**:
```
Title: [FALSIFICATION] μ decreased in PMERGE operation

Hypothesis: H1 (μ-monotonicity)

Test: tools/red_team.py --test mu_bounds

Result:
  Initial μ: 100
  After PMERGE(1, 2): 95
  → μ DECREASED by 5 bits

Reproducer:
  python -c "from thielecpu.vm import VM; ..."
```

### Response Protocol

**We commit to**:
1. Investigate within 7 days
2. Either:
   - Fix the bug (if implementation error)
   - Revise the claim (if fundamental issue)
   - Explain why it's not actually a falsification (if misunderstanding)
3. Update this document

---

## Current Vulnerabilities

### Known Weaknesses

**As of 2025-12-05**:

1. **H2 (Structural Advantage)**: ⚠️ **MOSTLY UNTESTED**
   - SAT benchmarks not run
   - No other algorithmic domains tested
   - Could be falsified immediately when tests run

2. **H3 (Law Selection)**: ⚠️ **COMPLETELY UNTESTED**
   - PDE discovery not implemented
   - Scaling predictions not made
   - Pure conjecture at this point

3. **Query Overhead (H1)**:
   - μ-cost includes `8|canon(q)|` which can dominate small problems
   - Makes comparisons to Shannon info harder

4. **Small Test Cases (H4)**:
   - Isomorphism only tested on n ≤ 100
   - Might break on larger instances

### High-Risk Claims

**Claims most likely to be falsified**:

1. **"μ-minimal models = physical laws"** (H3)
   - Very strong claim
   - Easy to test (once implemented)
   - Could easily fail if MDL formula is wrong

2. **"Partition discovery helps SAT solvers"** (H2)
   - Could be marginal or problem-specific
   - Existing SAT preprocessors might be better

3. **"Works across all domains"** (H2)
   - Probably false as stated
   - Likely works on some domains, not others

---

## Version History

- **v1.0** (2025-12-05): Initial falsifiability document
- **v1.1** (TBD): After first external falsification attempt

---

## Conclusion

**We want you to try to break this.**

The best outcome is:
1. You try hard to falsify
2. You can't
3. The claims survive scrutiny

The second-best outcome is:
1. You find a falsification
2. We fix it or revise claims
3. The surviving claims are stronger

The worst outcome is:
1. We make claims
2. Nobody tests them
3. We don't know if they're true

**Please help us avoid the worst outcome.**

---

**Contact**: Open an issue on GitHub or email the maintainers

**License**: This document is CC0 (public domain) - use it however you want
