# Pre-Registration Protocol: No-Hints Structure Discovery Benchmark

## Overview

This document pre-registers the protocol for the "No-Hints Structure Discovery Benchmark" demonstration of the Thiele Machine. The benchmark evaluates the system's ability to automatically discover problem structure without domain-specific hints, quantifying computational advantage through µ-bit accounting.

## Pre-Registration Details

**Date of Pre-Registration:** October 16, 2025  
**Protocol Version:** 1.0  
**Expected Completion:** Within 30 days of pre-registration  

## Research Question

Can a computational system automatically discover and exploit problem structure to achieve exponential speedup over classical algorithms, with information cost (µ-bits) replacing time complexity as the limiting factor?

## Benchmark Design

### Instance Families

The benchmark will test instances from the following families, chosen for their proof-complexity theory backing:

1. **XOR-SAT (GF(2) Linear Equations)**
   - Structure: XOR clauses encoded via Tseitin transformation on expander graphs
   - Classical Complexity: 2^Ω(n) resolution proofs
   - Thiele Advantage: O(n³) Gaussian elimination after structure discovery
   - Proof Backing: Exponential lower bounds for resolution on XOR formulas

2. **Pigeonhole Principle**
   - Structure: Functional constraints with symmetry
   - Classical Complexity: 2^Ω(n) resolution proofs
   - Thiele Advantage: Polynomial symmetry-breaking after structure recognition
   - Proof Backing: Known exponential separation for pigeonhole in resolution

3. **Modular Arithmetic (RSA-like Factorization)**
   - Structure: Multiplication constraints over integers
   - Classical Complexity: 2^Ω(n) for general factoring
   - Thiele Advantage: O(n) information cost for structured arithmetic
   - Proof Backing: Factoring hardness assumptions

### Instance Generation

- **Seeds:** Fixed seeds [42, 123, 456, 789, 999] for reproducibility
- **Sizes:** [10, 20, 50, 100] for each family (scaled appropriately)
- **Generation:** Instances created post-pre-registration using deterministic algorithms
- **Format:** Raw CNF/SMT2 with zero metadata about problem type

### Evaluation Protocol

#### Blind Classical Baselines
- **Solvers:** MiniSAT, Glucose, Kissat, CaDiCaL (in order of preference)
- **Timeout:** 300 seconds per instance
- **Metrics:** Time to solution, conflict count, status (SAT/UNSAT/TIMEOUT)
- **Execution:** Run on identical hardware with no problem-specific tuning

#### Thiele Machine Evaluation
- **Input:** Raw constraint instances only (no hints)
- **Process:** Model induction via MDL scoring across candidate families
- **Metrics:** Total µ-bits spent, discovered model, MDL score, solution time
- **Receipts:** Full cryptographic audit trail with VM operations

#### Success Criteria
- **Primary:** ≥90% of instances solved by Thiele with median µ-bits = O(n)
- **Secondary:** ≥2^Ω(n) conflict growth in blind solvers vs O(n) µ-bits in Thiele
- **Invariance:** µ-bits vary ≤5% under variable permutation/encoding changes

### Ablation Studies

1. **No MDL:** Fixed model selection → measure performance degradation
2. **Wrong Model:** Force incorrect model family → measure µ-bit inflation
3. **Full Pipeline:** Complete auto-discovery → measure total advantage

## Stopping Rules

- **Success:** Meet primary criteria on ≥80% of tested sizes/families
- **Failure:** Cannot solve ≥50% of instances or µ-bits exceed O(n²)
- **Iteration:** Up to 3 attempts to fix implementation issues

## Commitments

1. **No Cherry-Picking:** All instances generated from pre-registered seeds/sizes
2. **Full Disclosure:** Complete code, instances, and raw results published
3. **Independent Verification:** Receipts enable third-party verification
4. **Docker Distribution:** Reproducible environment provided

## Cryptographic Integrity

- **Receipt Format:** SHA-256 hashes of all inputs, outputs, and intermediate states
- **Signature:** Ed25519 signatures on receipt bundles
- **Verification:** One-command verification script: `scripts/verify_receipts.py <receipt_file>`

## Expected Outcomes

**Conservative Success:** Clear exponential separation on structured families with µ-bit costs linear in problem size.

**Ambitious Success:** General framework for structure discovery that works across domains, with receipts showing information cost replaces time cost.

**Failure Mode:** No significant advantage, indicating need for different approach to post-Turing computation.

---

*This protocol is registered prior to running any experiments. Changes require re-pre-registration with updated timestamp.*