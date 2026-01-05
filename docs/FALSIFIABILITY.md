# Falsifiability Criteria for Physical Claims

**Last Reviewed**: January 4, 2026

This document defines **explicit falsification criteria** for major physical claims in the Thiele Machine project.

## Claim Classification

- **[PROVEN]**: Formally verified in Coq
- **[IMPLEMENTED]**: Verified by testing across implementation layers
- **[CONJECTURED]**: Proposed but not experimentally validated
- **[SPECULATION]**: Theoretical extension with no validation

**January 2026 Update**: Two new proven theorems establish μ as both mathematically canonical (Initiality) and physically necessary (Necessity). See [docs/THEOREMS.md](THEOREMS.md) for details.

---

## Claim 1: Supra-Quantum Correlations (16/5 CHSH Value)

### Status: [CONJECTURED]

### Claim
The Thiele Machine can produce correlations with CHSH = 16/5 = 3.2, exceeding the quantum Tsirelson bound of 2√2 ≈ 2.828.

### What is PROVEN
- **[PROVEN]**: The probability distribution `supra_quantum_ns` mathematically achieves CHSH = 16/5
  - File: [coq/sandboxes/AbstractPartitionCHSH.v](../coq/sandboxes/AbstractPartitionCHSH.v), lines 490-546
  - Theorem: `sighted_is_supra_quantum`
- **[PROVEN]**: The distribution satisfies no-signaling constraints
  - Lemma: `supra_quantum_valid`
- **[PROVEN]**: 16/5 > 2√2 (algebraic inequality)
  - Lemma: `supra_quantum_exceeds_tsirelson`

### What is CONJECTURED
- **[CONJECTURED]**: Physical hardware can implement this distribution
- **[CONJECTURED]**: The implementation preserves no-signaling under noise
- **[CONJECTURED]**: The measurement process doesn't introduce hidden variables

### Falsification Criteria

**Definitive Falsification:**
1. Experimental CHSH value ≤ 2√2 in all trials
2. Detection of signaling (information transfer) between measurement stations
3. Proof that the distribution requires hidden variables (local realism)
4. Discovery of mathematical error in Coq proof (unlikely but possible)

**Required Measurement:**
- Apparatus: Two spatially separated measurement stations
- Protocol: CHSH game with random input choices
- Sample size: N ≥ 10,000 trials for 3σ confidence
- Success criterion: CHSH > 2.83 (accounting for statistical noise)

**Cost Estimate:**
- Academic lab setup: $10K-$50K (photonics or atomic systems)
- Commercial vendor: $100K-$500K (full turn-key system)
- DIY hobbyist: $1K-$5K (using commodity hardware, low fidelity)

**Current Status:**
- No experimental implementation exists
- No funding secured for experimental validation
- Mathematical proof complete

---

## Claim 2: Partition-Native Computing Advantage

### Status: [IMPLEMENTED]

### Claim
Partition operations (PNEW, PSPLIT, PMERGE) provide computational advantages over classical computing for certain problem classes.

### What is PROVEN
- **[PROVEN]**: Partition semantics are well-defined in Coq
  - Files: [coq/kernel/PartitionOps.v](../coq/kernel/PartitionOps.v), [coq/kernel/VMState.v](../coq/kernel/VMState.v)
- **[IMPLEMENTED]**: Python ↔ OCaml ↔ Verilog isomorphism for partition ops
  - Tests: [tests/test_partition_isomorphism_minimal.py](../tests/test_partition_isomorphism_minimal.py)

### What is CONJECTURED
- **[CONJECTURED]**: The advantage scales to real-world problem sizes
- **[CONJECTURED]**: Physical implementations preserve the mathematical advantage
- **[SPECULATION]**: The advantage applies to NP-complete problems

### Falsification Criteria

**Definitive Falsification:**
1. Proof that all partition programs can be efficiently simulated classically
2. Discovery of polynomial-time classical algorithm for a problem claimed to require partitions
3. Demonstration that the "advantage" is purely from parallelism (nothing special about partitions)

**Required Measurement:**
- Benchmark suite: Problems with known classical complexity
- Comparison: Partition-native vs. best classical algorithm
- Metric: Wall-clock time, energy, or other resource
- Sample size: 100+ problem instances per class

**Cost Estimate:**
- Simulation study: $0 (already done in benchmarks/)
- Physical implementation: $50K-$500K depending on scale

**Current Status:**
- Simulation benchmarks show advantages for specific constructions
- No physical hardware exists
- Theoretical advantage is algorithm-dependent, not universal

---

## Claim 3: μ-Conservation Law

### Status: [PROVEN] (mathematical) + [IMPLEMENTED] (software)

### Claim
The μ-ledger monotonically increases with computational operations, enforcing a thermodynamic-like conservation law.

### What is PROVEN
- **[PROVEN]**: μ-ledger semantics are formally defined
  - File: [coq/kernel/MuLedger.v](../coq/kernel/MuLedger.v)
- **[IMPLEMENTED]**: Python VM tracks μ correctly
  - Tests: [tests/test_mu_costs.py](../tests/test_mu_costs.py)
  - Tests: [tests/test_rtl_mu_charging.py](../tests/test_rtl_mu_charging.py)

### What is CONJECTURED
- **[CONJECTURED]**: μ corresponds to a physical thermodynamic quantity
- **[SPECULATION]**: μ-conservation proves physical realizability bounds

### Falsification Criteria

**Definitive Falsification:**
1. Discovery of partition program where μ decreases (violates monotonicity)
2. Proof that μ-ledger is redundant (can be eliminated without changing semantics)
3. Counterexample showing μ-costs don't match physical energy costs

**Required Measurement:**
- Test suite: Edge cases for μ-accounting (already exists)
- Verification: Cross-layer isomorphism for μ-ledger state
- Physical measurement: Energy consumption vs. μ-ledger in hardware

**Cost Estimate:**
- Software verification: $0 (already done)
- Hardware verification: $10K-$100K (power measurement on custom ASIC)

**Current Status:**
- Mathematical definition complete
- Software implementation verified
- No physical hardware to measure actual energy

---

## Claim 4: Turing Equivalence (Blind Mode)

### Status: [IMPLEMENTED]

### Claim
Thiele Machine with trivial partition (no PNEW/PSPLIT/PMERGE) is Turing-equivalent to classical computing.

### What is PROVEN
- **[IMPLEMENTED]**: Blind mode executes Python code identically to CPython
  - Tests: [tests/test_showcase_programs.py::TestBlindModeTuringMachine](../tests/test_showcase_programs.py)
  - Example: [examples/showcase/blind_mode_turing.py](../examples/showcase/blind_mode_turing.py)

### What is CONJECTURED
- **[CONJECTURED]**: The formal Coq model subsumes all Turing-computable functions
- **[SPECULATION]**: Non-blind mode exceeds Turing capabilities (false - Church-Turing thesis holds)

### Falsification Criteria

**Definitive Falsification:**
1. Turing-computable function that cannot be expressed in blind mode
2. Proof that blind mode is weaker than Turing machines
3. Discovery of a blind-mode program that halts when it shouldn't (or vice versa)

**Required Measurement:**
- Test suite: Classical algorithms (sorting, searching, arithmetic)
- Verification: Output equivalence to reference implementations
- Counterexample: Any Turing machine that cannot be encoded

**Cost Estimate:**
- Test suite execution: $0 (already exists)
- Formal Turing equivalence proof: 100-500 hours (Coq expert time)

**Current Status:**
- Empirical testing shows equivalence for tested cases
- No formal proof of full Turing equivalence (would require large Coq development)
- No known counterexamples

---

## Claim 5: No Hidden Variables in Supra-Quantum Correlations

### Status: [CONJECTURED]

### Claim
The supra-quantum correlations cannot be explained by local hidden variable theories.

### What is PROVEN
- **[PROVEN]**: The distribution violates Bell/CHSH inequality (mathematical)
  - Theorem: `sighted_is_supra_quantum` in [AbstractPartitionCHSH.v](../coq/sandboxes/AbstractPartitionCHSH.v)

### What is CONJECTURED
- **[CONJECTURED]**: Physical implementation has no hidden variables
- **[SPECULATION]**: The partition graph itself is the "hidden variable" (needs analysis)

### Falsification Criteria

**Definitive Falsification:**
1. Construction of local hidden variable model that reproduces CHSH = 16/5
2. Proof that partition graph encodes "hidden" correlations accessible to both parties
3. Detection of classical communication channel between measurement stations

**Required Measurement:**
- Protocol: Full Bell test with locality loopholes closed
- Apparatus: Space-like separated stations with fast random number generators
- Sample size: N ≥ 100,000 trials
- Analysis: Loophole-free Bell inequality violation

**Cost Estimate:**
- Academic setup: $100K-$1M (photon polarization or atomic systems)
- Commercial vendor: $1M+ (turn-key loophole-free system)

**Current Status:**
- No experimental setup exists
- Mathematical proof shows correlation exceeds classical bounds
- Question of "hidden variables" is open and requires experimental test

---

## Claim 6: Silicon-Enforced Isomorphism Transcends Physical Limits

### Status: [SPECULATION]

### Claim
Hardware implementation of partition semantics allows behaviors not achievable in physical quantum systems.

### What is PROVEN
- **Nothing**: This is pure speculation

### What is CONJECTURED
- **[SPECULATION]**: Silicon can enforce isomorphism that quantum systems cannot
- **[SPECULATION]**: Mathematical precision transcends physical noise limits

### Falsification Criteria

**Definitive Falsification:**
1. Proof that all partition behaviors can be simulated by quantum systems
2. Demonstration that hardware noise destroys the claimed advantage
3. Theoretical impossibility proof (e.g., from thermodynamics or information theory)

**Required Measurement:**
- Comparison: Partition hardware vs. quantum hardware on same task
- Metric: Success probability, fidelity, or other performance measure
- Environment: Realistic noise and decoherence

**Cost Estimate:**
- Unknown (requires both custom partition hardware AND quantum hardware)
- Estimated: $1M-$10M for fair comparison

**Current Status:**
- Purely speculative
- No evidence for or against
- Should be labeled as [SPECULATION] in all communications

---

## Summary Table

| Claim | Status | Falsification Cost | Current Evidence | Next Step |
|-------|--------|-------------------|------------------|-----------|
| Supra-quantum CHSH=16/5 | [CONJECTURED] | $10K-$500K | Mathematical proof only | Build apparatus |
| Partition advantage | [IMPLEMENTED] | $0-$500K | Simulation benchmarks | Physical hardware |
| μ-conservation | [PROVEN]+[IMPL] | $0 | Software verified | Hardware measurement |
| Turing equivalence | [IMPLEMENTED] | $0 | Empirical tests pass | Formal Coq proof |
| No hidden variables | [CONJECTURED] | $100K-$1M | Math proof only | Loophole-free test |
| Transcends physics | [SPECULATION] | $1M-$10M | None | Downgrade claim |

---

## Methodology for Future Claims

Any new physical claim must include:

1. **Status label**: [PROVEN], [IMPLEMENTED], [CONJECTURED], or [SPECULATION]
2. **Falsification criteria**: Explicit conditions that would disprove the claim
3. **Required measurement**: Apparatus, protocol, sample size, success criterion
4. **Cost estimate**: Best guess for experimental validation
5. **Current status**: What evidence exists today

---

**Last updated**: 2025-12-19  
**Note**: Solo research project, no institutional affiliation
