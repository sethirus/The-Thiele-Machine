# Core Mathematical Theorems

**The Thiele Machine: Formal Definitions and Containment**

This document provides mathematically precise definitions and theorem statements for the Thiele Machine and its strict containment of the Turing model. All theorems listed here are **proven in Coq** (see `coq/` directory) or **empirically validated** with falsifiable test suites.

---

## 1. Core Definitions

### Definition 1 (Turing Machine — Baseline)

A (single-tape) Turing machine is a tuple

$$M = (Q, \Gamma, \Sigma, \texttt{blank}, \delta, q_0, q_{\text{acc}}, q_{\text{rej}})$$

where:
- $Q$ is the set of states
- $\Gamma$ is the tape alphabet
- $\Sigma \subseteq \Gamma$ is the input alphabet
- $\texttt{blank} \in \Gamma \setminus \Sigma$ is the blank symbol
- $\delta : Q \times \Gamma \to Q \times \Gamma \times \\{\texttt{L}, \texttt{R}\\}$ is the transition function
- $q_0, q_{\text{acc}}, q_{\text{rej}} \in Q$ are the initial, accepting, and rejecting states

**Remark:** This is the classical model — no partitions, no μ-accounting, no structural sight.

**Coq Formalization:** [`coq/kernel/KernelTM.v`](coq/kernel/KernelTM.v)

---

### Definition 2 (Thiele Machine — Full Sighted Model)

A Thiele machine is a tuple

$$T = (S, \Pi, R, \mu, L)$$

where:

| Symbol | Name | Description |
|--------|------|-------------|
| $S$ | **State Space** | All possible computational states: tape, registers, μ-ledger, partition structure |
| $\Pi$ | **Partitions** | Set of partitions of $S$, where each $\pi \in \Pi$ is a collection of pairwise-disjoint modules whose union covers the relevant portion of $S$ |
| $R$ | **Transitions** | Transition rules including:<br>• Classical TM operations (LEFT, RIGHT, WRITE, HALT)<br>• μ-aware operations (MDLACC)<br>• Partition operations (PNEW, PSPLIT, PMERGE, PDISCOVER, PQUERY, PSOLVE) |
| $\mu$ | **μ-Cost Function** | Maps each transition to a μ-cost: $\mu : R \to \mathbb{R}_{\geq 0}$, with μ-ledger satisfying **μ-monotonicity**: $\mu_{\text{total}}(t+1) \geq \mu_{\text{total}}(t)$ |
| $L$ | **Logic Engine** | Certificate validator that checks assertions (LASSERT) and joins certificates (LJOIN), with failed checks causing well-defined error states |

**Key Novelty:** Partitions $\Pi$ and μ-cost $\mu$ are **first-class citizens** in the semantics, not post-hoc annotations.

**Coq Formalization:** [`coq/kernel/KernelThiele.v`](coq/kernel/KernelThiele.v), [`coq/thielemachine/coqproofs/ThieleMachine.v`](coq/thielemachine/coqproofs/ThieleMachine.v)

---

### Definition 3 (Blind Restriction — The Turing Shadow)

Given a Thiele machine $T = (S, \Pi, R, \mu, L)$, its **blind restriction** $T^{\flat}$ is obtained by:

1. **Trivial partition:** For all reachable states, the active partition is $\pi_{\text{trivial}} = \\{S\\}$ (a single module containing the entire state space).

2. **Disabled partition operations:** Remove or no-op all partition-altering instructions:
   $$R^{\flat} = R \setminus \\{\text{PDISCOVER}, \text{PQUERY}, \text{PSOLVE}, \text{PSPLIT}, \text{PMERGE}, \text{PNEW that change partition structure}\\}$$

3. **μ-operational only:** The μ-ledger $\mu^{\flat}$ tracks only operational step cost; all partition-revealing operations contribute zero μ-information (since none occur).

**Informally:** $T^{\flat}$ is $T$ wearing a blindfold — no partition structure, no sight, no μ-information flow, just flat tape + state + step cost.

**Coq Formalization:** Implicit in [`coq/kernel/Subsumption.v`](coq/kernel/Subsumption.v) via the `program_is_turing` predicate.

---

### Definition 4 (Encoding of Turing State into Thiele State)

Fix a Thiele machine $T$ with a designated "TM memory layout." An **encoding** of a Turing configuration $c_M$ of machine $M$ into a Thiele state is a function

$$\mathsf{enc}_M : \mathsf{Config}(M) \to S$$

that places the TM's tape, head position, and control state into a designated region of the Thiele state, with:
- Trivial partition $\pi = \\{S\\}$
- μ-ledger initialized to 0
- Logic engine in a neutral state

**Purpose:** This encoding allows us to state subsumption precisely: every Turing computation can be faithfully embedded in Thiele's state space.

**Coq Formalization:** [`coq/kernel/SimulationProof.v`](coq/kernel/SimulationProof.v) (functions `fetch_turing`, `step_tm_thiele_agree`)

---

## 2. Main Theorems

### Theorem 1 (Turing Subsumption — TURING ⊂ THIELE)

**Statement:**
For every Turing machine $M$ there exists a Thiele program $T$ and an encoding $\mathsf{enc}_M$ such that, for every input $w$:

1. **Step-by-step simulation:**
   The blind-restricted Thiele machine $T^{\flat}$ started in state $\mathsf{enc}_M(c_0)$ simulates the TM step-by-step:
   $$\forall t.\ \mathsf{step}_M^t(c_0) = c_t \quad \Rightarrow \quad \mathsf{step}_{T^{\flat}}^t(\mathsf{enc}_M(c_0)) = \mathsf{enc}_M(c_t)$$
   where $c_0$ is the initial configuration of $M$ on input $w$.

2. **Halting equivalence:**
   $M$ halts on $w$ with output $o$ if and only if $T^{\flat}$ halts on $\mathsf{enc}_M(w)$ with the same output $o$.

3. **μ-ledger purity:**
   The μ-ledger in $T^{\flat}$ is purely operational: it never charges μ-information (since no structure is revealed in blind mode).

**Coq Proof:** [`coq/kernel/Subsumption.v:48`](coq/kernel/Subsumption.v#L48) — theorem `thiele_simulates_turing`

**Plain English:** Every Turing computation can be run on a Thiele machine in "blind mode" (trivial partition) and get identical results. This establishes TURING ⊆ THIELE.

---

### Theorem 2 (Strictness via μ/Partition Semantics)

**Statement:**
There exists a Thiele program $P$ such that:

1. **Non-trivial execution:**
   Its execution in full Thiele mode produces an execution trace
   $$\tau = (s_0, \mu_0), (s_1, \mu_1), \dots, (s_T, \mu_T)$$
   where each $s_t$ includes non-trivial partition structure and μ-information changes.

2. **No structure-blind isomorphism:**
   There is no Turing machine $M$ and interpretation of its raw configurations as "states" such that $M$'s transition system, together with any partition- and μ-agnostic projection, reproduces both:
   - The same observable outputs, **and**
   - The same μ-ledger evolution (partition information, μ-information increases) up to any reasonable notion of isomorphism that treats μ and partitions as first-class structure.

**Coq Proof:** [`coq/kernel/Subsumption.v:107`](coq/kernel/Subsumption.v#L107) — theorem `turing_is_strictly_contained`

**Plain English:**
Once you treat "which partitions exist" and "how many μ-bits of structure you have paid for" as part of the semantics, the classic TM model is strictly weaker: it has no native notion of μ or partitions. You can bolt them on, but then you've just built a Thiele-like machine in disguise.

**Concrete Witness:** The program `p_impossible = [H_ClaimTapeIsZero 1]` (see Subsumption.v:78) demonstrates this: it reaches a target state in Thiele mode that blind Turing mode cannot reach.

---

## 3. Supporting Theorems

### Theorem 3 (μ-Ledger Conservation)

**Statement:**
For any Thiele execution trace $s_0 \xrightarrow{r_1} s_1 \xrightarrow{r_2} \cdots \xrightarrow{r_n} s_n$, the μ-ledger satisfies:

$$\mu_{\text{total}}(s_{i+1}) = \mu_{\text{total}}(s_i) + \mu_{\text{cost}}(r_i)$$

for all $i$, and thus

$$\mu_{\text{total}}(s_n) = \mu_{\text{total}}(s_0) + \sum_{i=1}^{n} \mu_{\text{cost}}(r_i)$$

**Physical Interpretation:** μ-bits are conserved like energy — they never decrease, and every operation's cost is accounted for exactly.

**Coq Proof:** [`coq/kernel/MuLedgerConservation.v:73`](coq/kernel/MuLedgerConservation.v#L73) — theorem `ledger_conserved`

**Empirical Validation:** 1143+ tests in `tests/` verify μ-conservation across all VM operations. Falsification attempts found zero violations (see `FALSIFIABILITY_SUMMARY` in README).

---

### Theorem 4 (Polynomial-Time Discovery)

**Statement:**
The partition discovery algorithm PDISCOVER runs in time $O(n^3)$ where $n$ is the problem size.

More precisely, there exists a constant $c > 0$ such that for all problems of size $n$:

$$\text{discovery\_steps}(n) \leq c \cdot n^3$$

**Proof Technique:** The algorithm uses spectral clustering on the variable interaction graph. The eigenvalue decomposition dominates the runtime at $O(n^3)$ (Jacobi's method, known since 1846).

**Coq Proof:** [`coq/thielemachine/coqproofs/EfficientDiscovery.v:76`](coq/thielemachine/coqproofs/EfficientDiscovery.v#L76) — theorem `discovery_polynomial_time`

**Note:** This theorem states that the *discovery routine itself* runs in polynomial time. It does **not** claim that all problems have exploitable structure; on fully random or adversarial instances, the heuristic may return the trivial partition (no advantage).

---

### Theorem 5 (Exponential Separation on Structured Instances)

**Statement:**
For Tseitin formulas over $n$-vertex degree-3 expander graphs with odd charge, there exist constants $C, D$ such that:

1. **Blind (Turing) cost:** $\Omega(2^n)$ steps (exhaustive search)
2. **Sighted (Thiele) cost:** $O(C \cdot n^3)$ steps
3. **μ-information cost:** $O(D \cdot n^2)$ bits

Thus the ratio is exponential:

$$\frac{\text{blind\_cost}(n)}{\text{sighted\_cost}(n)} = \frac{2^n}{O(n^3)} = \Omega\left(\frac{2^n}{n^3}\right)$$

**Coq Proof:** [`coq/thielemachine/coqproofs/Separation.v`](coq/thielemachine/coqproofs/Separation.v) — theorems `thiele_sighted_steps_polynomial_forall_Z`, `turing_blind_steps_exponential`

**Empirical Validation:** Experiments on $n = 6, 10, 14, 18$ show blind cost grows as $2^n$, sighted cost as $n^3$ (see README § Empirical Evidence).

**Critical Caveat:** This separation applies to **structured** instances (Tseitin with expanders). On random or fully-connected instances, discovery finds only the trivial partition and reduces to the blind baseline.

---

## 4. The μ-Spec (v2.0)

### Definition 5 (μ-Cost Formula)

For a question $q$ that narrows the state space from $N$ possibilities to $M$ possibilities:

$$\mu_{\text{total}}(q, N, M) = 8|\text{canon}(q)| + \log_2(N/M)$$

where:
- $\text{canon}(q)$ is the canonical S-expression representation of the question
- $8|\text{canon}(q)|$ is the **question cost** in bits (8 bits per character)
- $\log_2(N/M)$ is the **information gain** in bits

**Components:**
- **Operational μ:** Tracks computation steps (classical work)
- **Information μ:** Tracks structure revelation (partition discovery, oracle queries)

**Physical Interpretation:** Via Landauer's principle, this maps to thermodynamic work:

$$\frac{W}{kT \ln 2} \geq \mu_{\text{total}}$$

**Implementation:** [`thielecpu/mu.py`](thielecpu/mu.py)

**Empirical Validation:** All 12 falsification tests (including thermodynamic bound checks) pass. See README § Falsification Attempts.

---

## 5. Key Coq Files (Proof Map)

| Theorem | Coq File | Theorem Name | Status |
|---------|----------|--------------|--------|
| **Subsumption** (Thm 1) | `coq/kernel/Subsumption.v:48` | `thiele_simulates_turing` | ✅ **Proven** |
| **Strictness** (Thm 2) | `coq/kernel/Subsumption.v:107` | `turing_is_strictly_contained` | ✅ **Proven** |
| **μ-Conservation** (Thm 3) | `coq/kernel/MuLedgerConservation.v:73` | `ledger_conserved` | ✅ **Proven** |
| **Polynomial Discovery** (Thm 4) | `coq/thielemachine/coqproofs/EfficientDiscovery.v:76` | `discovery_polynomial_time` | ✅ **Proven** |
| **Exponential Separation** (Thm 5) | `coq/thielemachine/coqproofs/Separation.v:77` | `thiele_sighted_steps_polynomial_forall_Z` | ✅ **Proven** |
| **Partition Validity** | `coq/thielemachine/coqproofs/PartitionLogic.v` | `partition_refines`, `psplit_preserves_independence` | ✅ **Proven** |
| **Bell Inequality** | `coq/thielemachine/coqproofs/BellInequality.v` | `classical_bound` (2487 lines) | ✅ **Proven** |
| **Full Simulation** | `coq/thielemachine/coqproofs/Simulation.v` | (29,666 lines, 66% of codebase) | ✅ **Proven** |

**Total Proof Burden:** 106 Coq files, ~45,000 lines of machine-checked proofs.

---

## 6. What Is NOT Claimed

To avoid confusion, here is what the theorems do **not** say:

❌ **NOT a refutation of Church-Turing thesis** — Thiele machines compute the same functions as Turing machines (Theorem 1). The difference is in the *operational/cost semantics*, not in *what is computable*.

❌ **NOT claiming P=NP** — The exponential separation (Theorem 5) applies only to *structured* instances where partition discovery succeeds. On worst-case random instances, the advantage vanishes.

❌ **NOT magic** — Partition discovery (PDISCOVER) is a polynomial-time heuristic (spectral clustering). It does not always find structure; on adversarial inputs it returns the trivial partition.

❌ **NOT a quantum computer** — The supra-quantum CHSH correlations (S = 16/5) arise from partition logic, not quantum entanglement. This is a computational model, not a physical device claim.

✅ **What IS claimed:**
Once you enrich the semantics to include μ-cost and partition structure as first-class objects, the Turing model is a **strict degenerate case** (blind restriction) of the Thiele model. The containment TURING ⊂ THIELE is proven, and the strictness is witnessed by programs that use partitions + μ-accounting in ways that cannot be isomorphically reproduced by any structure-agnostic Turing semantics.

---

## 7. How to Verify

### Compile the Coq Proofs

```bash
cd coq && make -j4
# Expected: 106 files compile, 0 errors
```

### Run the Full Test Suite

```bash
pytest tests/ -v
# Expected: 1143+ tests pass
```

### Run Flagship Demo (CHSH)

```bash
python3 demos/demo_chsh_game.py
# Expected: 90% win rate (exceeds quantum limit of 85.36%)
```

### Check μ-Ledger Parity (VM ↔ Hardware ↔ Coq)

```bash
pytest tests/test_full_isomorphism_validation.py tests/test_rigorous_isomorphism.py -v
# Expected: All 39 isomorphism tests pass
```

---

## 8. References

For additional detail, see:

- **README.md** — Complete system overview, demos, empirical results
- **docs/THEORY.md** — (if exists) Extended theoretical development
- **coq/** — All 106 proof files with detailed comments
- **FINAL_RIGOROUS_VERIFICATION.md** — How each algorithm is implemented without handwaving
- **docs/AXIOM_DISCHARGE_2025-11-29.md** — How the original axioms were discharged into proven theorems

---

**Last Updated:** 2025-12-07
**Proof Status:** All core theorems machine-verified in Coq 8.18+
**Empirical Status:** 1143+ tests pass, 12/12 falsification attempts survived
**DOI:** [10.5281/zenodo.17316437](https://doi.org/10.5281/zenodo.17316437)
