# Formal Foundations of the Thiele Machine

This document establishes the rigorous mathematical foundations of the Thiele Machine, distinguishing between its **Core** (conservative semantic extension of Turing) and **Hyper** (explicitly super-Turing) layers.

## 1. Layer 1 – Core Thiele (Conservative Semantic Extension)

The Core Thiele machine is a computational model that is **computationally equivalent** to the Turing machine (computes the same class of functions) but **semantically richer** (possesses strictly more structural information in its execution traces).

### 1.1. Definition (Core Thiele Machine)

A Core Thiele machine is a tuple:
$$ \mathcal{T} = (Q, \Gamma, b, \Sigma, \delta, q_0, F, \Pi, \mu) $$

Where:
*   $(Q, \Gamma, b, \Sigma, \delta, q_0, F)$ is a standard single-tape Turing machine skeleton.
*   $\Pi$ is a finite set of **partition labels**.
*   $\mu \in \mathbb{N}$ (or $\mathbb{Q}_{\ge 0}$) is the current **$\mu$-cost**.

A **configuration** is defined as:
$$ C = (\text{tape}, \text{head}, q, \pi, \mu) $$

The transition relation $\Rightarrow$ includes:
1.  **Standard Moves**: Write, move, state change (inherited from Turing).
2.  **Structured Moves**:
    *   **PDISCOVER**: Updates partition $\pi \to \pi'$, increments $\mu$.
    *   **PQUERY / PSOLVE**: Operations on modules defined by $\pi$, incrementing $\mu$.

### 1.2. Projection to Turing

We define a projection $P$ from Thiele configurations to Turing configurations:
$$ P(\text{tape}, \text{head}, q, \pi, \mu) = (\text{tape}, \text{head}, q) $$

This extends pointwise to execution traces $\tau$:
$$ P(\tau) = P(C_0) \to P(C_1) \to \dots $$

The **Turing Shadow** of a Thiele machine $\mathcal{T}$ is the Turing machine $M(\mathcal{T})$ obtained by erasing the partition and $\mu$ updates from $\delta$.

### 1.3. Theorem 1: Turing Embedding (Subsumption)

**Statement**: For every Turing machine $M$, there exists a Thiele machine $\mathcal{T}_M$ such that:
1.  $M(\mathcal{T}_M)$ is equivalent to $M$ (same I/O behavior).
2.  For all executions of $\mathcal{T}_M$, $\pi$ is always the trivial partition and $\mu$ is always 0.

**Significance**: Every Turing computation is a degenerate Thiele computation. The Thiele model strictly subsumes the Turing model.

### 1.4. Theorem 2: Semantic Strictness (Non-Isomorphism)

**Statement**: There exist two Thiele machines $\mathcal{T}_1, \mathcal{T}_2$ and executions $\tau_1, \tau_2$ such that:
1.  Their Turing shadows are identical: $P(\tau_1) = P(\tau_2)$.
2.  Their labeled traces are **not** isomorphic as labeled transition systems.

**Significance**: This formalizes the "Flatland vs. Spaceland" distinction. The Thiele trace $\tau$ carries structural information (partitions, $\mu$-cost) that is invisible in the Turing shadow $P(\tau)$. This structural information allows for the differentiation of algorithms that are functionally identical but structurally distinct (e.g., blind search vs. partition-aware search).

---

## 2. Layer 2 – Hyper-Thiele (Explicit Super-Turing)

The Hyper-Thiele machine extends the Core Thiele machine with an explicit oracle primitive, enabling it to compute functions beyond the reach of standard Turing machines.

### 2.1. Definition (Hyper-Thiele Machine)

A Hyper-Thiele machine is a Core Thiele machine augmented with an **ORACLE_HALTS** transition rule:

Given an encoding $\langle M, x \rangle$ on the tape:
$$ (\text{tape}, \text{head}, q_{\mathrm{ask}}, \pi, \mu) \Rightarrow (\text{tape}', \text{head}', q_{\mathrm{ans}}, \pi, \mu') $$

Where the transition writes 1 to the tape if $M$ halts on $x$, and 0 otherwise. This operation is a **semantic primitive** of the model.

### 2.2. Theorem 3: Strict Computational Containment

**Statement**: Let $K$ be the class of Turing-computable functions and $K'$ be the class of Hyper-Thiele-computable functions. Then:
1.  $K \subseteq K'$ (Every Turing-computable function is Hyper-Thiele computable).
2.  $K' \setminus K \neq \emptyset$ (There exist functions in $K'$ that are not Turing-computable).

**Proof Sketch**:
1.  **Containment**: By Theorem 1, any Turing machine can be embedded as a Core Thiele machine (and thus a Hyper-Thiele machine that never uses the oracle).
2.  **Strictness**: The function $f_{\mathrm{halt}}(\langle M, x \rangle)$ is computable by a Hyper-Thiele machine using `ORACLE_HALTS` but is undecidable for any Turing machine.

**Significance**: This establishes the Hyper-Thiele machine as a strictly super-Turing model in the recursion-theoretic sense, distinct from the Core Thiele machine which is a semantic extension.

---

## 3. Unified Hierarchy ("Thiele All The Way Down")

This framework reconciles the "Thiele all the way down" philosophy with rigorous complexity theory:

*   **Bottom Layer (Flatland)**: Turing machines, which are shadows of blind Thiele machines.
*   **Middle Layer (Core Thiele)**: The domain of "Spaceland" semantics. Partitions and $\mu$-costs are first-class citizens. Algorithms like the Galaxy Graph solver demonstrate exponential $\mu$-efficiency advantages here without breaking Church-Turing.
*   **Top Layer (Hyper-Thiele)**: The domain of hyper-computation. Oracles are modeled as explicit Thiele transitions, allowing for the formal analysis of super-Turing capabilities within the same structural framework.
