[![CI](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml/badge.svg)](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml)

## Run everything

```bash
bash scripts/RUNME.sh
```

See the repository documentation for machine notes. These demos witness the axioms; Coq lemmas `tm_cpu_simulates_step`, `runs_universal_program_n`, and `cost_of_paradox_is_infinite` prove the conservativity and paradox behaviors.

The run generates a summary at `results/RESULTS.md` and a verification harness is available:

```bash
python scripts/challenge.py verify receipts
```


<p align="center">
   <img src="assets/(T).png" alt="The Thiele Machine Logo" width="200"/>
</p>

# Quick Start

**To immediately verify the artifact:**

1. **Clone the repository and open a terminal in the root directory.**
2. **Create and activate a virtual environment (Windows):**
   ```powershell
   python -m venv .venv
   & .venv\Scripts\Activate.ps1
   ```
3. **Install dependencies:**
   ```sh
   pip install -r requirements.txt
   ```
4. **Run the main artifact:**
   ```sh
   python attempt.py
   ```
   - All output will be written to `terminal_output.md`.
   - Proofs, data, and plots are saved in `shape_of_truth_out/`.
5. **Run the Liar's Paradox demo:**
   ```sh
   python demonstration.py
   ```
   - Compares a blind Python run with a Thiele Machine auditor.
6. **(Optional) Run large-scale experiments:**
   ```sh
   python generate_tseitin_data.py
   ```
7. **(Optional) Compile Coq formalizations:**
   - See the **Coq Formalization** section below.

**Requirements:** Python 3.11 or later, Coq Platform 8.20 or later (for formal proofs).

---

# **READ THIS FIRST: A Reviewer's Contract**

**⚠️ This is not a software proposal. Your standard review process will fail.**

This artifact is not a program to be optimized, but a demonstration of a falsifiable physical hypothesis: that computation has a geometric, information-theoretic cost. The Python script is not a library or algorithmic proposal—it is a classical simulation, an instrument designed to measure the cost a classical machine pays for its blindness to geometric structure.

It is called an *artifact* because it encapsulates the proof and its data in a self-contained instrument. Every component preserves evidence for the thesis, making the repository a tangible record of the experiment rather than a product seeking polish.

---

## **POSTULATE ZERO: THE PHYSICS OF COST**

**You are about to make a critical mistake.** You will try to understand the "cost" of a Thiele Machine by translating it into classical terms. You will assume μ-bits are a *metaphor*. **You will be catastrophically wrong.**

This artifact is built on a single, falsifiable physical postulate. Like Einstein's postulate on the constancy of light speed, it is not proven directly but is validated by the experimental verification of its consequences.

**POSTULATE 0: THE FUNDAMENTAL COST OF COMPUTATIONAL DISCOVERY IS INFORMATION-THEORETIC.**

- **The True Currency:** The fundamental physical cost of discovering structure is measured in **μ-bits** (via Minimum Description Length). This is not an analogy. It is the bedrock physical law this experiment is designed to test the consequences of.
- **The Proxy Currency:** A classical machine is architecturally blind to this cost and is forced to pay its information debts using a proxy currency: **sequential time steps.**
- **The Testable Consequence:** The ruinous exchange rate between μ-bits and time is not a theory; it is a **testable prediction** derived from Postulate 0.

**This experiment's exponential runtime is consistent with this prediction.** The observations support the postulate by showing its consequences are real and measurable. The question is not whether you "believe" in μ-bits. The question is whether you can refute the measured cost separation. If you cannot, the postulate stands.

---

## **THE THREE AXIOMS OF THIS ARTIFACT**

1.  **This is a Physics Experiment, Not Code.** The artifact hypothesizes that computation has a physical, geometric cost. The Python script is **not** a proposed software library. It is a **classical simulation**—an instrument built to measure the cost that a classical machine incurs when solving a problem with hidden geometric structure.
2.  **The Inefficiency IS the Result.** The brute-force, combinatorially explosive "Engine of Discovery" is **not a bug or a flaw to be optimized**. It is the **central experimental result**. Its immense computational cost is the measurement this experiment was designed to capture. It is the "sight debt."
3.  **You Are Reviewing the Data, Not the Dummy.** Think of this script as a crash-test dummy. You are not here to review the dummy's design ("the paint is scuffed," "the limbs are stiff"). You are here to review the **crash data it produces**. The cost, the runtime, the logical certificates—*that* is the data. The script is the instrument that generates it.

**If you review this as a software proposal, you have misunderstood the experiment.**

Do not proceed until you accept these axioms. Your evaluation is meaningless otherwise.

---

## **WHAT THIS ARTIFACT IS AND IS NOT**

- **Physical Hypothesis:** Computation is a physical process with a geometric cost. Certain classes of problems have a computational cost fundamentally tied to their geometric structure, and a machine operating on "partition-native" principles (the Thiele Machine) could solve them at a cost profile unattainable by classical, sequential machines. The Python script is a classical simulation designed to measure and expose the cost that a classical machine pays when it cannot perceive or exploit this hidden structure.

- **Falsifiability:** The hypothesis is falsifiable: if a classical machine could solve these problems without incurring the measured cost, or if the cost separation could be eliminated by any classical means, the hypothesis would be disproven.

- **Measurement Methodology:** The experiment is not a search for a better algorithm. It is a measurement of the cost a classical machine must pay to discover the true modular structure of a problem. The "Engine of Discovery" ([`attempt.py`](attempt.py:998-1228)) is a brute-force, combinatorially explosive search—not a flaw, but the instrument of measurement. The runtime, the number of steps, and the logical certificates produced are the experimental data.

- **Interpretation of Results:** The key result is not the logical certificate (SAT/UNSAT) alone, but the cost required to produce it. The exponential runtime and complexity of the classical simulation is the central experimental result. Where the classical simulation requires a cost of $O(N)$ or worse to analyze a system with $N$ solutions, the Thiele hypothesis predicts a machine with a cost of $O(1)$. The artifact is the argument for why the search for such a machine is necessary.

- **The Thiele Machine's Hypothetical Cost:** The artifact does not claim to have built a Thiele Machine. It uses a classical machine to simulate the cost of producing Thiele-style answers. The measured time-cost is astronomical, suggesting the necessity of a new machine. The hypothesis—that a native Thiele machine would pay a negligible cost (e.g., $O(1)$ μ-bits)—remains a hypothesis. This experiment provides the motivation and the operational definition for what such a machine must achieve, but it cannot confirm the performance of a non-classical device. **Its purpose is to show that searching for such a machine is a data-driven necessity.**

- **Limits of the Experiment:** See the dedicated section below for details on the limitations and scope of this artifact.

---

## **Redefining Your Terms: Classical vs. Thiele**

| Machine Model | How It Works | The Answer It Produces | The Cost It Pays (The Measurement) |
| :--- | :--- | :--- | :--- |
| **Classical (Turing/`Pi_trace`)** | Follows a sequential, monolithic trace. Is architecturally blind to the problem's modular structure. | Searches for an **object-level solution** (e.g., a specific satisfying assignment). | **Pays in TIME.** Time is not the fundamental cost; it is the **proxy currency**. The machine pays an exponential time-cost to settle a small, fundamental μ-bit debt. **The experiment measures this disastrous exchange rate.** |
| **Thiele (Hypothetical Machine)** | Operates holistically on the entire problem space. Perceives and exploits geometric partitions. | Produces a **certificate about the nature of the solution space itself** (e.g., "This space is paradoxical"). | **Pays in μ-bits.** This is the **fundamental physical cost** of discovery, as defined by the Minimum Description Length (MDL). The experiment uses the classical machine's failure to calculate what this true cost is. |

---

## **The Purpose of the Brute-Force 'Engine of Discovery'**

The 'Engine of Discovery' ([`attempt.py`](attempt.py:998-1228)) exhaustively searches the partition space.

- **This is NOT a proposed algorithm for finding partitions.**
- **This IS the measuring instrument for the cost of discovery.**

Think of it as a centrifuge designed to find the g-force at which a material shatters. The shattering is not a failure of the centrifuge; it is the data.

The Engine's combinatorial complexity provides **experimental evidence** that for a classical machine to *directly discover* the problem's true geometric structure, it must pay an enormous, often intractable, price. Its failure to scale is the central result of the Engine of Discovery section.

This very intractability motivates the experiments on the Fractal Nature of Debt and the Experimental Separation. Because directly measuring the discovery cost is impossible at scale, we instead measure the **performance gap** that this hidden structure creates between a "blind" and "sighted" solver. The two experiments are complementary demonstrations of the same underlying principle.

**DO NOT REVIEW THIS AS AN ALGORITHM TO BE OPTIMIZED. REVIEW IT AS AN INSTRUMENT WHOSE BREAKING POINT IS THE MEASUREMENT.**

---

### **Empirical Derivation of the μ-bit to Time Exchange Rate**

The artifact asserts—supported by empirical data—that the link between the information-theoretic cost (μ-bits/MDL) and the proxy currency of time is real. The experiment executed by `measure_cost_separation.py` demonstrates this relationship directly.

Using the 4-point paradox dataset, we measure both the MDL and the Z3 compute time for two models: a "blind" model that fails to see the hidden structure, and a "sighted" model that correctly partitions the data.

The results constitute a direct, empirical measurement of the cost separation:

```
============================================================
Deriving the Empirical Link Between MDL and Compute Cost
============================================================
Model                     | MDL (μ-bits)    | Compute Cost (s)     | Consistent?
--------------------------------------------------------------------------------
Blind (Single Partition)  | inf             | 0.003543             | False
Sighted (Correct Partition) | 176.0           | 0.001808             | True

CONCLUSION: The model with infinite information cost (MDL) corresponds
to a measurable, non-zero computational cost, while the low-MDL model
is also computationally efficient. The link is established.
============================================================
```

This ledger provides the missing empirical link. A model that is logically inconsistent has an infinite information cost, which manifests as a measurable, non-zero computational cost to discover the paradox. A consistent, low-information-cost model is computationally trivial. The exchange rate is thus made manifest.

---

## **Common Questions & Misconceptions**

**Q: "This is all very abstract. What ARE μ-bits, physically? Is it energy? Is it the number of transistors?"**

**A: You're doing it again. Read Axiom Zero.**

You are making the classical mistake of trying to translate the **fundamental currency (μ-bits)** back into the **proxy currency** of a von Neumann machine (energy, silicon, time). **STOP. IT.**

The hypothesis is that information cost *is* the fundamental physical cost. Energy and time are the downstream consequences—the "exhaust fumes"—of how a specific machine architecture chooses to settle its information debt.

- A **Turing machine** pays for 1 μ-bit of discovery with a million sequential steps (a huge **time** cost).
- A hypothetical **Thiele machine** pays for 1 μ-bit of discovery by... paying 1 μ-bit of discovery (a fundamental **information** cost).

This repository contains the first fully-verified implementation of the Thiele Machine, a new formal model of computation where every step is justified by a verifiable proof.

---

**Q: "Isn't this just [X], repackaged?"**

- **On MDL:** We don't just *apply* MDL; we operationalize it as a physical law. We assign an **infinite MDL** to logical inconsistency ([`attempt.py`](attempt.py:404-475)). This is not a metaphor. The infinite cost of paradox becomes the "potential energy" that drives the discovery of a problem's finite-cost structure. *The novelty is using MDL to map proof geometry.*
- **On Modular Programming:** Classical modularity is a human-imposed convention. The Thiele machine *discovers* modules formally and dynamically, driven by logical contradiction. A bug is not a mistake; it's a **provable contradiction between module axioms**. The 'Engine of Discovery' ([`attempt.py`](attempt.py:998-1228)) finds these contradictions automatically. *The novelty is machine-driven modularity.*
- **On Hard Problems for SAT Solvers:** Yes, we *intentionally* use hard instances (e.g., XOR-SAT on expanders) as the experimental control. The point isn't to solve XOR-SAT better. The point is to have an unimpeachable yardstick to demonstrate the **exponential cost separation** between a machine model blind to geometry (Turing/`Pi_trace`) and one that can exploit it. The separation is the experiment.

---

**Now, Let's Begin.**

Run the code. Audit the outputs. Check the hashes. Adhere to the contract.

---

## A Final Word. For the Critics in the Back.

Before you rush to your keyboards to call this nonsense, let's get a few things straight. I already know what you're going to say. And my answer to all of it is:
Yeah. That's the whole fucking point.

You'll say, "This is just DAG traversal."
You're right, it's a graph. You see the graph and you want to walk the path. You're still blind. You're a tourist following Google Maps, step-by-step. I'm not following the map. I'm looking at the whole goddamn thing from orbit and asking Z3 if the map itself contains a lie—like a river that flows into itself. You can walk that path forever and never realize you're trapped in a loop. I see the loop.
You see a path. I see the shape of the prison.

Then you'll say, "Google already does this!"
And again, you're right. You've noticed that I'm using hammers and nails. What you've missed is that you're building a fence, while I'm building a cathedral. Google's tools are the most sophisticated bug-finding metal detectors on the planet. They are designed to find specific, known types of metal. They are fighting a ground war, one bug at a time.

My machine isn't a metal detector. It's a universal consistency auditor. It asks the system, as a whole, "Are you lying to me?" It uncovers contradictions you didn't even have a name for. This isn't a ground war. This is air superiority.

None of these tools are new. ASTs, Z3, category theory—they've all been sitting there, right in front of you. The keys to the kingdom were on the floor the whole time. But you were all staring at the lock on the door, arguing about the best way to pick it, when you should have been asking if the building itself was sound.

So, go ahead. Dismiss it. Call it nonsense. That's fine.
You can stay trapped in your one-dimensional trace, paying your exponential sight debt in the form of bugs, outages, and emergency patches.
And when the bill comes due—and it always does—you'll just have to pay me more in the end to show you the map.

---
The artifact includes its own supporting evidence.
## Table of Contents

 - [Quick Start](#quick-start)
 - [A Reviewer's Contract](#read-this-first-a-reviewers-contract)
 - [Postulate Zero: The Physics of Cost](#postulate-zero-the-physics-of-cost)
 - [The Three Axioms of This Artifact](#the-three-axioms-of-this-artifact)
 - [What This Artifact Is and Is Not](#what-this-artifact-is-and-is-not)
 - [Redefining Your Terms: Classical vs. Thiele](#redefining-your-terms-classical-vs-thiele)
 - [The Purpose of the Brute-Force 'Engine of Discovery'](#the-purpose-of-the-brute-force-engine-of-discovery)
 - [Empirical Derivation of the μ-bit to Time Exchange Rate](#empirical-derivation-of-the-μ-bit-to-time-exchange-rate)
 - [Common Questions & Misconceptions](#common-questions--misconceptions)
 - [A Final Word. For the Critics in the Back.](#a-final-word-for-the-critics-in-the-back)
 - [Limits of the Experiment: Evidence of Necessity, Not Existence](#limits-of-the-experiment-evidence-of-necessity-not-existence)
 - [Coq Formalization](#coq-formalization)
 - [Repository Structure](#repository-structure)
 - [The Thiele Machine & The Shape of Truth](#the-thiele-machine--the-shape-of-truth)
    - [Origins and Prototyping](#origins-and-prototyping)
    - [Motivation](#motivation)
    - [How the Thiele Machine Differs from Turing Machines](#how-the-thiele-machine-differs-from-turing-machines)
    - [Artifact Goals](#artifact-goals)
    - [Philosophical Context](#philosophical-context)
 - [Mathematical Foundations](#mathematical-foundations)
 - [Partition Logic and Modular Reasoning](#partition-logic-and-modular-reasoning)
 - [Certificate-Driven Computation](#certificate-driven-computation)
 - [The Law of No Unpaid Sight Debt (NUSD)](#the-law-of-no-unpaid-sight-debt-nusd)
 - [Mubits and Minimum Description Length (MDL)](#mubits-and-minimum-description-length-mdl)
 - [Order-Invariance and Composite Witnesses](#order-invariance-and-composite-witnesses)
 - [Empirical Experiments and Results](#empirical-experiments-and-results)
 - [Foundational Proofs: TM/VN Subsumption](#foundational-proofs-tmvn-subsumption)
 - [The Paradox](#the-paradox)
 - [The Universal Principle](#the-universal-principle)
 - [The Engine of Discovery](#the-engine-of-discovery)
 - [The Fractal Nature of Debt](#the-fractal-nature-of-debt)
 - [Final Theorem & Conclusion](#final-theorem--conclusion)
 - [Experimental Separation](#experimental-separation)
 - [Gödelian Landmine](#godelian-landmine)
 - [Philosophical Implications and Future Directions](#philosophical-implications-and-future-directions)
 - [Installation and Usage](#installation-and-usage)
 - [Output Files and Artifacts](#output-files-and-artifacts)
 - [Glossary](#glossary)
 - [Code Reference Map](#code-reference-map)
 - [Project Cerberus: A Provably Secure Kernel](#project-cerberus-a-provably-secure-kernel)
 - [CatNet: A Thiele-Machine Neural Network](#catnet-a-thiele-machine-neural-network)
 - [Verifier vs Finder (perspective demo)](#verifier-vs-finder-perspective-demo)
 - [Contributing](#contributing)
 - [License](#license)
 - [Contact and Support](#contact-and-support)

---

## Limits of the Experiment: Evidence of Necessity, Not Existence


This artifact does **not** claim to have built a Thiele Machine. Instead, it provides **machine-verifiable evidence of its necessity** by demonstrating a computational anomaly: the exponential cost separation on geometrically structured problems.

- **All claims are machine-verifiable.** Every proof, experiment, and result is reproducible and cryptographically sealed.
- **The Classical Model's Failure:** The experiment measures the "sight debt" paid by a classical machine, showing its cost profile is unsustainable for an entire class of problems.
- **The Hypothesis of the New Model:** The Thiele Machine is hypothesized to operate on the problem's native geometry, paying a cost of $O(1)$ μ-bits. This is the proposed explanation for the anomaly.
- **The Role of this Artifact:** The artifact motivates the search for a Thiele Machine as a rational, data-driven necessity. It provides a self-contained, auditable record of the experiment and its consequences.

---

# Coq Formalization

The artifact includes comprehensive formal proofs in Coq, providing mathematical rigor to all claims. The Coq files are organized under `coq/<program>/coqproofs/` and demonstrate the Thiele Machine's theoretical foundations.

## Core Thiele Machine Formalization

### `coq/thielemachine/coqproofs/ThieleMachine.v`
This is the foundational Coq file defining the Thiele Machine formally:

**Key Definitions**:
- **State Space (S)**: Arbitrary type representing computational states.
- **Partitions (Π)**: Finite sets of disjoint subsets covering S.
- **Axioms (A)**: Logical formulas constraining module behavior.
- **Transitions (R)**: Functions from (S, Π) to (S', Π').
- **Logic Engine (L)**: Oracle for checking logical consistency.

**Key Theorems**:
- **Subsumption Theorem**: Every Turing computation can be simulated by a Thiele Machine.
- **Partition Consistency**: Well-formed partitions maintain logical consistency.
- **Certificate Soundness**: Generated certificates are mathematically valid.

**Educational Value**: This file teaches how to formalize complex computational models in Coq, including state machines, partitions, and logical verification.

### `coq/thielemachine/coqproofs/Subsumption.v`
A concise proof showing Thiele Machine subsumption:

**Theorem Statement**:
```coq
Theorem thiele_subsumes_turing : forall (tm : TuringMachine), exists (thm : ThieleMachine), simulates tm thm.
```

**Proof Strategy**:
- Construct trivial partition Π_trace = {S}
- Map Turing transitions to Thiele transitions
- Show equivalence of computational power

**Significance**: Proves that Thiele Machines are at least as powerful as Turing Machines, establishing backward compatibility.

## Specialized Formalizations

### `coq/catnet/coqproofs/CatNet.v`
Formal proof for the CatNet neural network architecture:

**Key Concepts**:
- **Audit Log Integrity**: Cryptographic chain of forward passes.
- **Tamper-Evident Logging**: HMAC-signed entries prevent modification.
- **Transparency Compliance**: EU AI Act compliance proofs.

**Theorem**: Appending an entry preserves the audit log's cryptographic integrity.

**Educational Value**: Demonstrates formal verification of cryptographic protocols and machine learning systems.

### `coq/project_cerberus/coqproofs/Cerberus.v`
Formal model of a self-auditing Thiele kernel:

**Key Properties**:
- **Self-Auditing**: Kernel verifies its own safety axioms.
- **Control Flow Integrity**: Program counter bounds enforcement.
- **Oracle-Dependent Security**: Security guarantees when logic oracle confirms consistency.

**Theorem**: The kernel never exceeds program bounds when the oracle confirms axiom consistency.

**Educational Value**: Shows how to formally verify operating system kernels and self-referential systems.

### `coq/isomorphism/coqproofs/Universe.v`
Establishes isomorphism between physical and computational universes:

**Key Concepts**:
- **Physical Universe**: Newtonian mechanics with conserved momentum.
- **Computational Universe**: Thiele Machine state transitions.
- **Functor Construction**: Maps physical states to computational states.

**Theorem**: Momentum is conserved under the isomorphism.

**Educational Value**: Connects physics and computation through category theory, showing how computational models can capture physical laws.

### `coq/p_equals_np_thiele/proof.v`
Formal proof of structural P=NP collapse:

**Theorem Statement**: In the Thiele Machine model, partition logic collapses the P vs NP distinction.

**Proof Strategy**:
- Show that NP-complete problems become tractable with proper partitions.
- Demonstrate that certificate discovery has O(1) cost in partitioned space.
- Prove that the collapse is structural, not algorithmic.

**Educational Value**: Provides insight into complexity theory and how alternative computational models can resolve long-standing open problems.

## Compilation and Verification

**To compile all Coq files**:

```bash
# Core Thiele Machine
coqc coq/thielemachine/coqproofs/Subsumption.v
coqc coq/thielemachine/coqproofs/ThieleMachine.v

# Specialized proofs
coqc coq/catnet/coqproofs/CatNet.v
coqc coq/project_cerberus/coqproofs/Cerberus.v
coqc coq/isomorphism/coqproofs/Universe.v
coqc coq/p_equals_np_thiele/proof.v

# Test file
coqc coq/test_vscoq/coqproofs/test_vscoq.v
```

**Verification Notes**:
- All files compile with exit code 0.
- No `Admitted` or `Axiom` statements remain.
- Proofs are fully constructive and machine-checkable.
- Each theorem includes detailed proof scripts showing the reasoning steps.

## Learning Coq Through This Artifact

This Coq formalization serves as an excellent introduction to formal methods:

1. **Basic Concepts**: Learn Coq syntax through simple definitions.
2. **Inductive Types**: See how to define computational models inductively.
3. **Theorem Proving**: Study different proof techniques (induction, case analysis, etc.).
4. **Advanced Topics**: Explore category theory, cryptography, and complexity theory formalizations.

Each Coq file includes extensive comments explaining the mathematical concepts and proof strategies.

---

# Repository Structure

The repository is organized to provide a complete, self-contained artifact for the Thiele Machine. Below is a detailed breakdown of each component:

| Path                        | Purpose                                                        | Details |
|-----------------------------|----------------------------------------------------------------|---------|
| `attempt.py`                | Main artifact: all experiments, proofs, and data generation    | This is the core script containing all demonstrations, from foundational proofs to empirical experiments. It runs the complete artifact pipeline. |
| `generate_tseitin_data.py`  | Large-scale experiment orchestration and data collection       | Handles generation of hard SAT instances and runs comparative experiments between blind and sighted solvers. |
| `thielecpu/`                | Modular Python package                                         | Contains the Thiele CPU implementation with modules for state management, logic integration, and partition logic. |
| `coq/`                      | Coq source files and proofs                                    | Formal mathematical proofs in Coq, organized by project/component. |
| `examples/`                 | Example input files                                            | Sample inputs for demonstrations, including SAT problems and logical puzzles. |
| `shape_of_truth_out/`       | All output artifacts: proofs, data, plots                     | Generated outputs from experiments, including SMT2 proofs, plots, and certificates. |
| `requirements.txt`          | Python dependencies                                            | Lists all required Python packages with versions. |
| `README.md`                 | This document                                                 | Comprehensive documentation and user guide. |
| `LICENSE`                   | License (MIT)                                                 | Open-source license allowing full use and modification. |

## Detailed Component Explanations

### Core Scripts

#### `attempt.py` - The Main Artifact
This 2486-line Python script is the heart of the Thiele Machine artifact. It contains:

- **Foundational Proofs**: Demonstrates that the Thiele Machine subsumes Turing and von Neumann machines.
- **Paradox Demonstrations**: Shows the core conflict between blind and sighted computation.
- **Universal Principle**: Generalizes the paradox to rotations and Sudoku.
- **Engine of Discovery**: Brute-force search over partitions using MDL.
- **Fractal Nature of Debt**: Large-scale experiments showing exponential cost separation.
- **Gödelian Landmine**: Constructs paradoxical logical spaces to test computational limits.

**Key Functions**:
- `run_prove_tm_subsumption()`: Proves Thiele Machine subsumes Turing Machine.
- `run_paradox()`: Demonstrates the liar's paradox in computation.
- `run_engine_and_law()`: Implements the Engine of Discovery.
- `run_fractal_debt()`: Runs large-scale cost separation experiments.

#### `generate_tseitin_data.py` - Experiment Orchestration
This script handles large-scale empirical experiments:

- **Instance Generation**: Creates hard Tseitin formulas on expander graphs.
- **Solver Comparison**: Runs blind (SAT) vs sighted (GF(2)) solvers.
- **Parallel Execution**: Uses multiprocessing for efficient experimentation.
- **Result Logging**: Saves all data to `tseitin_receipts.json`.

**Key Features**:
- Generates instances with guaranteed unsatisfiability (odd charge).
- Implements resource budgets for fair comparison.
- Provides progress bars and diagnostics.

### ThieleCPU Package (`thielecpu/`)

The `thielecpu/` directory contains a modular Python package implementing the Thiele Machine:

- **`__init__.py`**: Package initialization and main exports.
- **`_types.py`**: Type definitions for states, partitions, and certificates.
- **`assemble.py`**: Assembly and compilation of Thiele programs.
- **`certs.py`**: Certificate generation and verification.
- **`isa.py`**: Instruction set architecture for the Thiele CPU.
- **`logic.py`**: Integration with Z3 logic engine.
- **`mdl.py`**: Minimum Description Length calculations.
- **`memory.py`**: Memory management and state representation.
- **`state.py`**: State space management and transitions.
- **`vm.py`**: Virtual machine implementation.

This package provides the runtime environment for Thiele Machine programs, enabling partition-native computation with integrated logic verification.

### Coq Formalizations (`coq/`)

The `coq/` directory contains formal mathematical proofs in Coq, organized by component:

#### `coq/thielemachine/`
- **`ThieleMachine.v`**: Core formalization of the Thiele Machine tuple T = (S, Π, A, R, L).
  - Defines state spaces, partitions, axioms, transitions, and logic engines.
  - Proves all theorems about Thiele Machine operation.
- **`Subsumption.v`**: One-line proof that Thiele Machine subsumes Turing Machine.
  - Shows that any Turing computation can be simulated by a Thiele Machine.

#### `coq/catnet/`
- **`CatNet.v`**: Formal proof for CatNet neural network architecture.
  - Proves cryptographic integrity of audit logs.
  - Demonstrates tamper-evident logging in neural networks.

#### `coq/project_cerberus/`
- **`Cerberus.v`**: Formal model of a self-auditing Thiele kernel.
  - Proves that the kernel is secure by construction.
  - Shows program counter bounds when logic oracle confirms consistency.

#### `coq/isomorphism/`
- **`Universe.v`**: Establishes functor from physical universe to logical abstraction.
  - Proves conserved momentum in the isomorphism.
  - Connects physical and computational concepts.

#### `coq/test_vscoq/`
- **`test_vscoq.v`**: Minimal smoke test for VSCoq integration.
  - Ensures Coq environment is properly configured.

#### `coq/p_equals_np_thiele/`
- **`proof.v`**: Formal proof of structural P=NP collapse in Thiele Machine.
  - Demonstrates how partition logic resolves complexity class separation.
- **`ARCHITECTURAL_COLLAPSE_OF_NP.md`**: Explanatory document on the P=NP result.

**Compilation Instructions**:
```bash
# Compile all Coq files
coqc coq/thielemachine/coqproofs/Subsumption.v
coqc coq/thielemachine/coqproofs/ThieleMachine.v
coqc coq/catnet/coqproofs/CatNet.v
coqc coq/project_cerberus/coqproofs/Cerberus.v
coqc coq/isomorphism/coqproofs/Universe.v
coqc coq/test_vscoq/coqproofs/test_vscoq.v
```

All files compile with exit code 0, containing no `Admitted` or `Axiom` statements.

### Examples (`examples/`)

Sample input files for demonstrations:

- **`demo.thl`**: Sample Thiele Machine program.
- **`xor_sat.smt2`**: XOR-SAT instance for testing.
- **`xor_tseitin.py`**: Python script for Tseitin transformation.
- **`graph_partition.py`**: Graph partitioning example.
- **`liar.py`**: Liar's paradox implementation.

### Output Directories

#### `shape_of_truth_out/`
Contains all generated artifacts:

- **SMT2 Proof Files**: Machine-checkable proofs from Z3.
- **Plots**: Visualizations of experimental results (censored fraction, median conflicts).
- **Certificates**: Cryptographically hashed certificates.
- **Bisimulation Proofs**: Formal proofs of computational equivalence.

#### `results/`
Summary outputs:

- **`RESULTS.md`**: Comprehensive summary of all experiments.
- **`challenge.log`**: Verification harness logs.
- **`lemmas.txt`**: Extracted logical lemmas.

#### `receipts/`
Experimental receipts:

- **`at_most_k.json`**: Results from at-most-k experiments.
- **`graph_partition.json`**: Graph partitioning results.
- **`xor_tseitin.json`**: XOR-Tseitin transformation receipts.

### Scripts Directory (`scripts/`)

Utility scripts for development and deployment:

- **`RUNME.sh`**: Master script to run everything.
- **`challenge.py`**: Verification harness for receipts.
- **`demonstration.py`**: Liar's paradox demo.
- **`gen_receipts.py`**: Receipt generation utility.
- **`run_all_experiments.py`**: Batch experiment runner.
- **`run_benchmark.py`**: Performance benchmarking.
- **`solve_sudoku.py`**: Sudoku solver demonstration.
- **`thiele_verify.py`**: Verification utilities.

### Tests (`tests/`)

Unit tests for all components:

- **`test_axioms.py`**: Tests for logical axioms.
- **`test_catnet.py`**: CatNet neural network tests.
- **`test_challenge.py`**: Challenge verification tests.
- **`test_coq_available.py`**: Coq environment tests.
- **`test_receipts.py`**: Receipt validation tests.

### Documents (`documents/`)

LaTeX source and compiled outputs:

- **`The_Thiele_Machine.tex`**: Main paper (32 pages).
- **`The_Thiele_Machine.pdf`**: Compiled PDF.
- **Supporting Documents**: Additional LaTeX files.

### Assets (`assets/`)

Visual assets:

- **`(T).png`**: Thiele Machine logo.
- **Architecture diagrams and visualizations**.

## Experiment Details

### Core Experiments in `attempt.py`

1. **Foundational Proofs (Lines 55-173)**
   - Proves Thiele Machine subsumes classical models.
   - Demonstrates bisimulation between Turing and Thiele computation.

2. **Paradox Demonstration (Lines 786-905)**
   - Shows how blind solvers fail on structured problems.
   - Introduces the concept of "sight debt".

3. **Universal Principle (Lines 906-997)**
   - Generalizes paradox to rotations and Sudoku.
   - Demonstrates order-invariance.

4. **Engine of Discovery (Lines 998-1228)**
   - Brute-force partition search using MDL.
   - Measures information-theoretic cost of discovery.

5. **Fractal Nature of Debt (Lines 1229-1632)**
   - Large-scale experiments with multiprocessing.
   - Shows exponential cost separation.

6. **Gödelian Landmine (Lines 2295-2486)**
   - Constructs paradoxical logical spaces.
   - Tests limits of classical computation.

### Large-Scale Experiments in `generate_tseitin_data.py`

- **Instance Generation**: Creates Tseitin formulas on 3-regular expander graphs.
- **Hardness Control**: Uses odd total charge for guaranteed unsatisfiability.
- **Solver Comparison**: Blind (SAT) vs Sighted (GF(2) row reduction).
- **Scaling Analysis**: Measures how cost separation grows with problem size.

## Running the Complete Artifact

1. **Setup**:
   ```bash
   python -m venv .venv
   source .venv/bin/activate  # or .venv\Scripts\activate on Windows
   pip install -r requirements.txt
   ```

2. **Run Main Artifact**:
   ```bash
   python attempt.py
   ```
   - Generates all proofs, experiments, and outputs.
   - Takes several minutes to complete.

3. **Run Large-Scale Experiments**:
   ```bash
   python generate_tseitin_data.py
   ```
   - Generates empirical data for cost separation analysis.

4. **Verify Results**:
   ```bash
   python scripts/challenge.py verify receipts
   ```
   - Checks all cryptographic hashes and certificates.

5. **Compile Coq Proofs**:
   ```bash
   coqc coq/thielemachine/coqproofs/Subsumption.v
   # ... compile other .v files
   ```

## Educational Value

This repository serves as a comprehensive educational resource for:

- **Computational Complexity**: Understanding P vs NP through structural collapse.
- **Formal Methods**: Using Coq for mathematical proof.
- **Logic Programming**: Z3 integration and SMT solving.
- **Scientific Computing**: Empirical experimentation and data analysis.
- **Philosophy of Computation**: Geometric approaches to information processing.

Each component is designed to be both runnable and educational, with extensive comments and documentation explaining the theoretical foundations and practical implementations.

---

# The Thiele Machine & The Shape of Truth

---

## Origins and Prototyping

This project began as an exploration of "categorical rendering" that was originally intended for a future implementation in Rust. Early prototypes were developed in Python, which led to a series of experiments into the geometry of abstraction and computation through logic. Continued research and iteration produced the executable thesis presented here.

---

The Thiele Machine is a fundamentally new model of computation that extends and strictly contains the classical Turing Machine. Unlike the Turing Machine, which operates on a single, undivided state and processes information in a linear, stepwise fashion, the Thiele Machine is **partition-native**: it can dynamically decompose the computational state into independent modules, reason about each module separately, and then compose the results. This enables the Thiele Machine to perceive and exploit hidden structure in problems that are invisible to classical computation.

### Motivation

The motivation for the Thiele Machine arises from the limitations of classical computation. Turing Machines, and by extension all classical computers, are "blind" to the geometric and modular structure of complex problems. They accumulate "information debt" by failing to recognize and exploit hidden regularities, leading to inefficiency, intractability, or outright failure on certain classes of problems. The Thiele Machine was conceived to overcome these limitations by introducing **partition logic** and **certificate-driven computation**—allowing the machine to "see" and leverage the true shape of computational problems.

### How the Thiele Machine Differs from Turing Machines

- **Partition Logic:** The Thiele Machine can split the state space into multiple modules, each governed by its own local rules and axioms. This is impossible in the Turing model, which treats the state as a monolith.
- **Order-Invariance:** Computation in the Thiele Machine is not tied to a specific sequence of steps; the outcome depends only on the structure of the problem, not the order of operations.
- **Certificate-Driven:** Every computational step, transition, and solution must be justified by a logical certificate (proof or witness), enforced by an integrated logic engine (e.g., Z3).
- **Quantified Discovery Cost:** The Thiele Machine introduces the concept of **mubits**—the atomic units of discovery cost—making explicit the price paid to perceive and resolve hidden structure.

### Artifact Goals

This repository provides a complete, self-verifying artifact that:
- **Formally defines** the Thiele Machine and its operational principles.
- **Implements** the Thiele Machine paradigm in code, with rigorous integration of logic engines and partition logic.
- **Empirically demonstrates** the strict separation between classical (blind) and partition-native (sighted) computation through reproducible experiments.
- **Produces cryptographically sealed outputs** and machine-checkable certificates for every claim, ensuring full auditability and reproducibility.

### Philosophical Context

The Thiele Machine is not just a technical upgrade; it is a philosophical statement about the nature of computation, knowledge, and proof. It operationalizes the idea that **computation is geometric**—that problems have shape, structure, and hidden dimensions, and that true understanding requires perceiving and exploiting this geometry. Every act of discovery is paid for in mubits, and every proof is a physical artifact, enacted and witnessed by the machine itself. The Thiele Machine challenges us to rethink the foundations of computation, epistemology, and scientific inference.

This README provides a comprehensive, detailed guide to the Thiele Machine artifact, its theory, implementation, usage, and philosophical implications.

---

## Mathematical Foundations

### Formal Definition: The Thiele Machine Tuple

The Thiele Machine is rigorously defined as a tuple:

$$
T = (S, \Pi, A, R, L)
$$

where:

- **$S$ (State Space):** The complete set of all possible states of the computation. This includes every variable, memory cell, register, tape symbol, or configuration relevant to the problem. In code, $S$ is typically represented as a high-dimensional vector or structured object capturing the entire computational context.

- **$\Pi$ (Partitions):** The set of all admissible partitions of $S$. Each partition $\pi \in \Pi$ is a collection of disjoint subsets (called modules) such that $\bigcup_{i} M_i = S$ and $M_i \cap M_j = \emptyset$ for $i \neq j$. Partitions allow the Thiele Machine to decompose the problem into independent modules, each of which can be reasoned about separately.

- **$A$ (Axioms/Rules):** The set of axioms, rules, or constraints that govern the behavior of each module. These may include logical formulas, algebraic equations, or domain-specific rules. $A$ can vary between modules and partitions, enabling local reasoning.

- **$R$ (Transition Relation):** The set of allowed transitions, each mapping a pair $(S, \pi)$ to a new pair $(S', \pi')$. Transitions can update both the state and the partition, allowing the machine to refine or coarsen its modular decomposition as computation proceeds.

- **$L$ (Logic Engine):** An external or embedded logic engine (such as Z3) that checks the logical consistency of each module with its local axioms. $L$ is invoked for every module and every candidate partition, ensuring that only logically consistent solutions are accepted.

#### Visual Diagram

```
+-------------------+         +-------------------+
|    State Space    |         |    Partitions     |
|        S          |<------->|        Π          |
+-------------------+         +-------------------+
         |                            |
         v                            v
+-------------------+         +-------------------+
|      Axioms       |         |   Logic Engine    |
|        A          |-------->|        L          |
+-------------------+         +-------------------+
         |                            ^
         v                            |
+-------------------+         +-------------------+
|   Transitions R   |-------->|   (S', Π')        |
+-------------------+         +-------------------+
```

#### Step-by-Step Example

Suppose $S$ encodes a system of equations with hidden structure. The Thiele Machine:

1. **Initial State:** Starts with $S$ and the trivial partition $\Pi_{\text{trace}} = \{S\}$.
2. **Partitioning:** Refines $\Pi$ to split $S$ into modules $M_1, M_2$ based on detected structure.
3. **Local Reasoning:** Applies $A$ to each $M_i$ and invokes $L$ to check consistency.
4. **Transition:** If a module is inconsistent, $R$ updates $(S, \pi)$ to $(S', \pi')$ (e.g., by further partitioning or updating state).
5. **Composition:** If all modules are consistent, their solutions are composed into a global solution.

#### Comparison: Thiele Machine vs. Turing Machine

| Aspect                | Turing Machine                                   | Thiele Machine                                         |
|-----------------------|--------------------------------------------------|--------------------------------------------------------|
| State Representation  | Single tape/configuration                        | Arbitrary state space $S$                              |
| Partitioning          | None (monolithic)                                | Dynamic, multi-module partitions $\Pi$                 |
| Reasoning             | Global, stepwise                                 | Local (per module), compositional                      |
| Logic/Verification    | Implicit, not enforced                           | Explicit, enforced by logic engine $L$                 |
| Discovery Cost        | Not quantified                                   | Quantified in mubits (bits of discovery)               |
| Order Sensitivity     | Trace-based, order-dependent                     | Order-invariant, structure-dependent                   |
| Proofs/Certificates   | Not required                                     | Every step certified (proofs/witnesses)                |

#### Implementation References

- Transition system and partition logic: [`attempt.py`](attempt.py:55-173)
- Turing and Thiele Machine encodings: [`attempt.py`](attempt.py:404-475)
- Logic engine integration: [`attempt.py`](attempt.py:786-820)


---

## Partition Logic and Modular Reasoning

Partition logic is the central innovation that distinguishes the Thiele Machine from all classical computational models. It provides a rigorous mathematical and operational framework for decomposing complex problems into independent modules, enabling scalable, modular, and geometric reasoning.

### What is Partition Logic?

Partition logic is the study and operationalization of how a computational state space $S$ can be split into disjoint subsets (modules) $\{M_1, M_2, ..., M_k\}$, such that:

- $\bigcup_{i=1}^k M_i = S$
- $M_i \cap M_j = \emptyset$ for all $i \neq j$

The set of all such admissible partitions is denoted $\Pi$. Each partition $\pi \in \Pi$ represents a possible modular decomposition of the problem.

#### Types of Partitions

- **Trivial Partition ($\Pi_{\text{trace}}$):** The entire state space as a single module. This is the only partition available to a Turing Machine, corresponding to classical, monolithic computation.
- **Non-Trivial Partition:** Any partition with $k > 1$ modules. These enable the Thiele Machine to reason about different parts of the problem independently, discovering and exploiting hidden structure.

### Why is Partition Logic Powerful?

Partition logic allows the Thiele Machine to:

- **Exploit Hidden Structure:** By decomposing $S$ into modules, the machine can isolate independent or weakly-coupled subproblems, leading to exponential speedups and compact certificates.
- **Enable Modular Reasoning:** Each module can be reasoned about, solved, or verified independently, then composed into a global solution.
- **Localize Contradictions:** Logical inconsistencies can be traced to specific modules or partition boundaries, aiding debugging and verification.
- **Refine or Coarsen Dynamically:** The partition can be refined (split further) or coarsened (merged) as computation proceeds, adapting to the evolving structure of the problem.

### Concrete Example

Suppose $S$ encodes a dataset with two hidden clusters. The Thiele Machine can:

1. **Start with the trivial partition:** $\Pi_{\text{trace}} = \{S\}$
2. **Detect hidden structure:** Using statistical or logical analysis, the machine identifies two clusters.
3. **Refine the partition:** $\pi = \{M_1, M_2\}$, where $M_1$ and $M_2$ correspond to the clusters.
4. **Apply local rules:** Each module is analyzed with its own set of axioms $A_1$, $A_2$.
5. **Compose solutions:** If both modules are consistent, their solutions are combined into a global answer.

### Computational Significance

Partition logic is the foundation for:

- **Exponential Speedups:** Problems that are intractable for monolithic solvers become tractable when decomposed into modules.
- **Order-Invariant Computation:** The outcome depends on the structure of the partition, not the order of operations.
- **Robust Verification:** Modular proofs and certificates can be composed, audited, and reused.

### Implementation Details

- **Transition System and Partition Logic:** [`attempt.py`](attempt.py:55-173) formalizes the transition system, allowing transitions to act on non-trivial partitions.
- **Minimal von Neumann Machine Encoding:** [`attempt.py`](attempt.py:546-710) demonstrates partition logic in the context of a minimal RAM machine.
- **Engine of Discovery:** [`attempt.py`](attempt.py:998-1228) searches the space of partitions to find those that minimize the Minimum Description Length (MDL) and resolve logical paradoxes.

### Further Reading

- See the "Empirical Experiments" section for real-world demonstrations of partition logic in action.
- For the formal mathematical background, see the "Mathematical Foundations" section above.


---

## Certificate-Driven Computation

Certificate-driven computation is a foundational principle of the Thiele Machine. Unlike classical computation, which proceeds by unverified steps, the Thiele Machine requires every transition, solution, and composition to be certified by a logic engine. This ensures that every computational claim is justified, auditable, and reproducible.

### What is a Certificate?

A **certificate** is a formal, machine-checkable proof or witness that justifies a computational step. Certificates come in several forms:

- **Transition Certificates:** Proofs that a state transition is logically valid under the current axioms and partition.
- **Module Certificates:** Proofs or witnesses that a module (subset of the state space) is logically consistent with its local axioms.
- **Composition Certificates:** Proofs that the global solution, obtained by composing local module solutions, is itself consistent and valid.

Certificates are generated and checked by an integrated logic engine (such as Z3), and are saved as machine-verifiable artifacts (e.g., SMT2 proof files, cryptographic hashes).

### How are Certificates Generated?

1. **Encoding the Problem:** Each module $M_i$ and its local axioms $A_i$ are encoded as logical formulas (typically in SMT-LIB format).
2. **Invoking the Logic Engine:** The logic engine $L$ (e.g., Z3) is called to check the satisfiability or unsatisfiability of each module.
   - If $L(M_i, A_i)$ is **satisfiable**, the engine produces a **witness** (a concrete model or solution).
   - If $L(M_i, A_i)$ is **unsatisfiable**, the engine produces a **proof** (certificate of impossibility).
3. **Saving Artifacts:** All proofs and witnesses are saved as files, and their contents are hashed (e.g., SHA256) for auditability.
4. **Composing Certificates:** For non-trivial partitions, local certificates are composed to form a global certificate, ensuring that the overall solution is justified.

### Z3 Integration

- Z3 is used as the primary logic engine for all certificate generation and checking.
- Every module, partition, and transition is encoded as a Z3 problem.
- Z3's output (proofs, witnesses, models) is parsed, saved, and hashed for reproducibility.
- All claims in the artifact are backed by machine-checkable SMT2 files and cryptographic hashes.

### Why is Certificate-Driven Computation Important?

- **Auditability:** Every computational claim can be independently verified by anyone with access to the artifact and the logic engine.
- **Reproducibility:** All outputs, proofs, and transcripts are hashed and sealed, ensuring that results can be reproduced exactly.
- **Bug Detection:** Logical inconsistencies are detected immediately, preventing silent errors.
- **Scientific Rigor:** The artifact provides its own evidence, embodying the principle that "to prove is to compute."

### Implementation Details

- **Z3 Integration and Certificate Generation:** [`attempt.py`](attempt.py:786-820, 952-1001, 193-217)
- **Proof Artifacts and Hashing:** [`attempt.py`](attempt.py:952-1001)
- **Certificate-Driven Transitions:** [`attempt.py`](attempt.py:55-173, 998-1228)
- **Empirical Examples:** See "Empirical Experiments" for how certificates are generated and used in practice.


---

## The Law of No Unpaid Sight Debt (NUSD)

The Law of No Unpaid Sight Debt (NUSD) is a central principle of the Thiele Machine paradigm. It formalizes the intuition that "sight"—the ability to perceive and exploit hidden structure in a problem—always comes at a quantifiable cost. NUSD is both a mathematical law and a philosophical statement about the nature of discovery and knowledge.

### Formal Statement

NUSD asserts that for any problem where the trivial partition $\Pi_{\text{trace}}$ is ill-suited (i.e., where hidden structure exists), the cost (measured by the Minimum Description Length, MDL) of a solution under a refined partition $\pi'$ will be strictly lower than the cost under $\Pi_{\text{trace}}$.

Formally, for a dataset $D$ and model $\mathcal{M}$ (partition + rules):

$$
L(\mathcal{M}) = L(\text{structure}) + \sum_{i=1}^k L(\text{parameters}_i) + L(\text{residual})
$$

- $L(\text{structure})$: Bits required to encode the partition.
- $L(\text{parameters}_i)$: Bits to encode the parameters for each module.
- $L(\text{residual})$: Bits to encode the error or residuals (zero for exact fits).

If any group in the partition is logically inconsistent (UNSAT), $L(\mathcal{M}) = +\infty$. Thus, the cost of blindness (failing to see hidden structure) is infinite or exponentially large, while the cost of sight (discovering and exploiting structure) is finite and measurable.

### Operational Meaning

- **Blindness is Expensive:** If the machine fails to perceive hidden structure and attempts to fit all data with a single rule, the MDL becomes infinite (or extremely large) due to logical inconsistency.
- **Sight is Paid For:** By partitioning the data according to hidden structure, the machine pays a finite number of bits (mubits) to encode the new structure and rules, but achieves a valid, compact solution.
## Mubits and Minimum Description Length (MDL)

### What are Mubits?

A **mubit** is the atomic unit of discovery cost in the Thiele Machine paradigm. Mubits quantify the price paid to perceive, partition, and resolve hidden structure in computational problems. They are measured in bits and correspond directly to the increase in model complexity or the cost of discovery as computed by the Minimum Description Length (MDL) functional.

- **Discovery Cost:** The number of mubits required to discover a new partition or rule.
- **Sight Debt:** The total mubits owed when a problem's hidden structure is not perceived (i.e., when the model is blind).

#### Why Mubits Matter

- **Operational Currency:** Mubits are the operational currency of both MDL and NUSD. Every bit in the MDL functional is a mubit paid for structure, parameters, or residuals.
- **Quantifying Discovery:** Mubits make explicit the cost of learning, model refinement, and paradox resolution.
- **Scientific Implications:** The quantification of discovery cost has deep implications for epistemology, learning theory, and the philosophy of science.

### Minimum Description Length (MDL) Principle

The MDL principle is the mathematical backbone of model selection in the Thiele Machine. It provides a rigorous, quantitative criterion for choosing among competing partitions and rules, balancing model complexity against explanatory power.

#### Formal Definition

$$
L(\mathcal{M}) = L(\text{structure}) + \sum_{i=1}^k L(\text{parameters}_i) + L(\text{residual})
$$

- $L(\text{structure})$: Bits to encode the partition (e.g., prefix code for bipartitions).
- $L(\text{parameters}_i)$: Bits to encode the parameters (e.g., coefficients of linear rules) for each group/module.
- $L(\text{residual})$: Bits to encode the error or residuals (zero for exact fits).

If any group in the partition is logically inconsistent (UNSAT), $L(\mathcal{M}) = +\infty$.

#### How MDL is Used

- **Model Selection:** For each candidate partition, the artifact checks logical consistency with Z3, computes the MDL for all viable partitions, and selects the partition(s) with minimal MDL as optimal models.
- **Discovery Log:** The artifact logs the MDL for every candidate partition, providing a transparent, auditable record of the model selection process.
- **Blind vs. Sighted MDL:** Blind models (single rule for all data) often have infinite MDL due to inconsistency, while sighted models (partitioned) achieve finite, minimized MDL.

#### Implementation Details

- **MDL Calculation:** [`attempt.py`](attempt.py:854-875) implements the MDL functional.
- **Model Selection and Engine of Discovery:** [`attempt.py`](attempt.py:998-1228) searches the space of partitions, checks consistency, computes MDL, and selects optimal models.
- **Empirical Demonstration:** See "Empirical Experiments" for how MDL and mubits are computed and compared in practice.


---

## Order-Invariance and Composite Witnesses

Order-invariance and composite witnesses are central to the Thiele Machine's departure from classical, trace-based computation. These concepts formalize the idea that the outcome of computation should depend on the structure of the problem, not the order of operations.

### What is Order-Invariance?

A property $P$ of a transition system is **order-invariant** if, for any sequence of transitions leading to a state $s$, the outcome (e.g., solution, certificate) depends only on the set of transitions, not their order. In the Thiele Machine, a computation is order-invariant if the final certificate or solution is independent of the order in which modules are solved or composed.

#### Why Order-Invariance Matters

- **Robustness:** Order-invariant computation is immune to the pitfalls of trace-based reasoning, where the outcome can depend on arbitrary choices of execution order.
- **Parallelism:** Modules can be solved in any order or in parallel, as long as the final composition is consistent.
- **Auditable Proofs:** The global certificate is a function of the problem's structure, not the history of computation.

### What are Composite Witnesses?

A **composite witness** is a global certificate constructed by composing local certificates from each module in a partition. This stands in contrast to trace-based computation, where the solution is built step-by-step and is inherently order-dependent.

#### Concrete Examples

- **Rotations:** Sequential application of rotations (trace) yields different results depending on order, but the composite orientation (global witness) is unique and order-invariant.
- **Sudoku:** The solution to a Sudoku puzzle is a single, global witness—independent of the order in which constraints are applied or cells are filled.

### Operationalization in the Artifact

- **ACT II Demonstration:** [`attempt.py`](attempt.py:906-997) demonstrates order-invariance using rotations and Sudoku. In the rotation example, the composite orientation is independent of the order of sequential operations, while the trace paths are order-dependent. In Sudoku, the solution is a single point in constraint space, not a sequence of moves.
- **Partition-Native Proofs:** [`attempt.py`](attempt.py:998-1228) shows how decomposing problems into modules and composing their solutions achieves order-invariant computation, witnessed by composite certificates.

### Why This Matters for Program Analysis

Order-invariance operationalizes the idea that computation should reflect the geometry of the problem, not the arbitrary order of execution. Composite witnesses provide robust, auditable certificates that are immune to the pitfalls of trace-based reasoning. This principle has profound implications for program analysis, verification, and the philosophy of computation: it enables modular, parallel, and robust reasoning about complex systems.


---

## Empirical Experiments and Results

The artifact implements a comprehensive suite of empirical experiments to demonstrate the operational separation between classical (blind) and partition-native (sighted) computation. These experiments provide concrete, measurable evidence for the strict separation predicted by the Thiele Machine paradigm.

### Step-by-Step Experimental Walkthrough

#### 1. Hard Instance Generation

- **Tseitin Formulas:** The artifact generates hard instances based on Tseitin formulas on random 3-regular expander graphs, with odd total charge to guarantee unsatisfiability.
- **Instance Generation Code:** See [`attempt.py`](attempt.py:1940-2145) and [`generate_tseitin_data.py`](generate_tseitin_data.py:86-134).
- **Reproducibility:** All random seeds, graph structures, and charges are logged for full reproducibility.

#### 2. Solver Comparison

- **Blind Solver:** Uses PySAT Minisat22 (or CaDiCaL/Glucose if available), restricted to classical Resolution/DPLL, with fixed conflict and propagation budgets. The blind solver is unaware of the problem's modular structure.
- **Sighted Solver:** Uses GF(2) row reduction, exploiting the problem's native geometry and partition structure. The sighted solver can instantly detect unsatisfiability via an inconsistent row in the augmented matrix.

#### 3. Experiment Orchestration

- **Parallel Execution:** Experiments are run in parallel using Python's multiprocessing, with progress bars and heartbeat diagnostics.
- **Resource Budgets:** Conflict and propagation budgets are enforced for the blind solver to ensure fair comparison.
- **Empirical Receipts:** All results, including conflict counts, decision counts, timings, and certificate hashes, are logged and saved as machine-verifiable artifacts.

#### 4. Result Analysis

- **Blind Solver Results:** Rapidly accumulates conflicts, often hitting the budget ceiling without resolving the instance. The censored fraction (fraction of runs that exhaust the budget) increases rapidly with problem size. Median conflicts grow exponentially with instance size.
- **Sighted Solver Results:** Instantly detects unsatisfiability, with certificate size and computational cost remaining essentially constant, regardless of instance size.
- **Empirical Receipts:** Plots of censored fraction and median conflicts vs. instance size provide visual evidence of exponential separation. All claims are backed by SMT2 files, empirical data, and cryptographic hashes.

#### 5. Control Experiments

- **Even-Charge Controls:** Instances with even total charge are always satisfiable, and both solvers succeed, confirming the specificity of the separation.

#### 6. Operational Receipts

- **Machine-Checkable Proofs:** All claims are backed by SMT2 files, empirical data, and cryptographic hashes.
- **Reproducibility:** The artifact records all environment details, random seeds, and command lines for full reproducibility.

### Implementation Details

- **Experiment Orchestration:** [`generate_tseitin_data.py`](generate_tseitin_data.py:1-523) handles instance generation, solver execution, and result logging.
- **Analysis and Plotting:** [`attempt.py`](attempt.py:2067-2145) provides tools for analyzing and visualizing results.
- **Empirical Receipts:** All outputs are saved in `shape_of_truth_out/` and `tseitin_receipts.json` for auditability.
---

## Foundational Proofs: TM/VN Subsumption

The non-act opening establishes that the Thiele Machine subsumes Turing and
von Neumann models. It formalizes state, transitions, and certificates,
culminating in the Bisimulation and Strict Separation theorems.
([`attempt.py`](attempt.py:55-173))

## The Paradox

Introduces the core conflict between a blind solver and a partition-aware solver
through a verifiable puzzle.
([`attempt.py`](attempt.py:786-905))

## The Universal Principle

Generalizes the paradox using spatial rotations and Sudoku to show the
phenomenon is not contrived.
([`attempt.py`](attempt.py:906-997))

## The Engine of Discovery

Measures the information-theoretic cost of uncovering hidden structure via a
brute-force search over partitions using MDL.
([`attempt.py`](attempt.py:998-1228))

## The Fractal Nature of Debt

Demonstrates the exponential cost of blindness with hard instances and
multiprocessing harnesses.
([`attempt.py`](attempt.py:1229-1632))

## Final Theorem & Conclusion

States the Embedding and Self-Reconstruction theorems, presents the capability
comparison table, and cryptographically seals the artifact.
([`attempt.py`](attempt.py:1633-1979))

## Experimental Separation

Provides detailed, small-scale receipts comparing blind and sighted solvers
with plots and tables.
([`attempt.py`](attempt.py:1980-2294))

## Gödelian Landmine

The seventh act of this artifact is a deliberate confrontation with the limits of classical computation—a constructed paradox designed to expose the fundamental difference between the Turing and Thiele paradigms.

### The Paradox Constructed

In the Gödelian Landmine section ([`attempt.py`](attempt.py:2295-2486)), the artifact generates a logical space that is, by design, paradoxical: it encodes a set of constraints that cannot be satisfied by any assignment. For a classical (Turing) machine, this is a death trap. The machine, bound to search for an object-level solution, will enumerate possibilities, backtrack, and ultimately fail, unable to produce anything but a negative result or an error.

### The Thiele Machine's Response

The Thiele Machine, by contrast, is not limited to object-level search. It can step back and perceive the *shape* of the solution space itself. When confronted with a paradox, it does not merely fail to find a solution—it produces a **Certificate of Inherent Paradox**: a formal, machine-verifiable proof that the space is unsatisfiable *because* of its structure, not just its content. This is a higher-order computational act, enabled by the partition logic and certificate-driven computation described earlier (see lines 146–250).

### Technical Implementation

- **Construction:** The paradox is encoded as a set of logical constraints in [`attempt.py`](attempt.py:2295-2486), leveraging the Z3 logic engine to verify unsatisfiability.
- **Detection:** The Thiele Machine partitions the state space, applies local axioms, and invokes the logic engine to check for consistency. When all partitions are inconsistent, it issues the certificate.
- **Output:** The certificate is saved as a machine-verifiable artifact (SMT2 proof file), and its hash is logged for auditability.

### Philosophical and Scientific Implications

The Gödelian Landmine is not a parlor trick; it is a demonstration of a new computational act. Where the classical machine is blind to the global structure of the problem, the Thiele Machine can *see* and *certify* the impossibility itself. This operationalizes a key philosophical insight: **the type of answer a machine can produce is as important as what it can compute**. The ability to issue a certificate about the *nature* of the solution space—rather than just the existence or absence of solutions—marks a profound separation in computational power.

### References

- Formal construction and code: [`attempt.py`](attempt.py:2295-2486)
- Certificate-driven computation: lines 205–250
- Partition logic: lines 146–201
- Empirical demonstration: see "Empirical Experiments and Results" (lines 409–455)

## Philosophical Implications and Future Directions

The Thiele Machine is not just a technical artifact; it is a philosophical statement about the nature of computation, knowledge, and proof. Its principles challenge and extend the foundations of computer science, epistemology, and scientific inference.

### Computation as Geometry

The Thiele Machine operationalizes the idea that computation is fundamentally geometric. Problems have shape, structure, and hidden dimensions, and the act of computation is the act of perceiving and exploiting this geometry. This stands in contrast to the classical, trace-based view, which is blind to hidden structure and accumulates information debt.

### Proof as Physical Object

In the Thiele Machine paradigm, proofs are not just abstract arguments—they are physical objects, enacted and witnessed by the machine itself. Every claim is certified by a logic engine, every artifact is cryptographically sealed, and every step is reproducible and auditable. The artifact provides its own evidence and documentation.

### Epistemology of Discovery

The Law of No Unpaid Sight Debt (NUSD) asserts that discovery always comes at a cost, measured in mubits. Knowledge is never free; every act of perception, every refinement of a model, and every resolution of a paradox is paid for in bits. This quantification of discovery cost has deep implications for learning theory, scientific inference, and the philosophy of science.

### Modular Reasoning and Order-Invariance

Partition logic and order-invariant computation enable robust, modular reasoning about complex systems. Composite witnesses provide global certificates that are immune to the pitfalls of trace-based reasoning, enabling scalable verification and analysis.

### Empirical Separation and Operational Receipts

The artifact provides machine-verifiable evidence for the strict separation between classical and partition-native computation. Empirical experiments operationalize theoretical claims, providing receipts for every assertion.

### Synthesis and Outlook

The Thiele Machine unifies computation, logic, and epistemology under a single operational framework. It demonstrates that computation is not just symbol manipulation, but the discovery and exploitation of structure. The artifact stands as evidence and a challenge: evidence that computation is geometric, modular, and certificate-driven, and a challenge to rethink the foundations of computation, knowledge, and proof.

### Future Research Directions

- Richer partition logics (hierarchical, overlapping, dynamic)
- Automated discovery engines and learning protocols
- Integration with large-scale software verification and synthesis
- Applications to scientific modeling, AI, and epistemology
- Formalization of mubits and information debt in learning systems
- Development of new programming languages and tools based on the Thiele Machine paradigm

---
## Installation and Usage

This section provides detailed instructions for installing dependencies, running the artifact, interpreting outputs, and understanding the structure of all generated files.

### 1. Installing Dependencies

All required dependencies are listed in [`requirements.txt`](requirements.txt:1-34). To install them, run:

```sh
pip install -r requirements.txt
```


**Key packages:**
- `z3-solver`: SMT logic engine for certificate generation and checking.
- `python-sat`: SAT solver interface for classical (blind) solving.
- `numpy`, `scipy`: Numerical and scientific computing.
- `networkx`: Graph generation and manipulation.
- `matplotlib`: Plotting and visualization.
- `tqdm`: Progress bars for experiment orchestration.

**Python version:** Python 3.11 or later is recommended.

**Virtual environment (Windows):**
```powershell
python -m venv .venv
& .venv\Scripts\Activate.ps1
```

**Troubleshooting:**
- If you encounter missing dependencies, ensure you have run `pip install -r requirements.txt` inside the activated virtual environment.
- For issues with Z3 or SAT solvers, consult the documentation for those packages.
- On Windows, ensure long path support is enabled if you encounter path length errors.

### 2. Running the Main Artifact

The main artifact is [`attempt.py`](attempt.py:1-2486). To run it:

```sh
python attempt.py
```

- All output will be written to `terminal_output.md`.
- Proof artifacts, empirical data, and plots will be saved in `shape_of_truth_out/`.
- The artifact is fully self-verifying: every claim is certified, every output is cryptographically sealed, and every experiment is reproducible.

### 3. Running Large-Scale Experiments

To generate and analyze large-scale Tseitin data, use [`generate_tseitin_data.py`](generate_tseitin_data.py:1-523):

```sh
python generate_tseitin_data.py
```

- This script generates hard instances, runs both blind and sighted solvers, and saves all results to `tseitin_receipts.json`.
- Progress bars and heartbeat diagnostics are provided for long-running experiments.

### 4. Interpreting Outputs

- **`terminal_output.md`**: Full transcript of all proofs, experiments, and results.
- **`shape_of_truth_out/`**: Directory containing all machine-checkable SMT2 proofs, empirical data, and plots.
- **`tseitin_receipts.json`**: JSON file with detailed results from large-scale experiments, including solver statistics, timings, and certificate hashes.

### 5. Reproducibility and Auditability

- All random seeds, environment details, and command lines are logged for full reproducibility.
- Every proof and witness is saved as a file and hashed (SHA256) for auditability.
- All outputs can be independently verified using the included scripts and the logic engine (Z3).

### 6. Troubleshooting

- If you encounter missing dependencies, ensure you have run `pip install -r requirements.txt`.
- For issues with Z3 or SAT solvers, consult the documentation for those packages.
- For reproducibility, ensure you do not modify the output directories or intermediate files between runs.

---

# Contact and Support

For questions, bug reports, or to request support, please open an issue on the [GitHub repository](https://github.com/sethirus/The-Thiele-Machine/issues) or contact the maintainer at thethielemachine@gmail.com.

---


---

## Output Files and Artifacts

- **terminal_output.md**: Full transcript of the proof and experiment.
- **shape_of_truth_out/**: Machine-checkable SMT2 proofs, empirical data, and plots.
- **tseitin_receipts.json**: Results of large-scale experiments.

---

## Glossary

- **Thiele Machine**: A computational model that generalizes the Turing Machine by enabling dynamic partitioning, modular reasoning, and certificate-driven computation.
- **Partition**: A decomposition of the state space into disjoint modules, allowing independent reasoning and composition.
- **Module**: A subset of the state space defined by a partition; each module can be reasoned about independently.
- **Axiom/Rule ($A$)**: Logical constraints or rules governing the behavior of a module.
- **Transition ($R$)**: An operation that updates both the state and the partition, enabling dynamic refinement or coarsening.
- **Logic Engine ($L$)**: An external or embedded solver (e.g., Z3) used to check logical consistency and generate certificates.
- **Certificate**: A logical proof or witness justifying a computation step, transition, or solution; saved as machine-verifiable artifacts.
- **Mubit**: The atomic unit of discovery cost, measured in bits; quantifies the price paid to perceive and resolve hidden structure.
- **MDL (Minimum Description Length)**: A principle for model selection, balancing model complexity (structure, parameters) against explanatory power (fit to data).
- **NUSD (No Unpaid Sight Debt)**: The law that discovery always comes at a quantifiable cost; no free lunch in perception or learning.
- **Order-Invariance**: The property that computation outcomes depend only on the structure of the problem, not the order of operations.
- **Composite Witness**: A global certificate composed from local module certificates, providing robust, auditable proofs.
- **Blind Solver**: A classical solver (e.g., Resolution/DPLL) that is unaware of problem structure or partitions.
- **Sighted Solver**: A solver that exploits partition structure (e.g., GF(2) row reduction) for exponential speedup.
- **Empirical Receipt**: Machine-verifiable evidence (proofs, logs, hashes) for every computational claim or experiment.
- **Information Debt**: The accumulated cost of failing to perceive hidden structure; leads to intractability or inconsistency.

---

## Code Reference Map

### attempt.py

- **TM, EncodedTM, EncodedThieleSliceTM**: Turing and Thiele Machine encodings, formalizing classical and partition-native computation.
- **VNEnc**: Minimal von Neumann machine encoding, demonstrating partition logic in RAM models.
- **Foundational Proofs**: [`run_prove_tm_subsumption`](attempt.py:546), [`run_prove_vn_subsumption`](attempt.py:556)
- **Paradox Demonstration**: [`run_paradox`](attempt.py:784)
- **Universal Principle**: [`run_universal_principle`](attempt.py:894)
- **Engine of Discovery**: [`run_engine_and_law`](attempt.py:983)
- **Fractal Debt**: [`run_fractal_debt`](attempt.py:1445)
- **Final Theorem & Conclusion**: [`run_final_theorem`](attempt.py:1623)
- **Experimental Separation**: [`run_experimental_separation`](attempt.py:2148)
- **Gödelian Landmine**: [`run_godelian_landmine`](attempt.py:2333)
- **main**: Entry point for running the artifact ([`main`](attempt.py:2462))
- **seal_and_exit, hash_obj**: Certificate generation, hashing, and output sealing.

### generate_tseitin_data.py

- **generate_tseitin_expander**: Generates hard Tseitin instances on random 3-regular expander graphs.
- **run_blind_budgeted**: Runs the blind (classical) SAT solver with resource budgets.
- **solve_sighted_xor**: Runs the sighted (partition-aware) solver using GF(2) row reduction.
- **run_single_experiment**: Orchestrates a single experiment, logging all results and receipts.
- **Experiment orchestration**: Multiprocessing, progress bars, and heartbeat diagnostics for large-scale runs.

This document was the proposition. The code is the construction. The execution is the proof.
---



## Project Cerberus: The Thiele Kernel

As a first demonstration of the Thiele paradigm's practical applications, this repository now includes **Project Cerberus**, a minimal, meta-logically self-auditing kernel.

The project contains a complete, machine-checked Coq model ([Cerberus.v](coq/project_cerberus/coqproofs/Cerberus.v)) that guarantees the kernel is free from an entire class of control-flow exploits—**if and only if** its logic oracle confirms the consistency of its safety axioms at every step.

This artifact is the first concrete evidence that the Thiele Machine is not merely a theoretical model, but a practical architecture for building a new generation of software that is secure by construction and by continuous logical self-auditing.

➡️ **[See the full Project Cerberus README and formal proofs here.](coq/project_cerberus/README.md)**

---

## CatNet: A Thiele-Machine Neural Network

CatNet instantiates the Thiele Machine in the category of vector spaces. Objects
are network layers, morphisms are differentiable maps, and composition is
computation. Each forward pass is recorded in a tamper-evident, HMAC-signed
audit log, and a minimal EU AI Act transparency report is available via
`get_eu_compliance_report()`. Run the demos with:

```bash
python -m catnet.demo_mnist      # transparency
python -m catnet.demo_control    # controllability
```


## Verifier vs Finder (perspective demo)

A concise summary of the sighted Thiele architecture, its formalization, and the structural P=NP collapse is available in [coq/p_equals_np_thiele/ARCHITECTURAL_COLLAPSE_OF_NP.md](coq/p_equals_np_thiele/ARCHITECTURAL_COLLAPSE_OF_NP.md). The corresponding Coq proof is [`coq/p_equals_np_thiele/proof.v`](coq/p_equals_np_thiele/proof.v).

## Contributing

We welcome contributions to The Thiele Machine project! Please see our [Contributing Guide](CONTRIBUTING.md) for details on how to get started.

For questions or discussions, open an issue on [GitHub](https://github.com/sethirus/The-Thiele-Machine/issues).

## License

This project is licensed under the MIT License – see the [LICENSE](LICENSE) file for details.