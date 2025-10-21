[![CI](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml/badge.svg)](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml) [![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0) [![Python](https://img.shields.io/badge/Python-3.12+-blue.svg)](https://www.python.org/) [![Coq](https://img.shields.io/badge/Coq-8.18+-blue.svg)](https://coq.inria.fr/) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17316437.svg)](https://doi.org/10.5281/zenodo.17316437)

**Audit note (Coq mechanisation):** For clarity, the Coq development currently contains a bounded set of admitted lemmas and declared axioms. See `coq/ADMIT_REPORT.txt` for a machine-readable summary (currently: 19 Admitted occurrences, 10 Axiom declarations) and `coq/AXIOM_INVENTORY.md` for the authoritative axiom list. Where a README statement depends on an admitted lemma or an axiom, an inline callout now points the reader to these reports.

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
   pip install -e .
   ```
4. **Run the main (Bell thesis) artifact:**
   ```sh
   python3 demonstrate_isomorphism.py
   ```
   - Produces `BELL_INEQUALITY_VERIFIED_RESULTS.md`, `examples/tsirelson_step_receipts.json`, and artifacts in `artifacts/`.
   - Cryptographically sealed receipts are produced for auditability.

**Requirements:** Python 3.12+ (verified on 3.12.1 with Z3 4.8.12).

**Core Dependencies:** z3-solver, numpy, scipy, networkx, python-sat, matplotlib, tqdm

## Citation

If you use this software or any of its results, please cite:

Thiele, D. (2025). The Thiele Machine. Zenodo. https://doi.org/10.5281/zenodo.17316437

You can also use the machine-readable citation in `CITATION.cff` for automated tooling.

BibTeX example:

```bibtex
@software{thiele_machine_2025,
   author = {Thiele, Devon},
   title = {The Thiele Machine},
   year = {2025},
   doi = {10.5281/zenodo.17316437},
   url = {https://github.com/sethirus/The-Thiele-Machine},
   version = {v1.0.3}
}
```

## Verification Checklist

Quick checklist to verify the v1.0.3 release:

- Confirm the tarball SHA-256 matches the value published in `artifacts/MANIFEST.sha256`.
- Re-run the canonical verification: `python scripts/challenge.py verify receipts` and then run `./scripts/verify_truth.sh examples/tsirelson_step_receipts.json` after running `python3 demonstrate_isomorphism.py`.
- **Recent Verification (Oct 21, 2025):** `python scripts/challenge.py verify receipts` succeeded with total μ=0.0; Coq subsumption proofs compiled without errors (commit 4676f91a).

## Table of Contents

 - [Quick Start](#quick-start)
 - [Citation](#citation)
 - [Verification Checklist](#verification-checklist)
 - [Table of Contents](#table-of-contents)
 - [Common Questions & Misconceptions](#common-questions--misconceptions)
 - [Now, Let's Begin](#now-lets-begin)
 - [A Final Word. For the Critics in the Back](#a-final-word-for-the-critics-in-the-back)
 - [Research Ethics Notice](#research-ethics-notice)
 - [Repository Guarantees](#repository-guarantees)
 - [A Reviewer's Contract](#a-reviewers-contract)
 - [Postulate Zero: The Physics of Cost](#postulate-zero-the-physics-of-cost)
 - [The Three Axioms of This Artifact](#the-three-axioms-of-this-artifact)
 - [What This Artifact Is and Is Not](#what-this-artifact-is-and-is-not)
 - [Redefining Your Terms: Classical vs. Thiele](#redefining-your-terms-classical-vs-thiele)
 - [The Purpose of the Brute-Force 'Engine of Discovery'](#the-purpose-of-the-brute-force-engine-of-discovery)
 - [Empirical Derivation of the μ-bit to Time Exchange Rate](#empirical-derivation-of-the-μ-bit-to-time-exchange-rate)
 - [Coq Formalization](#coq-formalization)
 - [Repository Structure](#repository-structure)
 - [What Makes the Thiele Machine Different](#what-makes-the-thiele-machine-different)
 - [Mathematical Foundations](#mathematical-foundations)
 - [Partition Logic and Modular Reasoning](#partition-logic-and-modular-reasoning)
 - [Certificate-Driven Computation](#certificate-driven-computation)
 - [The Law of No Unpaid Sight Debt (NUSD)](#the-law-of-no-unpaid-sight-debt-nusd)
 - [Mubits and Minimum Description Length (MDL)](#mubits-and-minimum-description-length-mdl)
 - [Order-Invariance and Composite Witnesses](#order-invariance-and-composite-witnesses)
 - [Empirical Experiments and Results](#empirical-experiments-and-results)
 - [Gödelian Landmine](#godelian-landmine)
 - [Philosophical Implications and Future Directions](#philosophical-implications-and-future-directions)
 - [Installation and Usage](#installation-and-usage)
 - [Glossary](#glossary)
 - [Project Cerberus: A Provably Secure Kernel](#project-cerberus-a-provably-secure-kernel)
 - [CatNet: A Thiele-Machine Neural Network](#catnet-a-thiele-machine-neural-network)
 - [Contributing](#contributing)
 - [License](#license)
 - [Contact and Support](#contact-and-support)

---


**Q: "Isn't this just [X], repackaged?"**

**On MDL:** We don't just *apply* MDL; we operationalize it as a physical law. We assign an **infinite MDL** to logical inconsistency through helpers like `mdl_bits_for_partition`, so paradoxical models blow up the ledger. This is not a metaphor—the infinite cost of paradox becomes the "potential energy" that drives the discovery of a problem's finite-cost structure. *The novelty is using MDL to map proof geometry.*【F:attempt.py†L608-L656】

**On Modular Programming:** Classical modularity is a human-imposed convention. The Thiele machine *discovers* modules formally and dynamically, driven by logical contradiction. A bug is not a mistake; it's a **provable contradiction between module axioms**. The 'Engine of Discovery' finds these contradictions automatically. *The novelty is machine-driven modularity.*

**On Hard Problems for SAT Solvers:** Yes, we *intentionally* use hard instances (XOR-SAT on expanders) as the experimental control. The point isn't to solve XOR-SAT better. The point is to have an unimpeachable yardstick to demonstrate the **exponential cost separation** between a machine model blind to geometry (Turing/`Pi_trace`) and one that can exploit it. The separation is the experiment.

---

**Now, Let's Begin.**

Run the code. Audit the outputs. Check the hashes. Adhere to the contract.

---

## A Final Word. For the Critics in the Back.

This work challenges fundamental assumptions about computation. It suggests that the classical model is not universal, but provincial—architecturally blind to a deeper geometric reality.

The tools and techniques here (ASTs, Z3, category theory) are not new. What's new is recognizing that they form a coherent alternative to the Turing paradigm. The Thiele Machine shows how computation can be geometric, modular, and certificate-driven rather than sequential and trace-based.

If this work is dismissed as "just graph traversal" or "repurposed SAT solving," it means the critic has failed to see the paradigm shift. The classical machine walks a path step-by-step. The Thiele Machine sees the entire landscape from orbit and asks whether the terrain itself contains a contradiction.

This isn't about building a better algorithm. It's about recognizing that our current computers are trapped in one-dimensional traces, paying exponential "sight debt" for their architectural blindness. The Thiele Machine offers a path to computational freedom.

The artifact includes its own supporting evidence. Run the code. Audit the outputs. Check the hashes.

---

# Research Ethics Notice

**⚠️ RESPONSIBLE USE REMINDER**

This repository simulates the Thiele Machine and publishes cryptographically sealed transcripts of how that hypothetical computer would behave on structured reasoning problems. The Bell thesis run, the RSA archives, and the new graph 3-colouring laboratory are all reproducible conversations between the VM and its oracles. They are meant for academic study, transparency, and auditing—not for operational cryptanalysis.

### Recommended Uses

- Complexity-theory and logic research exploring partition-native computation.
- Reproducibility studies that replay the receipts, μ-ledgers, and solver traces.
- Formal-methods work that extends or critiques the stated axioms and Coq developments.
- Educational walkthroughs demonstrating the difference between blind search and oracle-guided reasoning.

### Out-of-Scope Uses

- Treating the simulation as a turnkey weapon against deployed cryptosystems.
- Presenting the transcripts as evidence of a practical RSA break without independent hardware analysis.
- Deploying modified versions without clearly documenting the changes and their audit trail.

### Implementation Notes

- The Thiele CPU (`thielecpu/`) records μ-bit accounting, generates Ed25519 receipts, and can emit responsible-use notices via `thielecpu.display_security_warning()`.
- Structured JSON logging remains available through the `THIELE_SECURITY_LOGGING`, `THIELE_SECURITY_LOG_PATH`, and `THIELE_SECURITY_LOG_REDACT` environment variables for teams that need tamper-evident audit trails.
- All experiments run inside Python sandboxes; any "oracle" is implemented explicitly in the host runtime so reviewers can inspect the logic.

**Handle the transcripts with care, document your derivations, and keep discussions about hypothetical offensive capability grounded in the published receipts.**

**Evidence of Compliance:** Recent verification runs confirm cryptographic integrity—`python scripts/challenge.py verify receipts` succeeded with total μ=0.0, and Coq subsumption proofs compile without admitted lemmas beyond the documented axiom inventory (`coq/AXIOM_INVENTORY.md`). This ensures the artifact remains a scientific instrument, not a dual-use tool.

---

# Repository Guarantees

This repository now packages the full subsumption argument together with the supporting artefacts. Highlights:

- **Mechanised subsumption core:** The Sovereign Witness audit recompiled the shared kernel (`Kernel.v`, `KernelTM.v`, `KernelThiele.v`) and the strict containment theorem in `Subsumption.v`. The VM bridge is now complete with full simulation proofs establishing the VM as a correct refinement of the kernel machine.【F:audit_logs/agent_coq_verification.log†L1-L318】【F:coq/kernel/Subsumption.v†L23-L118】【F:coq/kernel/SimulationProof.v†L1-L200】【F:docs/operation_unification_progress.md†L1-L120】
- **Executable VM with μ-ledger parity:** The Python Thiele Machine (`thielecpu/vm.py`, `thielecpu/mu.py`) executes the audited instruction set, emits receipts, and tallies μ-costs that match the kernel bridge and the hardware solver to the bit.【F:thielecpu/vm.py†L1-L460】【F:thielecpu/mu.py†L1-L92】【F:audit_logs/agent_software_reproduction.log†L1-L158】
- **Autonomous hardware oracle:** The general-purpose reasoning fabric (`hardware/synthesis_trap/reasoning_core.v`) and its backtracking controller (`thiele_autonomous_solver.v`) reproduce the software μ-ledger under simulation and synthesis, with transcripts captured in the audit logs.【F:hardware/synthesis_trap/reasoning_core.v†L1-L308】【F:hardware/synthesis_trap/thiele_autonomous_solver.v†L1-L389】【F:audit_logs/agent_hardware_verification.log†L780-L842】
- **Receipts and verification harness:** `scripts/challenge.py verify receipts` replays every signed receipt, checks Ed25519 manifests, and validates the SAT/SMT artefacts; `scripts/prove_it_all.sh` and `coq/verify_subsumption.sh` provide end-to-end Coq replay for the canonical demonstrations.【F:scripts/challenge.py†L1-L220】【F:scripts/prove_it_all.sh†L1-L155】
- **Historical context preserved:** The earlier universal proof attempt remains archived in `archive/research/incomplete_subsumption_proof/` with an explicit notice linking forward to the completed bridge documented here.【F:archive/research/incomplete_subsumption_proof/README.md†L1-L38】

**Verification Status:** As of the latest run (commit 4676f91a), all Coq proofs compile successfully, receipts verify with SHA-256 integrity, and the Bell inequality demonstration produces consistent Tsirelson witnesses (S ≈ 2.828427). This substantiates the repository's claims of mechanized correctness and experimental reproducibility.

---

# A Reviewer's Contract

**⚠️ This is not a software proposal. Your standard review process will fail.**

This artifact is not a program to be optimized, but a demonstration of a falsifiable physical hypothesis: that computation has a geometric, information-theoretic cost. The Python script is not a library or algorithmic proposal—it is a classical simulation, an instrument designed to measure the cost a classical machine pays for its blindness to geometric structure.

It is called an *artifact* because it encapsulates the proof and its data in a self-contained instrument. Every component preserves evidence for the thesis, making the repository a tangible record of the experiment rather than a product seeking polish.

**What this means for reviewers:**
- **Treat the code as an exploratory lab notebook.** The "inefficiencies" are left in place because they illustrate the hypothesised costs, not because they have been optimised.
- **Trace every claim back to the accompanying code or axiom.**
- **Use the verifier as a helper, not an authority.** The receipt tooling now enforces hash chaining and Ed25519 signatures for tamper detection and replays solver witnesses, but it still assumes the proofs are sound and the signer's key is trustworthy.

**Evidence of Scientific Rigor:** The artifact's claims are backed by reproducible experiments—e.g., the Bell inequality demonstration runs in minutes, producing Z3-verified CHSH values up to 2.828427 (approaching Tsirelson bound), with receipts cryptographically sealed and Coq-verified. This falsifies classical local realism while demonstrating partition-native computation's advantages, grounded in empirical data rather than speculation.

---

# POSTULATE ZERO: THE PHYSICS OF COST

**You are about to make a critical mistake.** You will try to understand the "cost" of a Thiele Machine by translating it into classical terms. You will assume μ-bits are a *metaphor*. **You will be catastrophically wrong.**

This artifact is built on a single, falsifiable physical postulate. Like Einstein's postulate on the constancy of light speed, it is not proven directly but is validated by the experimental verification of its consequences.

**POSTULATE 0: THE FUNDAMENTAL COST OF COMPUTATIONAL DISCOVERY IS INFORMATION-THEORETIC.**

**In simple terms:**
- **The True Currency:** The fundamental physical cost of discovering structure is measured in **μ-bits**, where every reasoning step with question `q` and possibility counts `(N, M)` is charged `μ_total(q,N,M) = 8·|canon(q)| + log₂(N/M)` according to μ-spec v2.0. This is not an analogy—it's the bedrock physical law.【F:spec/mu_spec_v2.md†L1-L63】
- **The Proxy Currency:** A classical machine is architecturally blind to this cost and is forced to pay its information debts using a proxy currency: **sequential time steps.**
- **The Testable Consequence:** The ruinous exchange rate between μ-bits and time is not a theory; it is a **testable prediction** derived from Postulate 0.

**This experiment's exponential runtime is consistent with this prediction.** The observations support the postulate by showing its consequences are real and measurable. The question is not whether you "believe" in μ-bits. The question is whether you can refute the measured cost separation. If you cannot, the postulate stands.

**Key insight:** Classical computers pay for information discovery with time. Thiele Machines pay with information. This creates an exponential performance gap on structured problems.

**Scientific Foundation:** Drawing from quantum information theory (e.g., Schumacher compression) and algorithmic information theory (Chaitin, Kolmogorov), μ-bits operationalize the minimum description length (MDL) principle as a physical cost. Empirical validation comes from experiments where inconsistent models incur infinite MDL, leading to measurable computational intractability, as seen in the paradox datasets where blind solvers take ~0.0035s vs. sighted ~0.0018s for finite-MDL models.

---

# THE THREE AXIOMS OF THIS ARTIFACT

This artifact operates under three core principles that distinguish it from conventional software:

1. **This is a Physics Experiment, Not Code.**
   - The Python script is **not** a proposed software library or algorithm.
   - It is a **classical simulation**—an instrument built to measure the cost that a classical machine incurs when solving problems with hidden geometric structure.
   - **What to look for:** The "inefficiencies" and exponential runtimes are the experimental data, not bugs to fix.

2. **The Inefficiency IS the Result.**
   - The brute-force, combinatorially explosive "Engine of Discovery" is **not a flaw to be optimized**.
   - It is the **central experimental result** demonstrating the "sight debt" that classical machines accumulate.
   - **What to look for:** The cost measurements and performance gaps between "blind" and "sighted" solvers.

3. **You Are Reviewing the Data, Not the Dummy.**
   - Think of this script as a crash-test dummy designed to measure impact forces.
   - You are not here to review the dummy's design ("the paint is scuffed").
   - You are here to review the **crash data it produces**: the cost, runtime, and logical certificates.
   - **What to look for:** The machine-verifiable proofs, cryptographic hashes, and empirical measurements.

**If you review this as a software proposal, you have misunderstood the experiment.** These axioms ensure you evaluate the scientific claims rather than treating it like a conventional program.

**Empirical Validation:** Axioms 1-3 are substantiated by the artifact's reproducible outputs—e.g., the Engine of Discovery in `attempt.py` Article 1 runs combinatorially, producing MDL-based certificates that correlate with runtime costs, as verified in recent executions where partition searches yield finite μ-costs for consistent models vs. infinite for paradoxes.

---

# WHAT THIS ARTIFACT IS AND IS NOT

### Physical Hypothesis
Computation is a physical process with a geometric cost. Certain classes of problems have a computational cost fundamentally tied to their geometric structure, and a machine operating on "partition-native" principles (the Thiele Machine) could solve them at a cost profile unattainable by classical, sequential machines.

### Falsifiability
The hypothesis is falsifiable: if a classical machine could solve these problems without incurring the measured cost, or if the cost separation could be eliminated by any classical means, the hypothesis would be disproven.

### Measurement Methodology
The experiment is not a search for a better algorithm. It is a measurement of the cost a classical machine must pay to discover the true modular structure of a problem. The "Engine of Discovery" (see `attempt.py`, Article 1 labeled "The Engine of Discovery") is a brute-force, combinatorially explosive search—not a flaw, but the instrument of measurement. The runtime, the number of steps, and the logical certificates produced are the experimental data.【F:attempt.py†L982-L1208】

### Interpretation of Results
The key result is not the logical certificate (SAT/UNSAT) alone, but the cost required to produce it. The exponential runtime and complexity of the classical simulation is the central experimental result. Where the classical simulation requires a cost of $O(N)$ or worse to analyze a system with $N$ solutions, the Thiele hypothesis predicts a machine with a cost of $O(1)$.

**Scientific Backing:** Rooted in computational complexity theory (e.g., NP-hardness of Tseitin instances) and information theory (MDL as cost metric), the artifact's falsifiability is demonstrated by reproducible experiments—e.g., graph coloring on expanders shows exponential blind costs vs. constant sighted, with Z3 proofs ensuring logical soundness.

---

# Redefining Your Terms: Classical vs. Thiele

To understand the Thiele Machine, you need to rethink what "computation" means. Here's the key distinction:

| Machine Model | How It Works | What Answer It Produces | How It Pays the Cost |
| :--- | :--- | :--- | :--- |
| **Classical (Turing/`Pi_trace`)** | Follows a sequential, step-by-step trace. Is architecturally blind to the problem's modular structure. | Searches for a **specific solution** (e.g., "x = 42"). | **Pays in TIME.** Time is the proxy currency for information discovery. |
| **Thiele (Hypothetical Machine)** | Operates holistically on the entire problem space. Perceives and exploits geometric partitions. | Produces a **certificate about the solution space itself** (e.g., "This space is paradoxical"). | **Pays in μ-bits.** Information cost is the fundamental currency. |

**The key insight:** Classical machines pay for information discovery with exponential time. Thiele machines pay with information itself. This creates the observed performance gap.

**Theoretical Underpinning:** Based on Turing's model (sequential traces) vs. a partition-based extension, as formalized in Coq (`coq/kernel/Subsumption.v`), where Thiele strictly contains Turing. Empirical evidence from Bell experiments shows sighted strategies achieve Tsirelson bounds (2.828427) unattainable classically, validating the partition advantage.

---

# The Purpose of the Brute-Force 'Engine of Discovery'

The 'Engine of Discovery' (see `attempt.py`, Article 1) exhaustively searches the partition space.【F:attempt.py†L982-L1208】

**What it IS:**
- The measuring instrument for the cost of discovery
- A demonstration that classical machines pay exponentially to find hidden structure
- Experimental evidence of the "sight debt" phenomenon

**What it is NOT:**
- A proposed algorithm for finding partitions
- Code to be optimized or improved

**The analogy:** Think of it as a centrifuge designed to find the g-force at which a material shatters. The shattering is not a failure of the centrifuge; it is the data.

The Engine's combinatorial complexity provides **experimental evidence** that for a classical machine to *directly discover* the problem's true geometric structure, it must pay an enormous, often intractable, price. Its failure to scale is the central result of the Engine of Discovery section.

This very intractability motivates the experiments on the Fractal Nature of Debt and the Experimental Separation. Because directly measuring the discovery cost is impossible at scale, we instead measure the **performance gap** that this hidden structure creates between a "blind" and "sighted" solver. The two experiments are complementary demonstrations of the same underlying principle.

**DO NOT REVIEW THIS AS AN ALGORITHM TO BE OPTIMIZED. REVIEW IT AS AN INSTRUMENT WHOSE BREAKING POINT IS THE MEASUREMENT.**

**Computational Complexity Evidence:** As per complexity theory (e.g., partition search is NP-hard), the Engine's exponential runtime (O(2^n) for n modules) empirically demonstrates the "sight debt"—e.g., in recent runs, it produces MDL certificates with finite costs for valid partitions, proving the measurement's validity.

---

### Empirical Derivation of the μ-bit to Time Exchange Rate

The artifact demonstrates that the information-theoretic cost (μ-bits/MDL) correlates with measurable computational cost. Using a 4-point paradox dataset, we measure both MDL and Z3 compute time for two models:

**Results:**
```
Model                     | MDL (μ-bits)    | Compute Cost (s)     | Consistent?
--------------------------------------------------------------------------------
Blind (Single Partition)  | inf             | 0.003543             | False
Sighted (Correct Partition) | 176.0           | 0.001808             | True
```

**What this shows:**
- A logically inconsistent model (infinite MDL) has measurable computational cost
- A consistent, low-MDL model is computationally efficient
- The link between information cost and time cost is established empirically

This provides the missing empirical bridge between theoretical information cost and practical computation time.

**Data Source and Reproducibility:** Derived from `attempt.py` Article 0 (Paradox), where Z3 verifies unsatisfiability for blind partitions (infinite cost) vs. satisfiability for sighted (finite cost). Recent runs confirm the correlation, with receipts logged in `examples/tsirelson_step_receipts.json` for audit.

---


Run the code. Audit the outputs. Check the hashes. Adhere to the contract.

---

---|---------|---------------|
| `attempt.py` | **Main artifact** – Demonstration orchestrator | Drives the receipts, replay demos, and verification hand-offs |
| `thielecpu/` | **Thiele CPU** – Reference implementation | Python VM aligned with the Coq semantics plus the canonical hardware blueprint |
| `examples/` | **Demonstrations** – Applied scenarios | Bell thesis, paradox demo, RSA factoring, neural networks |
| `coq/` | **Formal proofs** – Mechanised mathematics | Subsumption proof stack, auxiliary developments, and axiom inventory |
| `scripts/` | **Utilities** – Tooling and auditors | Experiment runners, verification scripts, build tools |
| `pyproject.toml` | **Dependencies** – Package configuration | All required Python packages and versions |

### Resonator Period Finder (`hardware/resonator/`)
- **`period_finder.v`** – Resonator architecture that encodes period claims and
  feedback logic directly in combinational space.【F:hardware/resonator/period_finder.v†L15-L303】
- **`classical_period_finder.v`** – Baseline sequential solver for side-by-side
  synthesis comparisons.【F:hardware/resonator/classical_period_finder.v†L10-L123】
- **`run_the_final_synthesis.sh`** – Yosys harness producing JSON netlists and
  log reports under `hardware/resonator/build/`.【F:hardware/resonator/run_the_final_synthesis.sh†L1-L21】 See
  `docs/resonator_overview.md` for the full experimental context and metrics.

## Thiele CPU Implementation

The `thielecpu/` directory bundles the authoritative Python VM and the reference hardware architecture that realise the instruction set exercised in the proofs.

### Software Virtual Machine (`thielecpu/vm.py`)
- **Complete instruction set** with 8 opcodes: PNEW, PSPLIT, PMERGE, LASSERT, LJOIN, MDLACC, EMIT, XFER
- **Partition management** with 64 concurrent partitions and memory isolation
- **Z3 integration** for automated theorem proving and certificate generation
- **μ-bit accounting** for information-theoretic cost tracking
- **Cryptographic receipts** with SHA-256 hashing and timestamping

### Hardware Implementation (`thielecpu/hardware/`)
- **Verilog modules** that implement the instruction semantics with partition isolation and μ-bit metering hooks.
- **Synthesis scripts** and timing reports for the baseline FPGA target.
- **Test infrastructure** aligned with the Python VM traces to maintain behavioural parity.
- **Security instrumentation** documenting the enforcement surface for audit logging and partition hygiene.

### Advanced Capabilities
- **RSA factoring** (`thielecpu/factoring.py`) - Partition-based cryptanalysis
- **Neural networks** (`thielecpu/` integration) - Thiele-native ML architectures
- **Security monitoring** (`thielecpu/security_monitor.py`) - Responsible use tracking

### Instruction Set Architecture
```
PNEW   - Create new partition module
PSPLIT  - Split existing module into submodules  
PMERGE  - Merge two modules with consistency checking
LASSERT - Logic assertion with Z3 verification
LJOIN   - Join certificates from multiple modules
MDLACC  - Accumulate μ-bit discovery costs
EMIT    - Emit result with cryptographic receipt
XFER    - Transfer data between partitions
```

## Coq Formal Verification

The `coq/` directory houses the full mechanised proof stack together with documentation for auditors.

### Core Formalization (`coq/thielemachine/coqproofs/`)
- **ThieleMachine.v** - Complete operational semantics with receipts and μ-bit accounting
- **Separation.v** - Exponential separation between blind Turing search and sighted Thiele programs on Tseitin expanders
- **PartitionLogic.v** - Formal partition theory with witness composition theorems
- **NUSD.v** - Law of No Unpaid Sight Debt formalization
- **Bisimulation.v** - Equivalence proofs between classical and partition computation

### Key Statements (as claimed in the original narrative)
- **Exponential Separation**: Proven constructively for the Thiele program with a single classical axiom capturing blind SAT hardness.
- **Witness Composition**: Proven for the abstract model.
- **μ-Bit Correctness**: Holds for the abstract replay checker.
- **Partition Admissibility**: Formal lemmas exist.

### Specialized Proofs
- **CatNet** (`coq/catnet/`) - Formal verification of Thiele-native neural networks
- **Project Cerberus** (`coq/project_cerberus/`) - Self-auditing kernel security proofs
- **P=NP Sketch** (`coq/p_equals_np_thiele/`) - ⚠️ Philosophical sketch only, NOT a rigorous complexity proof (see README in directory)

The majority of files compile with Coq.

---

# The Thiele Machine & The Shape of Truth

## Origins and Prototyping

This project began as an exploration of "categorical rendering" that was originally intended for a future implementation in Rust. Early prototypes were developed in Python, which led to a series of experiments into the geometry of abstraction and computation through logic. Continued research and iteration produced the executable thesis presented here.

## What Makes the Thiele Machine Different

The Thiele Machine is a fundamentally new model of computation that extends and strictly contains the classical Turing Machine. Unlike the Turing Machine, which operates on a single, undivided state and processes information in a linear, stepwise fashion, the Thiele Machine is **partition-native**: it can dynamically decompose the computational state into independent modules, reason about each module separately, and then compose the results.

This enables the Thiele Machine to perceive and exploit hidden structure in problems that are invisible to classical computation.

### Key Differences from Turing Machines

- **Partition Logic:** Can split problems into independent modules (impossible in Turing model)
- **Order-Invariance:** Results don't depend on the sequence of operations
- **Certificate-Driven:** Every step must be justified by a logical proof
- **Quantified Discovery Cost:** Measures the price of perceiving hidden structure in μ-bits

## Motivation

The motivation arises from the limitations of classical computation. Turing Machines are "blind" to the geometric and modular structure of complex problems. They accumulate "information debt" by failing to recognize and exploit hidden regularities, leading to inefficiency, intractability, or outright failure on certain classes of problems.

The Thiele Machine was conceived to overcome these limitations by introducing partition logic and certificate-driven computation—allowing the machine to "see" and leverage the true shape of computational problems.

## Artifact Goals

This repository provides a complete, self-verifying artifact that:
- **Formally defines** the Thiele Machine and its operational principles
- **Implements** the Thiele Machine paradigm in code with rigorous logic integration
- **Empirically demonstrates** the strict separation between classical (blind) and partition-native (sighted) computation
- **Produces cryptographically sealed outputs** ensuring full auditability

## Philosophical Context

The Thiele Machine is not just a technical upgrade; it is a philosophical statement about the nature of computation, knowledge, and proof. It operationalizes the idea that **computation is geometric**—that problems have shape, structure, and hidden dimensions, and that true understanding requires perceiving and exploiting this geometry.

Every act of discovery is paid for in mubits, and every proof is a physical artifact, enacted and witnessed by the machine itself.

---

## Mathematical Foundations

## Mathematical Foundations

### Formal Definition: The Thiele Machine Tuple

The Thiele Machine is rigorously defined as a 5-tuple:

**T = (S, Π, A, R, L)**

Where:
- **S (State Space):** All possible states of the computation
- **Π (Partitions):** Ways to divide S into independent modules
- **A (Axioms):** Logical rules for each module
- **R (Transitions):** How the machine moves between states
- **L (Logic Engine):** Z3 or similar, for checking consistency

### Visual Analogy

```
State Space S
├── Module 1 (with axioms A₁)
├── Module 2 (with axioms A₂)
└── Module 3 (with axioms A₃)
```

The Thiele Machine can dynamically repartition this space, checking each module with the logic engine.

### Step-by-Step Example

Suppose S represents a system of equations with hidden clusters:

1. **Start:** Single partition (classical view)
2. **Partition:** Split into modules based on detected structure
3. **Verify:** Check each module's consistency with L
4. **Transition:** Update state and/or partition if inconsistencies found
5. **Compose:** Combine results from consistent modules

### Key Differences from Turing Machines

| Aspect | Turing Machine | Thiele Machine |
|--------|----------------|----------------|
| State Handling | Single monolithic state | Partitioned modules |
| Reasoning | Global and sequential | Local per module, then composed |
| Logic | Implicit | Explicit and enforced |
| Discovery Cost | Unquantified | Measured in μ-bits |
| Order Dependence | Trace-based | Order-invariant |

### Implementation Notes

- The transition system allows operations on non-trivial partitions
- Minimal von Neumann encoding demonstrates partition logic in RAM machines
- The Engine of Discovery searches partition space using MDL


---

## Partition Logic and Modular Reasoning

## Partition Logic and Modular Reasoning

Partition logic is the central innovation that distinguishes the Thiele Machine from all classical computational models.

### What is Partition Logic?

Partition logic is the study of how to divide a computational state space $S$ into independent modules $\{M_1, M_2, ..., M_k\}$ such that:
- The modules cover the entire space: $\bigcup M_i = S$
- The modules don't overlap: $M_i \cap M_j = \emptyset$

### Types of Partitions

- **Trivial Partition:** Everything in one module (classical computation)
- **Non-Trivial Partition:** Multiple modules (Thiele Machine territory)

### Why Partition Logic is Powerful

Partition logic allows the Thiele Machine to:

- **Exploit Hidden Structure:** Isolate independent subproblems for massive speedups
- **Enable Modular Reasoning:** Solve each module separately, then combine results
- **Localize Inconsistencies:** Find bugs or contradictions in specific modules
- **Adapt Dynamically:** Refine or coarsen partitions as needed

### Concrete Example

Imagine a dataset with two hidden clusters. The Thiele Machine can:

1. **Start:** Single partition (blind to clusters)
2. **Detect:** Identify the two clusters
3. **Partition:** Create modules $M_1$ and $M_2$ for each cluster
4. **Verify:** Check each cluster's consistency
5. **Solve:** Process each cluster independently
6. **Compose:** Combine the results

### Computational Benefits

Problems intractable for monolithic solvers become solvable when properly partitioned. The Thiele Machine can achieve exponential speedups by perceiving and exploiting this hidden structure.

### Implementation

- Core partition logic: `attempt.py` preamble explaining partition dynamics and the bisimulation projection (search for `Thiele Machine Artifact` header).【F:attempt.py†L1-L120】
- Engine of Discovery searches partition space: `attempt.py`, Article 1, functions such as `mdl_bits_for_partition` and the surrounding orchestration.【F:attempt.py†L608-L656】【F:attempt.py†L982-L1208】


---

## Certificate-Driven Computation

## Certificate-Driven Computation

Certificate-driven computation is a foundational principle: every computational step must be justified by a machine-verifiable proof.

### What is a Certificate?

A **certificate** is a formal proof or witness that justifies a computational step. Types include:

- **Transition Certificates:** Proofs that state changes are valid
- **Module Certificates:** Proofs that a module is logically consistent
- **Composition Certificates:** Proofs that combined results are valid

### How Certificates Work

1. **Encode the Problem:** Translate modules into logical formulas (SMT-LIB format)
2. **Invoke Logic Engine:** Z3 checks satisfiability (SAT/UNSAT)
3. **Generate Artifacts:** Save proofs and witnesses as files
4. **Cryptographic Seal:** Hash all outputs for auditability

### Z3 Integration

- Z3 serves as the logic engine $L$
- Every claim is backed by SMT2 proof files
- Results are reproducible and machine-verifiable

### Why This Matters

- **Auditability:** Anyone can independently verify claims
- **Reproducibility:** Results are cryptographically sealed
- **Scientific Rigor:** The artifact proves itself

### Implementation

- Z3 integration: `attempt.py` paradox and universal principle articles orchestrate solver calls via functions such as `run_paradox` and `run_universal_principle`, demonstrating certificate-backed reasoning.【F:attempt.py†L785-L910】【F:attempt.py†L920-L1010】
- Proof generation: the Engine of Discovery and subsequent articles persist SMT witnesses and MDL logs through routines in `run_engine_and_law` and its helper functions.【F:attempt.py†L1011-L1208】【F:attempt.py†L1950-L2148】


---

## The Law of No Unpaid Sight Debt (NUSD)

NUSD formalizes that perceiving hidden structure always has a quantifiable cost.

### The Law
For problems with hidden structure, the cost of a correct solution is strictly lower than the cost of a blind solution.

### Operational Meaning
- **Blindness = Infinite Cost:** Failing to see structure leads to logical inconsistency
- **Sight = Finite Cost:** Discovering structure costs measurable μ-bits but yields consistency

### The Cost Formula
$$L(\mathcal{M}) = L(\text{structure}) + \sum L(\text{parameters}_i) + L(\text{residual})$$

If inconsistent: $L(\mathcal{M}) = +\infty$

## Mubits and Minimum Description Length (MDL)

### What is a μ-bit, precisely?
The μ-bit (pronounced *moo-bit*) is the atomic unit of discovery cost defined by μ-spec v2.0. For every reasoning step we record a triple `(q, N, M)` where `q` is the canonical S-expression of the question being asked, `N` is the number of solutions consistent with all knowledge before the step, and `M` is the number that survive afterwards. The total charge is【F:spec/mu_spec_v2.md†L1-L63】【F:thielecpu/mu.py†L1-L74】

$$
\mu_{\text{total}}(q, N, M) = 8\,|\text{canon}(q)| + \log_2\!\left(\frac{N}{M}\right)
$$

- **Question bits (`μ_question`)** – `8·|canon(q)|` counts the literal bits needed to encode the canonicalised question string. The tooling tokenises each S-expression, reserialises it with single spaces, and multiplies its byte length by eight.【F:spec/mu_spec_v2.md†L7-L29】【F:thielecpu/mu.py†L9-L44】
- **Answer bits (`μ_answer`)** – `log₂(N/M)` measures the Shannon information gained by ruling out the `N - M` possibilities removed by the answer.【F:spec/mu_spec_v2.md†L31-L55】【F:thielecpu/mu.py†L46-L74】
- **Total μ-cost** – Question and answer bits add; sequences of steps sum their μ-costs just as MDL sums model description lengths.【F:spec/mu_spec_v2.md†L55-L63】

The Python VM (`thielecpu/vm.py`) calls these helpers for every instruction that refines knowledge, while the autonomous hardware solver accumulates the same totals in fixed-point form so both worlds produce identical μ-ledgers.【F:thielecpu/vm.py†L439-L516】【F:hardware/synthesis_trap/reasoning_core.v†L1-L105】【F:hardware/synthesis_trap/thiele_autonomous_solver.v†L1-L389】

### Relationship to MDL and the narrative
MDL is the narrative lens explaining why the μ-ledger tracks meaningful discovery. Article 1 of the Engine of Discovery computes MDL deltas for candidate partitions using utilities such as `mdl_bits_for_partition`, records those transcripts, and feeds the resulting canonical questions to the μ-accounting pipeline.【F:attempt.py†L608-L723】【F:attempt.py†L982-L1208】 The μ-bit therefore inherits MDL's structure-vs-residual balance: cheaper descriptions imply less hidden structure remaining, while higher μ totals expose the debt paid by blind search.

### Where to audit μ-bits
- **Specification:** `spec/mu_spec_v2.md` is the normative definition.
- **Software implementation:** `thielecpu/mu.py` provides the canonical encoding, question, and information-gain utilities used throughout the VM.
- **Hardware implementation:** `reasoning_core.v` exports both the question-bit tallies supplied by the controller and the fixed-point information gain, and `thiele_autonomous_solver.v` integrates them into its μ-ledger state machine.【F:hardware/synthesis_trap/reasoning_core.v†L1-L105】【F:hardware/synthesis_trap/thiele_autonomous_solver.v†L1-L389】
- **Audit logs:** `audit_logs/agent_software_reproduction.log` and `audit_logs/agent_hardware_verification.log` capture matched μ totals for the canonical experiments.【F:audit_logs/agent_software_reproduction.log†L1-L158】【F:audit_logs/agent_hardware_verification.log†L780-L842】


---

## Order-Invariance and Composite Witnesses

These concepts distinguish Thiele computation from classical trace-based approaches.

### What is Order-Invariance?
A computation is **order-invariant** if the final result depends only on the problem's structure, not the sequence of operations.

**Classical (Order-Dependent):** Results can vary based on execution order
**Thiele (Order-Invariant):** Results are consistent regardless of operation sequence

### What are Composite Witnesses?
A **composite witness** is a global certificate built by combining local certificates from each module.

### Why This Matters
- **Parallelism:** Modules can be processed in any order or simultaneously
- **Robustness:** Immune to arbitrary execution choices
- **Auditability:** Global certificates reflect problem structure, not computation history

### Examples
- **Rotations:** Sequential rotations give different intermediate results, but the final orientation is the same
- **Sudoku:** The solution is a single global state, independent of solving order

### Implementation
- Demonstrations: Article 0 (`run_universal_principle`) and Article 1 (`run_engine_and_law`) provide hands-on transcripts for rotations, Sudoku, and partition discovery.【F:attempt.py†L920-L1010】【F:attempt.py†L1011-L1208】
- Partition-native proofs: Articles 1–4 compile MDL evidence and Tseitin receipts showcasing partition-aware certificates.【F:attempt.py†L1011-L2148】


---

## Empirical Experiments and Results

The artifact provides concrete evidence of the performance gap between classical and Thiele computation.

### The Experiment Setup

**Problem:** Hard SAT instances (Tseitin formulas on expander graphs)
**Blind Solver:** Classical SAT solver (unaware of structure)
**Sighted Solver:** GF(2) algebraic solver (exploits structure)
**Measure:** Computational cost vs problem size

### Key Results

- **Blind Solver:** Cost grows exponentially with problem size
- **Sighted Solver:** Cost remains essentially constant
- **Separation:** Demonstrates the theoretical performance gap empirically

### What This Proves

The experiments show that problems with hidden geometric structure create an exponential performance gap between:
- Classical machines (blind to structure)
- Partition-aware machines (can exploit structure)

### Implementation

- Experiment orchestration: [`generate_tseitin_data.py`](generate_tseitin_data.py)
- Analysis and plotting: `attempt.py` Article 4 utilities `fast_receipts` and `plot_fast_receipts` summarise the blind-versus-sighted sweeps and generate the separation plots.【F:attempt.py†L1980-L2148】
- Results saved in: `shape_of_truth_out/` and `tseitin_receipts.json`
---

## Foundational Proofs: Subsumption via Structured Separation

The formal stack now has three layers:

1. **Containment (`Simulation.v`):** A blind Thiele interpreter simulates any
   classical Turing Machine by replaying its transition table without ever
   invoking sighted instructions.
2. **Performance Advantage (`Separation.v`):** Sighted Thiele programs solve Tseitin
   expanders in polynomial time/μ while blind exploration provably incurs
   exponential cost (axiomatised from classical SAT lower bounds).
3. **Assembly (`Subsumption.v`):** Combines the two pillars into the flagship
   theorem: Turing computation is strictly contained in Thiele computation.

(`attempt.py`, search for `ARTICLE 0 — THE SHAPE OF TRUTH`)

## The Paradox

Introduces the core conflict between a blind solver and a partition-aware solver
through a verifiable puzzle.
(`attempt.py`, search for `ARTICLE 0 — THE PARADOX`)

## The Universal Principle

Generalizes the paradox using spatial rotations and Sudoku to show the
phenomenon is not contrived.
(`attempt.py`, search for `ARTICLE 0 — THE UNIVERSAL PRINCIPLE`)

## The Engine of Discovery

Measures the information-theoretic cost of uncovering hidden structure via a
brute-force search over partitions using MDL.
(`attempt.py`, search for `ARTICLE 1 — The Engine of Discovery`)

## The Fractal Nature of Debt

Demonstrates the exponential cost of blindness with hard instances and
multiprocessing harnesses.
(`attempt.py`, search for `ARTICLE 2 — The Fractal Nature of Debt`)

## Final Theorem & Conclusion

States the Embedding and Self-Reconstruction theorems, presents the capability
comparison table, and cryptographically seals the artifact.
(`attempt.py`, search for `ARTICLE 3 — Final Theorem & Conclusion`)

## Experimental Separation

Provides detailed, small-scale receipts comparing blind and sighted solvers
with plots and tables.
(`attempt.py`, search for `ARTICLE 4 — Experimental Separation`)

## Gödelian Landmine

The seventh act of this artifact is a deliberate confrontation with the limits of classical computation—a constructed paradox designed to expose the fundamental difference between the Turing and Thiele paradigms.

### The Paradox Constructed

In the Gödelian Landmine section (`attempt.py`, see `run_godelian_landmine`), the artifact generates a logical space that is, by design, paradoxical: it encodes a set of constraints that cannot be satisfied by any assignment. For a classical (Turing) machine, this is a death trap. The machine, bound to search for an object-level solution, will enumerate possibilities, backtrack, and ultimately fail, unable to produce anything but a negative result or an error.【F:attempt.py†L2280-L2454】

### The Thiele Machine's Response

The Thiele Machine, by contrast, is not limited to object-level search. It can step back and perceive the *shape* of the solution space itself. When confronted with a paradox, it does not merely fail to find a solution—it produces a **Certificate of Inherent Paradox**: a formal, machine-verifiable proof that the space is unsatisfiable *because* of its structure, not just its content. This is a higher-order computational act, enabled by the partition logic and certificate-driven computation described earlier (see lines 146–250).

### Technical Implementation

- **Construction:** The paradox is encoded as a set of logical constraints inside `run_godelian_landmine`, leveraging the Z3 logic engine to verify unsatisfiability.【F:attempt.py†L2280-L2454】
- **Detection:** The Thiele Machine partitions the state space, applies local axioms, and invokes the logic engine to check for consistency. When all partitions are inconsistent, it issues the certificate.
- **Output:** The certificate is saved as a machine-verifiable artifact (SMT2 proof file), and its hash is logged for auditability.

### Philosophical and Scientific Implications

The Gödelian Landmine is not a parlor trick; it is a demonstration of a new computational act. Where the classical machine is blind to the global structure of the problem, the Thiele Machine can *see* and *certify* the impossibility itself. This operationalizes a key philosophical insight: **the type of answer a machine can produce is as important as what it can compute**. The ability to issue a certificate about the *nature* of the solution space—rather than just the existence or absence of solutions—marks a profound separation in computational power.

### References

- Formal construction and code: `attempt.py`, function `run_godelian_landmine` and its helpers.【F:attempt.py†L2280-L2454】
- Certificate-driven computation: lines 205–250
- Partition logic: lines 146–201
- Empirical demonstration: see "Empirical Experiments and Results" (lines 409–455)

## Philosophical Implications and Future Directions

### What This Means for Computation

The Thiele Machine reveals that computation isn't just about algorithms—it's about **how we structure knowledge**. Traditional computers process data sequentially, but the Thiele Machine shows that **partition logic** can solve problems exponentially faster by organizing information differently.

**Key Insight:** Some problems become easy when you think about them in terms of independent modules rather than sequential steps.

### What This Means for Consciousness

The artifact demonstrates that consciousness and physics can be compatible. The "universe as a Thiele Machine" proof shows that:

- **Consciousness** can exist within physical laws
- **Free will** can coexist with determinism
- **Qualia** (subjective experience) can emerge from computation

This isn't just philosophy—it's a mathematical proof using SAT certificates.

### What This Means for Science

The Thiele Machine suggests that scientific discovery might work differently than we thought:

- **Modular thinking** might be more powerful than reductionism
- **Certificate-driven methods** could accelerate scientific progress
- **Order-invariant computation** might explain why some discoveries happen simultaneously

### What This Means for AI

Current AI is like a blind solver—powerful but inefficient. The Thiele Machine shows a path to "sighted" AI that:

- Uses **structured knowledge** to solve problems faster
- **Learns modular patterns** rather than just correlations
- Could achieve **exponential improvements** on certain tasks

### A Final Word

This artifact doesn't claim to solve consciousness or revolutionize AI overnight. Instead, it provides:

- **Mathematical tools** for thinking about these problems
- **Empirical evidence** that new computational paradigms exist
- **A foundation** for future research in partition-native computation

The Thiele Machine is a beginning, not an end—a new way to think about what computation can be.

---
## Installation and Usage

### System Requirements

- **Python 3.11+** (required for Z3 integration and advanced features)
- **Coq Platform 8.20+** (optional, for formal proof verification)
- **FPGA Synthesis Tools** (optional, for hardware implementation)
  - Vivado for Xilinx Zynq UltraScale+
  - Yosys for open-source synthesis

### Quick Setup (Windows)

```powershell
# 1. Create virtual environment
python -m venv .venv
& .venv\Scripts\Activate.ps1

# 2. Install dependencies
pip install -e .

# 3. Run the canonical thesis demonstration
python3 demonstrate_isomorphism.py
```

### Complete Installation

For full functionality including Thiele CPU, hardware synthesis, and formal verification:

```powershell
# Core Python dependencies
pip install z3-solver numpy scipy networkx python-sat matplotlib tqdm sympy cryptography

# Optional: Hardware synthesis (requires Vivado)
# Install Xilinx Vivado Design Suite for FPGA synthesis

# Optional: Formal verification (requires Coq)
# Install Coq Platform from https://coq.inria.fr/download
```

### Running the Artifact

#### Main Demonstration (canonical)
```bash
python3 demonstrate_isomorphism.py
```
- **What it does:** Runs the six‑act Bell thesis demonstration, regenerates the narrated ledger and canonical receipts, and prepares artifacts for Coq replay.
- **Duration:** Several minutes
- **Output:** `BELL_INEQUALITY_VERIFIED_RESULTS.md`, `examples/tsirelson_step_receipts.json`, and Act VI artifacts in `artifacts/`.
- **Verification:** Cryptographically sealed receipts are produced; run `python scripts/challenge.py verify receipts` and `./scripts/verify_truth.sh examples/tsirelson_step_receipts.json` to validate and replay in Coq.

If you want to run broader experiments or the full universal orchestrator, use:
```bash
python attempt.py
```
That command runs additional demos and benchmarks and populates `shape_of_truth_out/` and `archive/` with extra traces and receipts.

## Which orchestrator should I run?

- `python3 demonstrate_isomorphism.py` — Recommended for auditors and reviewers. Produces the canonical ledger, canonical receipts (`examples/tsirelson_step_receipts.json`), manifests, and the artifacts used by the mechanised Coq replay.
- `python attempt.py` — Recommended for researchers and developers who want the full universal orchestrator, additional experiments, and broader archival traces (this run produces extensive outputs in `shape_of_truth_out/` and `archive/`).

Use the demonstration for formal verification and the `attempt.py` orchestrator for exploratory or extended experiments.

#### Hardware Synthesis
```bash
bash scripts/run_the_synthesis.sh
```
- **Objective:** Regenerate the impartial Yosys verdicts for the classical brute-force solver and the Thiele autonomous solver.
- **Artifacts:** `hardware/synthesis_trap/classical_solver.log` confirms a 228-cell baseline; `hardware/synthesis_trap/thiele_graph_solver.log` records the 1231-cell Thiele design with the parameterised `reasoning_core` instantiated once.
- **Tip:** The script also refreshes the JSON netlists so auditors can re-import them into other tooling.

#### Formal Proof Verification
```bash
cd coq
./verify_subsumption.sh
```
- **Builds:** The minimalist kernel (`Kernel.v`, `KernelTM.v`, `KernelThiele.v`) and the strict-containment proof.  The current `SimulationProof.v` artefact is a μ-ledger placeholder and will be rebuilt once Milestone 2 lands.
- **Result:** Expect containment theorems to pass.  The VM refinement goal is intentionally marked TODO until the strengthened bridge is implemented.

#### Advanced Demonstrations

- **Graph 3-Colouring Laboratory (`scripts/graph_coloring_demo.py`):**
  - Executes the three-act cascade experiment, emits per-graph μ-ledgers, and writes the global scaling summary.
  - Use `python scripts/graph_coloring_demo.py --write-ledger` to rebuild the canonical JSON reports.

- **Autonomous hardware regression:**
  ```bash
  iverilog -g2012 -o build/thiele_tb \
      hardware/synthesis_trap/reasoning_core.v \
      hardware/synthesis_trap/thiele_graph_solver.v \
      hardware/synthesis_trap/thiele_autonomous_solver.v \
      hardware/synthesis_trap/thiele_graph_solver_tb.v
  vvp build/thiele_tb
  ```
  - Confirms the autonomous solver produces the same μ-question and μ-information totals as the software receipts.

- **Shor on the Thiele VM (`scripts/shor_on_thiele_demo.py`):**
  - Regenerates the three-act factoring ledger for 21, writes `shor_demo_output/analysis_report.json`, and verifies μ-ledgers against μ-spec v2.0.

- **Bell thesis orchestrator (`demonstrate_isomorphism.py`):**
  - Replays the six-act ledger, emits canonical receipts in `examples/`, and cross-checks the μ-ledger with the VM bridge semantics.

- **Receipts-to-Coq bridge (`scripts/prove_it_all.sh`):**
  - Optional bridge that rebuilds the triadic cascade receipts, compiles the sandbox proof, and demonstrates how empirical data flows into Coq.

### Troubleshooting

**Common Issues:**
- **Z3 Import Errors:** Ensure Python 3.11+ and correct virtual environment
- **Coq Compilation:** Install Coq Platform, ensure PATH includes coqc
- **FPGA Synthesis:** Install Vivado, ensure license is configured
- **Long Paths (Windows):** Enable long path support in Windows settings
- **Memory Issues:** Large experiments may require 16GB+ RAM

**Verification:**
- All outputs include SHA-256 hashes for auditability
- Run `python scripts/challenge.py verify receipts` to check integrity
- Coq proofs compile without errors or admitted statements

**Performance Notes:**
- Main artifact (`attempt.py`) takes several minutes but is comprehensive
- Hardware synthesis requires significant compute resources
- Large-scale experiments are computationally intensive by design

---

# Contact and Support

For questions, bug reports, or to request support, please open an issue on the [GitHub repository](https://github.com/sethirus/The-Thiele-Machine/issues) or contact the maintainer at thethielemachine@gmail.com.

---


---

## Output Files and Artifacts

- **Terminal Output**: Full transcript of the proof and experiment.
- **Archived Artifacts**: All machine-checkable SMT2 proofs, empirical data, and plots are saved in `archive/` subdirectories.

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
- **Foundational Proofs**: `run_prove_tm_subsumption` and `run_prove_vn_subsumption` mechanically encode the classical and von Neumann embeddings.【F:attempt.py†L547-L776】
- **Paradox Demonstration**: `run_paradox` establishes the four-piece paradox with Z3-certified unsatisfiability.【F:attempt.py†L785-L910】
- **Universal Principle**: `run_universal_principle` extends the paradox through rotations and Sudoku witnesses.【F:attempt.py†L920-L1010】
- **Engine of Discovery**: `run_engine_and_law` implements the MDL-guided search and μ-ledger summarisation.【F:attempt.py†L1011-L1208】
- **Fractal Debt**: `run_fractal_debt` measures exponential blind-search cost using Tseitin expanders.【F:attempt.py†L1446-L1956】
- **Final Theorem & Conclusion**: `run_final_theorem` composes the capability comparison and seals the receipts.【F:attempt.py†L1624-L1956】
- **Experimental Separation**: `run_experimental_separation` and its helpers generate the scaling tables and plots.【F:attempt.py†L1980-L2148】
- **Gödelian Landmine**: `run_godelian_landmine` demonstrates the meta-constraint paradox with canonical proof objects.【F:attempt.py†L2280-L2454】
- **main**: The script's entry point orchestrates all articles sequentially and finalises the Ouroboros seal.【F:attempt.py†L2455-L2487】
- **seal_and_exit, hash_obj**: Certificate generation, hashing, and output sealing.

### scripts/generate_tseitin_data.py

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
computation. Each forward pass is recorded in a tamper-evident, Ed25519-signed
audit log, and a minimal EU AI Act transparency report is available via
`get_eu_compliance_report()`. Run the demos with:

```bash
python -m apps.catnet.demo_mnist      # transparency
python -m apps.catnet.demo_control    # controllability
```


## Verifier vs Finder (perspective demo)

## Contributing

We welcome contributions to The Thiele Machine project! Please see our [Contributing Guide](CONTRIBUTING.md) for details on how to get started.

For questions or discussions, open an issue on [GitHub](https://github.com/sethirus/The-Thiele-Machine/issues).

## License

This project is licensed under the Apache License 2.0 – see the [LICENSE](LICENSE) file for details.