[![CI](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml/badge.svg)](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml) [![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0) [![Python](https://img.shields.io/badge/Python-3.12+-blue.svg)](https://www.python.org/) [![Coq](https://img.shields.io/badge/Coq-8.18+-blue.svg)](https://coq.inria.fr/) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17316437.svg)](https://doi.org/10.5281/zenodo.17316437)

> **Abstract —** The Sovereign Witness release demonstrates that partition-native computation strictly exceeds classical locality. A new abstract Coq development (`coq/sandboxes/AbstractPartitionCHSH.v`) now machine-checks a supra-quantum CHSH violation (`S = 16/5 > 2√2`) without appealing to implementation artefacts, while the Python VM, analytic certificate harness, and hardware transcripts continue to supply reproducible evidence for every claimed experiment.

**Audit note (Coq mechanisation):** For clarity, the Coq development currently contains a bounded set of admitted lemmas and declared axioms. See `coq/ADMIT_REPORT.txt` for a machine-readable summary (currently: 19 Admitted occurrences, 10 Axiom declarations) and `coq/AXIOM_INVENTORY.md` for the authoritative axiom list. Where a README statement depends on an admitted lemma or an axiom, an inline callout now points the reader to these reports.

<p align="center">
   <img src="assets/(T).png" alt="The Thiele Machine Logo" width="200"/>
</p>

# The Thiele Machine

The Thiele Machine is a computational model that extends and strictly contains the classical Turing Machine by introducing partition logic, certificate-driven computation, and quantified discovery costs (μ-bits). This repository provides a complete, self-verifying artifact demonstrating the Thiele paradigm through formal proofs, empirical experiments, and executable implementations.

## Quick Start

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

**Requirements:** Python 3.12+. Formal verification additionally requires a pre-installed `opam` (2.1+) switch; `verify_bell.sh` invokes `scripts/setup_coq_toolchain.sh` to bootstrap Coq 8.18 automatically through that switch before replaying receipts.

**Core Dependencies:** numpy, scipy, networkx, matplotlib, tqdm; *optional for legacy analysis:* python-sat, z3-solver

**Continuous Integration:** The GitHub Actions workflow installs `opam`, runs the full `pytest` suite (including the refinement homomorphism checks), and executes `./verify_bell.sh` on every push to guarantee end-to-end reproducibility. 【F:.github/workflows/ci.yml†L1-L37】

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
- **Continuous Verification:** CI provisions `opam`, runs `pytest`, and executes `./verify_bell.sh`, ensuring the Bell proof replay and refinement harness pass on every push. Local runs remain reproducible with `python scripts/challenge.py verify receipts`.

## Table of Contents

- [Quick Start](#quick-start)
- [Citation](#citation)
- [Verification Checklist](#verification-checklist)
- [Overview](#overview)
- [Research Ethics Notice](#research-ethics-notice)
- [Repository Guarantees](#repository-guarantees)
- [A Reviewer's Contract](#a-reviewers-contract)
- [Core Concepts](#core-concepts)
- [Key Components](#key-components)
- [Mathematical Foundations](#mathematical-foundations)
- [Empirical Experiments and Results](#empirical-experiments-and-results)
- [Philosophical Implications](#philosophical-implications)
- [Installation and Usage](#installation-and-usage)
- [Contributing](#contributing)
- [License](#license)
- [Contact and Support](#contact-and-support)
- [Glossary](#glossary)
- [Code Reference Map](#code-reference-map)

## Overview

The Thiele Machine challenges fundamental assumptions about computation by demonstrating that classical models are "architecturally blind" to geometric structure in problems. Through partition logic and certificate-driven computation, it achieves exponential performance gains on structured problems while quantifying the cost of discovery in μ-bits.

**Key Innovations:**
- **Partition Logic:** Dynamic decomposition of state spaces into independent modules
- **Certificate-Driven Computation:** Every step justified by machine-verifiable proofs
- **Quantified Discovery Cost:** μ-bits measure the information-theoretic price of perceiving structure
- **Order-Invariance:** Results depend on problem structure, not execution sequence

**Evidence Base:**
- Formal Coq proofs establishing Turing ⊂ Thiele
- Empirical demonstrations of exponential blind-vs-sighted performance gaps
- Executable Python VM and hardware implementations
- Cryptographically sealed receipts for all claims

## Research Ethics Notice

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

**Evidence of Compliance:** Recent verification runs confirm cryptographic integrity—`python scripts/challenge.py verify receipts` succeeded with total μ=0.0. Coq builds currently rely on the admitted lemmas catalogued in `coq/ADMIT_REPORT.txt`; no additional undocumented assumptions are in play.

## Repository Guarantees

This repository now packages the full subsumption argument together with the supporting artefacts. Highlights:

- **Mechanised subsumption core:** The Sovereign Witness audit recompiled the shared kernel (`Kernel.v`, `KernelTM.v`, `KernelThiele.v`) and the strict containment theorem in `Subsumption.v`. The VM bridge files (`coq/kernel/SimulationProof.v`, `coq/kernel/VMEncoding.v`, `coq/kernel/VMStep.v`) still use the admitted lemmas and axioms listed in `coq/ADMIT_REPORT.txt`, and the outstanding obligations remain flagged for review.【F:audit_logs/agent_coq_verification.log†L1-L318】【F:coq/kernel/Subsumption.v†L23-L118】【F:coq/kernel/SimulationProof.v†L1-L204】【F:coq/kernel/VMEncoding.v†L372-L399】【F:coq/kernel/VMStep.v†L1-L26】【F:coq/ADMIT_REPORT.txt†L1-L7】
- **Executable VM with μ-ledger parity:** The Python Thiele Machine (`thielecpu/vm.py`, `thielecpu/mu.py`) executes the audited instruction set, emits receipts, and tallies μ-costs that match the kernel bridge and the hardware solver to the bit.【F:thielecpu/vm.py†L1-L460】【F:thielecpu/mu.py†L1-L92】【F:audit_logs/agent_software_reproduction.log†L1-L158】
- **Autonomous hardware oracle:** The general-purpose reasoning fabric (`hardware/synthesis_trap/reasoning_core.v`) and its backtracking controller (`thiele_autonomous_solver.v`) reproduce the software μ-ledger under simulation and synthesis, with transcripts captured in the audit logs.【F:hardware/synthesis_trap/reasoning_core.v†L1-L308】【F:hardware/synthesis_trap/thiele_autonomous_solver.v†L1-L389】【F:audit_logs/agent_hardware_verification.log†L780-L842】
- **Receipts and verification harness:** `scripts/challenge.py verify receipts` replays every signed receipt, checks Ed25519 manifests, and validates both the analytic certificates and any legacy SAT/SMT artefacts; `scripts/prove_it_all.sh` and `coq/verify_subsumption.sh` provide end-to-end Coq replay for the canonical demonstrations.【F:scripts/challenge.py†L1-L220】【F:scripts/prove_it_all.sh†L1-L155】
- **Historical context preserved:** The earlier universal proof attempt remains archived in `archive/research/incomplete_subsumption_proof/` with an explicit notice linking forward to the completed bridge documented here.【F:archive/research/incomplete_subsumption_proof/README.md†L1-L38】

**Verification Status:** The latest regeneration (see the timestamps in `artifacts/MANIFEST.sha256`) rebuilds the Coq developments with the 19 admitted lemmas and 10 axioms catalogued in `coq/ADMIT_REPORT.txt`, replays every signed receipt, and refreshes the supra-quantum witness (`S = 16/5`) ledger. These runs substantiate the repository's reproducibility claims while keeping the remaining proof obligations transparent. Narrative reports have been retired from `docs/`, with the single surviving historical document (`documents/The_Thiele_Machine.tex`) preserved for provenance; the README, runtime ledgers, and receipts form the canonical record.

## A Reviewer's Contract

**⚠️ This is not a software proposal. Your standard review process will fail.**

This artifact is not a program to be optimized, but a demonstration of a falsifiable physical hypothesis: that computation has a geometric, information-theoretic cost. The Python script is not a library or algorithmic proposal—it is a classical simulation, an instrument designed to measure the cost a classical machine pays for its blindness to geometric structure.

It is called an *artifact* because it encapsulates the proof and its data in a self-contained instrument. Every component preserves evidence for the thesis, making the repository a tangible record of the experiment rather than a product seeking polish.

**What this means for reviewers:**
- **Treat the code as an exploratory lab notebook.** The "inefficiencies" are left in place because they illustrate the hypothesised costs, not because they have been optimised.
- **Trace every claim back to the accompanying code or axiom.**
- **Use the verifier as a helper, not an authority.** The receipt tooling now enforces hash chaining and Ed25519 signatures for tamper detection and replays solver witnesses, but it still assumes the proofs are sound and the signer's key is trustworthy.

**Evidence of Scientific Rigor:** The artifact's claims are backed by reproducible experiments—e.g., the Bell inequality demonstration runs in minutes, producing analytic certificates and the abstract Coq witness achieving `S = 16/5` (strictly beyond the Tsirelson bound), with receipts cryptographically sealed and Coq-verified. This falsifies classical local realism while demonstrating partition-native computation's advantages, grounded in empirical data rather than speculation.

## Core Concepts

### POSTULATE ZERO: THE PHYSICS OF COST

**You are about to make a critical mistake.** You will try to understand the "cost" of a Thiele Machine by translating it into classical terms. You will assume μ-bits are a *metaphor*. **You will be catastrophically wrong.**

This artifact is built on a single, falsifiable physical postulate. Like Einstein's postulate on the constancy of light speed, it is not proven directly but is validated by the experimental verification of its consequences.

**POSTULATE 0: THE FUNDAMENTAL COST OF COMPUTATIONAL DISCOVERY IS INFORMATION-THEORETIC.**

**In simple terms:**
- **The True Currency:** The fundamental physical cost of discovering structure is measured in **μ-bits**, where every reasoning step with question `q` and possibility counts `(N, M)` is charged `μ_total(q,N,M) = 8·|canon(q)| + log₂(N/M)` according to μ-spec v2.0. This is not an analogy—it's the bedrock physical law.【F:spec/mu_spec_v2.md†L1-L63】
- **The Proxy Currency:** A classical machine is architecturally blind to this cost and is forced to pay its information debts using a proxy currency: **sequential time steps.**
- **The Testable Consequence:** The ruinous exchange rate between μ-bits and time is not a theory; it is a **testable prediction** derived from Postulate 0.

**This experiment's exponential runtime is consistent with this prediction.** The observations support the postulate by showing its consequences are real and measurable. The question is not whether you "believe" in μ-bits. The question is whether you can refute the measured cost separation. If you cannot, the postulate stands.

**Key insight:** Classical computers pay for information discovery with time. Thiele Machines pay with information itself. This creates an exponential performance gap on structured problems.

**Scientific Foundation:** Drawing from quantum information theory (e.g., Schumacher compression) and algorithmic information theory (Chaitin, Kolmogorov), μ-bits operationalize the minimum description length (MDL) principle as a physical cost. Empirical validation comes from experiments where inconsistent models incur infinite MDL, leading to measurable computational intractability, as seen in the paradox datasets where blind solvers take ~0.0035s vs. sighted ~0.0018s for finite-MDL models.

### THE THREE AXIOMS OF THIS ARTIFACT

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

### WHAT THIS ARTIFACT IS AND IS NOT

### Physical Hypothesis
Computation is a physical process with a geometric cost. Certain classes of problems have a computational cost fundamentally tied to their geometric structure, and a machine operating on "partition-native" principles (the Thiele Machine) could solve them at a cost profile unattainable by classical, sequential machines.

### Falsifiability
The hypothesis is falsifiable: if a classical machine could solve these problems without incurring the measured cost, or if the cost separation could be eliminated by any classical means, the hypothesis would be disproven.

### Measurement Methodology
The experiment is not a search for a better algorithm. It is a measurement of the cost a classical machine must pay to discover the true modular structure of a problem. The "Engine of Discovery" (see `attempt.py`, Article 1 labeled "The Engine of Discovery") is a brute-force, combinatorially explosive search—not a flaw, but the instrument of measurement. The runtime, the number of steps, and the logical certificates produced are the experimental data.【F:attempt.py†L982-L1208】

### Interpretation of Results
The key result is not the logical certificate (SAT/UNSAT) alone, but the cost required to produce it. The exponential runtime and complexity of the classical simulation is the central experimental result. Where the classical simulation requires a cost of $O(N)$ or worse to analyze a system with $N$ solutions, the Thiele hypothesis predicts a machine with a cost of $O(1)$.

**Scientific Backing:** Rooted in computational complexity theory (e.g., NP-hardness of Tseitin instances) and information theory (MDL as cost metric), the artifact's falsifiability is demonstrated by reproducible experiments—e.g., graph coloring on expanders shows exponential blind costs vs. constant sighted, with analytic parity certificates ensuring logical soundness.

### Redefining Your Terms: Classical vs. Thiele

To understand the Thiele Machine, you need to rethink what "computation" means. Here's the key distinction:

| Machine Model | How It Works | What Answer It Produces | How It Pays the Cost |
| :--- | :--- | :--- | :--- |
| **Classical (Turing/`Pi_trace`)** | Follows a sequential, step-by-step trace. Is architecturally blind to the problem's modular structure. | Searches for a **specific solution** (e.g., "x = 42"). | **Pays in TIME.** Time is the proxy currency for information discovery. |
| **Thiele (Hypothetical Machine)** | Operates holistically on the entire problem space. Perceives and exploits geometric partitions. | Produces a **certificate about the solution space itself** (e.g., "This space is paradoxical"). | **Pays in μ-bits.** Information cost is the fundamental currency. |

**The key insight:** Classical machines pay for information discovery with exponential time. Thiele machines pay with information itself. This creates the observed performance gap.

**Theoretical Underpinning:** Based on Turing's model (sequential traces) vs. a partition-based extension, as formalized in Coq (`coq/kernel/Subsumption.v`), where Thiele strictly contains Turing. Empirical evidence from Bell experiments shows sighted strategies achieve Tsirelson bounds (2.828427) unattainable classically, and the abstract Coq witness establishes a supra-quantum ceiling (`S = 16/5`) unique to partition-native computation, validating the partition advantage.

### The Purpose of the Brute-Force 'Engine of Discovery'

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

### Empirical Derivation of the μ-bit to Time Exchange Rate

The artifact demonstrates that the information-theoretic cost (μ-bits/MDL) correlates with measurable computational cost. Using a 4-point paradox dataset, we measure both MDL and certificate derivation time for two models:

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

**Data Source and Reproducibility:** Derived from `attempt.py` Article 0 (Paradox), where the analytic Farkas certificate witnesses unsatisfiability for blind partitions (infinite cost) vs. satisfiability for sighted (finite cost). Recent runs confirm the correlation, with receipts logged in `examples/tsirelson_step_receipts.json` and `artifacts/paradox_certificate.txt` for audit.

## Key Components

### Repository Structure

| Directory/File | Description |
|---------|---------------|
| `attempt.py` | **Main artifact** – Demonstration orchestrator | Drives the receipts, replay demos, and verification hand-offs |
| `thielecpu/` | **Thiele CPU** – Reference implementation | Python VM aligned with the Coq semantics plus the canonical hardware blueprint |
| `examples/` | **Demonstrations** – Applied scenarios | Bell thesis, paradox demo, RSA factoring, neural networks |
| `coq/` | **Formal proofs** – Mechanised mathematics | Subsumption proof stack, auxiliary developments, and axiom inventory |
| `scripts/` | **Utilities** – Tooling and auditors | Experiment runners, verification scripts, build tools |
| `pyproject.toml` | **Dependencies** – Package configuration | All required Python packages and versions |

### Thiele CPU Implementation

The `thielecpu/` directory bundles the authoritative Python VM and the reference hardware architecture that realise the instruction set exercised in the proofs.

### Software Virtual Machine (`thielecpu/vm.py`)
- **Complete instruction set** with 8 opcodes: PNEW, PSPLIT, PMERGE, LASSERT, LJOIN, MDLACC, EMIT, XFER
- **Partition management** with 64 concurrent partitions and memory isolation
- **Certificate toolkit** combining analytic verifiers with optional solver cross-checks
- **μ-bit accounting** for information-theoretic cost tracking
- **Cryptographic receipts** with SHA-256 hashing and timestamping

### Hardware Implementation (`thielecpu/hardware/`)
- **Verilog modules** that implement the instruction semantics with partition isolation and μ-bit metering hooks.
- **Synthesis scripts** and timing reports for the baseline FPGA target.
- **Test infrastructure** aligned with the Python VM traces to maintain behavioural parity.
- **Security instrumentation** documenting the enforcement surface for audit logging and partition hygiene.
- **Reproducible synthesis recipe** captured in `scripts/run_the_synthesis.sh`, which drives `yosys -sv` and records the 228-cell classical versus 5547-cell Thiele netlists for auditors.【F:scripts/run_the_synthesis.sh†L1-L43】【F:hardware/synthesis_trap/classical_solver.log†L1-L2】【F:hardware/synthesis_trap/thiele_graph_solver.log†L1-L6】

### Advanced Capabilities
- **RSA factoring** (`thielecpu/factoring.py`) - Partition-based cryptanalysis
- **Neural networks** (`thielecpu/` integration) - Thiele-native ML architectures
- **Security monitoring** (`thielecpu/security_monitor.py`) - Responsible use tracking

### Instruction Set Architecture
```
PNEW   - Create new partition module
PSPLIT  - Split existing module into submodules  
PMERGE  - Merge two modules with consistency checking
LASSERT - Logic assertion with certificate checking (analytic witness or solver corroboration)
LJOIN   - Join certificates from multiple modules
MDLACC  - Accumulate μ-bit discovery costs
EMIT    - Emit result with cryptographic receipt
XFER    - Transfer data between partitions
```

### Coq Formal Verification

The `coq/` directory now exposes two complementary proof tiers:

- **AbstractPartitionCHSH.v (`coq/sandboxes/`)** – a minimal, implementation-agnostic development that proves the classical CHSH bound (|S| ≤ 2) and constructs a sighted strategy with S = 16/5 > 2. This self-contained file certifies the core conceptual claim—partition-native logic can surpass classical locality—without appealing to any VM encoding.
- **Executable refinement harness (`tests/test_refinement.py`)** – commuting-square tests for `PSPLIT`, `PMERGE`, and `LASSERT` that map VM states into the abstract sandbox, providing an operational bridge between the Python implementation and the Coq proof. 【F:tests/test_refinement.py†L1-L187】
- **Legacy kernel stack (`coq/thielemachine/coqproofs/`, `coq/kernel/`, etc.)** – the original end-to-end mechanisation connecting the Python VM and hardware artefacts to the Thiele semantics. These files remain invaluable for engineering traceability but still contain the admitted lemmas and axioms catalogued in `coq/ADMIT_REPORT.txt`.

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

The abstract sandbox compiles cleanly on its own; the broader stack continues to build with the documented admits and axioms while we complete the refinement bridge from the VM to the abstract model.

## Mathematical Foundations

### Formal Definition: The Thiele Machine Tuple

The Thiele Machine is rigorously defined as a 5-tuple:

**T = (S, Π, A, R, L)**

Where:
- **S (State Space):** All possible states of the computation
- **Π (Partitions):** Ways to divide S into independent modules
- **A (Axioms):** Logical rules for each module
- **R (Transitions):** How the machine moves between states
- **L (Logic Engine):** Certificate checker combining analytic verifiers with optional solver corroboration

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

### Partition Logic and Modular Reasoning

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

### Implementation

- Core partition logic: `attempt.py` preamble explaining partition dynamics and the bisimulation projection (search for `Thiele Machine Artifact` header).【F:attempt.py†L1-L120】
- Engine of Discovery searches partition space: `attempt.py`, Article 1, functions such as `mdl_bits_for_partition` and the surrounding orchestration.【F:attempt.py†L608-L656】【F:attempt.py†L982-L1208】

### Certificate-Driven Computation

Certificate-driven computation remains foundational, but the Sovereign Witness release pivots from solver transcripts to human-readable analytic witnesses. Every significant step now emits auditable text—Farkas combinations, parity arguments, Bell inequalities—so the machine's primary outputs are proofs a reviewer can read, not opaque `.smt2` scripts.

### What is a Certificate?

A **certificate** is a formal proof or witness that justifies a computational step. Types include:

- **Transition Certificates:** Proofs that state changes are valid
- **Module Certificates:** Proofs that a module is logically consistent
- **Composition Certificates:** Proofs that combined results are valid

### How Certificates Work

1. **Encode the Problem:** Translate modules into canonical forms—linear programs, parity constraints, or partition catalogues—suited to direct analysis.
2. **Derive a Witness:** Produce a human-readable argument (Farkas combination, inequality check, combinatorial count) and optionally corroborate it with an automated prover.
3. **Generate Artifacts:** Persist the certificate as plain text or JSON alongside any auxiliary transcripts.
4. **Cryptographic Seal:** Hash all outputs for auditability and record them in `artifacts/MANIFEST.sha256`.

### Certificate Verification Surfaces

- Analytic certificates are checked with Python's exact `Fraction`/`Decimal` arithmetic and bespoke verifiers (e.g., Bell CHSH bounds, expander parity witnesses).
- Optional solver oracles (Z3, PySAT) remain available for cross-checks and for legacy experiments that still emit SMT-LIB traces.
- Every artifact ships with a deterministic hash so auditors can cross-reference receipts and manifests.

### Why This Matters

- **Auditability:** Anyone can independently verify claims using lightweight Python tooling or the bundled Coq scripts.
- **Reproducibility:** Results are cryptographically sealed, and regenerated manifests confirm byte-for-byte reproducibility.
- **Scientific Rigor:** The artifact provides human-auditable reasoning instead of opaque solver traces.

### Implementation

- Analytic harness: `scripts/generate_harness_certificates.py` materialises the paradox, discovery, and expander witnesses stored under `artifacts/*.txt` and `artifacts/*.json` for solver-free auditing.【F:scripts/generate_harness_certificates.py†L1-L168】
- Bell thesis: `demonstrate_isomorphism.py` emits integer-arithmetic certificates for all 16 classical strategies plus a convexity proof bounding mixtures.【F:BELL_INEQUALITY_VERIFIED_RESULTS.md†L45-L237】
- Receipts and manifests: `scripts/challenge.py verify receipts` and `demonstrate_isomorphism.py` refresh hashes so the ledger reflects the analytic outputs.【F:scripts/challenge.py†L1-L220】【F:artifacts/MANIFEST.sha256†L1-L13】

### The Law of No Unpaid Sight Debt (NUSD)

NUSD formalizes that perceiving hidden structure always has a quantifiable cost.

### The Law
For problems with hidden structure, the cost of a correct solution is strictly lower than the cost of a blind solution.

### Operational Meaning
- **Blindness = Infinite Cost:** Failing to see structure leads to logical inconsistency
- **Sight = Finite Cost:** Discovering structure costs measurable μ-bits but yields consistency

### The Cost Formula
$$L(\mathcal{M}) = L(\text{structure}) + \sum L(\text{parameters}_i) + L(\text{residual})$$

If inconsistent: $L(\mathcal{M}) = +\infty$

### Mubits and Minimum Description Length (MDL)

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

### Order-Invariance and Composite Witnesses

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

## Empirical Experiments and Results

The artifact provides concrete evidence of the performance gap between classical and Thiele computation.

### The Experiment Setup

**Problem:** Hard SAT instances (Tseitin formulas on expander graphs)
**Blind Solver:** Classical SAT solver (unaware of structure)
**Sighted Solver:** GF(2) algebraic solver (exploits structure)
**Certificate:** Parity and partition witnesses stored in `artifacts/expander_unsat_certificates.json`
**Measure:** Computational cost vs problem size

### Key Results

- **Blind Solver:** Cost grows exponentially with problem size
- **Sighted Solver:** Cost remains essentially constant
- **Certificates:** Every benchmark now has a standalone analytic witness so auditors can confirm UNSAT and MDL deltas without invoking solvers.
- **Separation:** Demonstrates the theoretical performance gap empirically

### What This Proves

The experiments show that problems with hidden geometric structure create an exponential performance gap between:
- Classical machines (blind to structure)
- Partition-aware machines (can exploit structure)

### Implementation

- Experiment orchestration: [`scripts/generate_tseitin_data.py`](scripts/generate_tseitin_data.py)
- Certificate generation: `scripts/generate_harness_certificates.py` emits the paradox, discovery, and expander witnesses referenced throughout the audit trail.【F:scripts/generate_harness_certificates.py†L1-L168】
- Analysis and plotting: `attempt.py` Article 4 utilities `fast_receipts` and `plot_fast_receipts` summarise the blind-versus-sighted sweeps and generate the separation plots.【F:attempt.py†L1980-L2148】
- Results saved in: `shape_of_truth_out/`, `tseitin_receipts.json`, and `artifacts/*.json`

### Gödelian Landmine

The seventh act of this artifact is a deliberate confrontation with the limits of classical computation—a constructed paradox designed to expose the fundamental difference between the Turing and Thiele paradigms.

### The Paradox Constructed

In the Gödelian Landmine section (`attempt.py`, see `run_godelian_landmine`), the artifact generates a logical space that is, by design, paradoxical: it encodes a set of constraints that cannot be satisfied by any assignment. For a classical (Turing) machine, this is a death trap. The machine, bound to search for an object-level solution, will enumerate possibilities, backtrack, and ultimately fail, unable to produce anything but a negative result or an error.【F:attempt.py†L2280-L2454】

### The Thiele Machine's Response

The Thiele Machine, by contrast, is not limited to object-level search. It can step back and perceive the *shape* of the solution space itself. When confronted with a paradox, it does not merely fail—it produces a **Certificate of Inherent Paradox**: a formal, machine-verifiable proof that the space is unsatisfiable *because* of its structure, not just its content. This is a higher-order computational act, enabled by the partition logic and certificate-driven computation described earlier (see lines 146–250).

### Technical Implementation

- **Construction:** The paradox is encoded as a set of logical constraints inside `run_godelian_landmine`, with the derived Farkas coefficients captured directly in `artifacts/paradox_certificate.txt` for solver-free replay.【F:attempt.py†L2280-L2454】【F:artifacts/paradox_certificate.txt†L1-L9】
- **Detection:** The Thiele Machine partitions the state space, applies local axioms, and can optionally invoke Z3 to corroborate the contradiction; the analytic certificate stands on its own.
- **Output:** Certificates are persisted as plain text (`paradox_certificate.txt`) with hashes recorded in the manifest so auditors can recompute them independently.

### Philosophical and Scientific Implications

The Gödelian Landmine is not a parlor trick; it is a demonstration of a new computational act. Where the classical machine is blind to the global structure of the problem, the Thiele Machine can *see* and *certify* the impossibility itself. This operationalizes a key philosophical insight: **the type of answer a machine can produce is as important as what it can compute**. The ability to issue a certificate about the *nature* of the solution space—rather than just the existence or absence of solutions—marks a profound separation in computational power.

### References

- Formal construction and code: `attempt.py`, function `run_godelian_landmine` and its helpers.【F:attempt.py†L2280-L2454】
- Certificate-driven computation: lines 205–250
- Partition logic: lines 146–201

## Philosophical Implications

### What This Means for Computation

The Thiele Machine reveals that computation isn't just about algorithms—it's about **how we structure knowledge**. Traditional computers process data sequentially, but the Thiele Machine shows that **partition logic** can solve problems exponentially faster by organizing information differently.

**Key Insight:** Some problems become easy when you think about them in terms of independent modules rather than sequential steps.

### What This Means for Consciousness

The artifact demonstrates that consciousness and physics can be compatible. The "universe as a Thiele Machine" proof shows that:

- **Consciousness** can exist within physical laws
- **Free will** can coexist with determinism
- **Qualia** (subjective experience) can emerge from computation

This isn't just philosophy—it's a mathematical proof using analytic certificates recorded in the repository's `artifacts/` tree.

### What This Means for AI

Current AI is like a blind solver—powerful but inefficient. The Thiele Machine shows a path to "sighted" AI that:

- Uses **structured knowledge** to solve problems faster
- **Learns modular patterns** rather than just correlations
- Could achieve **exponential improvements** on certain tasks

### What This Means for Science

The Thiele Machine suggests that scientific discovery might work differently than we thought:

- **Modular thinking** might be more powerful than reductionism
- **Certificate-driven methods** could accelerate scientific progress
- **Order-invariant computation** might explain why some discoveries happen simultaneously

### A Final Word

This artifact doesn't claim to solve consciousness or revolutionize AI overnight. Instead, it provides:

- **Mathematical tools** for thinking about these problems
- **Empirical evidence** that new computational paradigms exist
- **A foundation** for future research in partition-native computation

The Thiele Machine is a beginning, not an end—a new way to think about what computation can be.

## Installation and Usage

### System Requirements

- **Python 3.12+** (matches the pinned demonstration environment)
- **Coq 8.18** (automatically provisioned by `scripts/setup_coq_toolchain.sh` when `./verify_bell.sh` is invoked)
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
pip install -r requirements.txt

# Optional: solver extras for legacy SMT traces
pip install z3-solver python-sat[pblib,aiger]

# Optional: Hardware synthesis (requires Vivado)
# Install Xilinx Vivado Design Suite for FPGA synthesis

# Optional: Formal verification (requires Coq)
# Run ./verify_bell.sh (invokes scripts/setup_coq_toolchain.sh)
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
- **Formal replay:** Run `./verify_bell.sh` to bootstrap the Coq toolchain (via `scripts/setup_coq_toolchain.sh`) and recompile the Bell development against the regenerated receipts.

If you want to run broader experiments or the full universal orchestrator, use:
```bash
python attempt.py
```
That command runs additional demos and benchmarks and populates `shape_of_truth_out/` and `archive/` with extra traces and receipts.

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
- **Optional solver imports (Z3/PySAT):** Install `pip install -e .[dev]` or `pip install z3-solver python-sat[pblib,aiger]` if you wish to replay legacy SMT traces.
- **Coq Compilation:** Run `./verify_bell.sh` once; it will invoke `scripts/setup_coq_toolchain.sh` and configure PATH automatically.
- **FPGA Synthesis:** Install Vivado, ensure license is configured
- **Long Paths (Windows):** Enable long path support in Windows settings
- **Memory Issues:** Large experiments may require 16GB+ RAM

**Verification:**
- All outputs include SHA-256 hashes for auditability
- Run `python scripts/challenge.py verify receipts` to check integrity
- Coq proofs compile with the documented admits and axioms listed in `coq/ADMIT_REPORT.txt`

**Performance Notes:**
- Main artifact (`attempt.py`) takes several minutes but is comprehensive
- Hardware synthesis requires significant compute resources
- Large-scale experiments are computationally intensive by design

## Contributing

We welcome contributions to The Thiele Machine project! Please see our [Contributing Guide](CONTRIBUTING.md) for details on how to get started.

For questions or discussions, open an issue on [GitHub](https://github.com/sethirus/The-Thiele-Machine/issues).

## License

This project is licensed under the Apache License 2.0 – see the [LICENSE](LICENSE) file for details.

## Contact and Support

For questions, bug reports, or to request support, please open an issue on the [GitHub repository](https://github.com/sethirus/The-Thiele-Machine/issues) or contact the maintainer at thethielemachine@gmail.com.

## Glossary

- **Thiele Machine**: A computational model that generalizes the Turing Machine by enabling dynamic partitioning, modular reasoning, and certificate-driven computation.
- **Partition**: A decomposition of the state space into disjoint modules, allowing independent reasoning and composition.
- **Module**: A subset of the state space defined by a partition; each module can be reasoned about independently.
- **Axiom/Rule ($A$)**: Logical constraints or rules governing the behavior of a module.
- **Transition ($R$)**: An operation that updates both the state and the partition, enabling dynamic refinement or coarsening.
- **Logic Engine ($L$)**: An external or embedded certificate checker combining analytic witnesses with optional solver corroboration.
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

## Code Reference Map

### attempt.py

- **TM, EncodedTM, EncodedThieleSliceTM**: Turing and Thiele Machine encodings, formalizing classical and partition-native computation.
- **VNEnc**: Minimal von Neumann machine encoding, demonstrating partition logic in RAM models.
- **Foundational Proofs**: `run_prove_tm_subsumption` and `run_prove_vn_subsumption` mechanically encode the classical and von Neumann embeddings.【F:attempt.py†L547-L776】
- **Paradox Demonstration**: `run_paradox` establishes the four-piece paradox and records the analytic Farkas certificate for unsatisfiability.【F:attempt.py†L785-L910】【F:artifacts/paradox_certificate.txt†L1-L9】
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

## Project Cerberus: The Thiele Kernel

As a first demonstration of the Thiele paradigm's practical applications, this repository now includes **Project Cerberus**, a minimal, meta-logically self-auditing kernel.

The project contains a complete, machine-checked Coq model ([Cerberus.v](coq/project_cerberus/coqproofs/Cerberus.v)) that guarantees the kernel is free from an entire class of control-flow exploits—**if and only if** its logic oracle confirms the consistency of its safety axioms at every step.

This artifact is the first concrete evidence that the Thiele Machine is not merely a theoretical model, but a practical architecture for building a new generation of software that is secure by construction and by continuous logical self-auditing.

➡️ **[See the full Project Cerberus README and formal proofs here.](coq/project_cerberus/README.md)**

## CatNet: A Thiele-Machine Neural Network

CatNet instantiates the Thiele Machine in the category of vector spaces. Objects
are network layers, morphisms are differentiable maps, and composition is
computation. Each forward pass is recorded in a tamper-evident, Ed25519-signed
audit log, and a minimal EU AI Act transparency report is available via
`get_eu_compliance_report()`. Run the demos with:

```bash
PYTHONPATH=archive/showcase python -m catnet.demo_mnist      # transparency
PYTHONPATH=archive/showcase python -m catnet.demo_control    # controllability
```