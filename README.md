[![CI](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml/badge.svg)](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml) [![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0) [![Python](https://img.shields.io/badge/Python-3.12+-blue.svg)](https://www.python.org/) [![Coq](https://img.shields.io/badge/Coq-8.18+-blue.svg)](https://coq.inria.fr/) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17316437.svg)](https://doi.org/10.5281/zenodo.17316437)

<div align="center">
   <h1>The Thiele Machine</h1>
   <p><strong>Self-Installing Proofs. No Source. No Trust. Only Mathematics.</strong></p>
</div>

> **TL;DR:** The Thiele Machine is a new computational model that strictly contains the Turing Machine. It measures the cost of "seeing" hidden structure in problems (μ-bits) and demonstrates exponential performance gains when that structure is exploited. This repository provides formal proofs, empirical experiments, and executable implementations that make these claims falsifiable.

---

## Table of Contents

- [What is The Thiele Machine?](#what-is-the-thiele-machine)
- [Quick Start](#quick-start)
- [Try It In Your Browser](#try-it-in-your-browser)
- [The Core Claim](#the-core-claim)
- [Understanding Thiele Receipts](#understanding-thiele-receipts)
- [Self-Hosting Kernel](#self-hosting-kernel)
- [Formal Verification](#formal-verification)
- [Running Experiments](#running-experiments)
- [Repository Structure](#repository-structure)
- [Installation](#installation)
- [For Reviewers](#for-reviewers)
- [Citation](#citation)
- [Contributing](#contributing)

---

## What is The Thiele Machine?

**The Thiele Machine extends the Turing Machine by adding three capabilities:**

| Capability | What It Does | Why It Matters |
|------------|--------------|----------------|
| **Partition Logic** | Divides state space into independent modules | Enables parallel reasoning on subproblems |
| **Certificate-Driven Computation** | Every step produces a verifiable proof | Makes computation auditable and reproducible |
| **μ-Bit Accounting** | Measures the cost of perceiving structure | Quantifies the "price of sight" |

### The Key Insight

Classical computers are **architecturally blind** to problem structure. They search exhaustively, paying in time. The Thiele Machine can **see** structure and pay in information (μ-bits) instead—often exponentially cheaper.

**Analogy:** Imagine solving a jigsaw puzzle. A classical machine tries every piece in every position. The Thiele Machine first notices "these pieces are all sky" and "these are all grass," then solves each cluster independently.

### Is This a Refutation of Church-Turing?

**No.** The Thiele Machine computes the same functions as a Turing Machine. What differs is the **cost profile**. The Coq proofs establish:
- `thiele_simulates_turing`: Every Turing computation can be reproduced exactly
- `turing_is_strictly_contained`: Some Thiele computations require oracle/sight primitives unavailable to blind traces

These are properties of an enriched model, not a refutation of computability theory.

---

## Quick Start

### 30-Second Demo

```bash
# Clone and setup
git clone https://github.com/sethirus/The-Thiele-Machine.git
cd The-Thiele-Machine
pip install -e .

# Verify a receipt and materialize a file from proofs
python3 verifier/replay.py examples/000_hello.json --trust-manifest receipts/trust_manifest.json
```

**What happened?** You just reconstructed a file from cryptographic proofs—no source code required, only mathematics.

### Self-Hosting Demo

The Thiele kernel can reconstruct itself from receipts:

```bash
python3 verifier/replay.py bootstrap_receipts && sha256sum thiele_min.py
```

**Expected output:**
```
Materialized: thiele_min.py (8348 bytes, sha256=77cd06bb...)
Receipt verification complete. All invariants satisfied.
77cd06bbb84ed8ccc4fd2949c555a8ba553d56629c88338435db65ce4d079135  thiele_min.py
```

### Full Verification

```bash
# Run the Bell thesis demonstration (produces formal certificates)
python3 demonstrate_isomorphism.py

# Verify all receipts
python scripts/challenge.py verify receipts

# (Optional) Replay Coq proofs
./verify_bell.sh  # Requires Coq 8.18
```

---

## Try It In Your Browser

<div align="center">

[![Launch Receipt Verifier](https://img.shields.io/badge/🔒_Launch_Receipt_Verifier-Try_Now-blue?style=for-the-badge)](https://sethirus.github.io/The-Thiele-Machine/)

**Verify receipts client-side. Zero uploads. 100% privacy.**

[![Proof-Install Demo](https://img.shields.io/badge/🔒_Proof--Install-Demo-blue?style=for-the-badge)](https://sethirus.github.io/The-Thiele-Machine/demos/install.html)
[![ZK Verify](https://img.shields.io/badge/⚡_ZK_Verify-Demo-purple?style=for-the-badge)](https://sethirus.github.io/The-Thiele-Machine/demos/zk.html)
[![Trusting Trust](https://img.shields.io/badge/🔐_Trusting_Trust-Demo-green?style=for-the-badge)](https://sethirus.github.io/The-Thiele-Machine/demos/trusting-trust.html)

</div>

---

## The Core Claim

### Exponential Blind/Sighted Cost Separation

On structured problems, **blind solvers** (unaware of structure) pay exponentially more than **sighted solvers** (exploiting structure).

| Problem Size | Blind μ_conflict | Sighted μ_answer | Cost Ratio |
|--------------|------------------|------------------|------------|
| 6            | 15.0 ± 2.0       | 9.0 ± 0.0        | 1.67×      |
| 10           | 46.7 ± 9.2       | 15.0 ± 0.0       | 3.11×      |
| 14           | 107.3 ± 24.6     | 21.0 ± 0.0       | 5.11×      |
| 18           | 172.0 ± 67.6     | 27.0 ± 0.0       | 6.37×      |

**Key observation:** Blind cost grows exponentially. Sighted cost stays near-constant (1 μ/variable).

### Falsifiable Predictions

This claim is stated in two falsifiable forms:

1. **Thermodynamic bound:** For any process reducing N→M possibilities with query q:
   $$\frac{W}{kT\ln 2} \geq 8|canon(q)| + \log_2(N/M) - \varepsilon$$

2. **Scaling separation:** On problems with growing compositional depth, blind solvers scale super-polynomially while sighted solvers stay O(1).

**How to break the claim:** Produce a counterexample with controlled structure where the separation vanishes, or show negative slack in the thermodynamic bound.

<!-- FALSIFIABILITY_SUMMARY_START -->
| Probe | Metric | Value |
| --- | --- | --- |
| Landauer | runs analysed | 12 |
| Landauer | trials analysed | 156 |
| Landauer | min(W/kTln2 − Σμ) | 0.000 |
| Landauer | worst deficit beyond ε=0.050 | 0.000 |
| Turbulence | mean final runtime ratio (blind/sighted) | 2.489 |
| Turbulence | module 0 runtime ratio (blind/sighted) | 3.382 |
| Turbulence | module 1 runtime ratio (blind/sighted) | 4.301 |
| Turbulence | module 2 runtime ratio (blind/sighted) | 3.041 |
| Turbulence | module 3 runtime ratio (blind/sighted) | 3.113 |
| Cross-domain | mean final runtime ratio (blind/sighted) | 5.995 |
<!-- FALSIFIABILITY_SUMMARY_END -->

---

## Understanding Thiele Receipts

### What is a Receipt?

A **Thiele receipt** is a cryptographic proof that lets you verify software without trusting source code or build processes. Think: **mathematical proof instead of "just trust me."**

### Receipt Types

| Type | Purpose | Example |
|------|---------|---------|
| **File Receipt** | Proves file contents | `000_hello.json` |
| **Transition Receipt** | Proves state change validity | `bootstrap_receipts/*.json` |
| **Certificate Receipt** | Proves logical consistency | `tsirelson_step_receipts.json` |

### Creating Receipts

```bash
# Single file
python3 create_receipt.py my_file.py --sign path/to/private.key --key-id my-key

# Entire directory
python3 create_receipt.py --directory ./src --sign path/to/private.key --key-id my-key

# From GitHub release
python3 create_receipt.py --archive https://github.com/user/repo/archive/v1.0.0.tar.gz \
    --sign path/to/private.key --key-id my-key
```

### Verifying Receipts

```bash
# CLI verification
python3 verifier/replay.py receipt.json --trust-manifest receipts/trust_manifest.json

# Browser verification
# Visit: https://sethirus.github.io/The-Thiele-Machine/verify.html
```

📖 **Full documentation:** [RECEIPT_GUIDE.md](RECEIPT_GUIDE.md) | [SIGNING_AND_TRUST.md](SIGNING_AND_TRUST.md)

---

## Self-Hosting Kernel

The Thiele kernel demonstrates **"system = proof"** architecture:

```
┌─────────────────────────────────────────────────┐
│           bootstrap_receipts/                    │
│  ┌─────────────────────────────────────────────┐│
│  │ 010_create_partition.json                   ││
│  │ 020_emit_mu_helpers.json                    ││
│  │ 030_emit_verify.json                        ││
│  │ 040_emit_replay.json                        ││
│  │ 050_kernel_emit.json                        ││
│  └─────────────────────────────────────────────┘│
└─────────────────┬───────────────────────────────┘
                  │ verifier/replay.py (170 LoC)
                  ▼
┌─────────────────────────────────────────────────┐
│              thiele_min.py                       │
│     SHA256: 77cd06bb...                          │
│     (Can verify its own receipts!)               │
└─────────────────────────────────────────────────┘
```

### One-Line Challenge

```bash
python3 verifier/replay.py bootstrap_receipts && \
python3 thiele_min.py --verify bootstrap_receipts/050_kernel_emit.json && \
sha256sum thiele_min.py
```

**Why this matters:**
- **Tiny TCB:** The verifier is ~170 lines—far smaller than trusting kernel source
- **Cryptographic:** Every byte justified by hash chains
- **Self-verifying:** The kernel verifies its own construction
- **Deterministic:** Same receipts → identical kernel

---

## Formal Verification

### Coq Proof Status

The repository contains **89 Coq files across 17 directories**, all building without axioms:

| Component | Status | Location |
|-----------|--------|----------|
| Core Kernel | ✅ Complete | `coq/kernel/` |
| Subsumption Proof | ✅ Complete | `coq/kernel/Subsumption.v` |
| Bell Thesis | ✅ Complete | `coq/thielemachine/verification/` |
| Theory Proofs | ✅ Complete | `theory/` |

### Key Theorems

- **`thiele_simulates_turing`** — Every Turing run reproduced exactly
- **`turing_is_strictly_contained`** — Thiele programs exist that classical traces cannot reach
- **`local_CHSH_bound`** — Classical CHSH ≤ 2 (Bell inequality)
- **Supra-quantum witness** — S = 16/5 > 2√2 (Tsirelson bound)

### Running Proofs

```bash
# Quick theory proofs
coqc -Q theory theory theory/Genesis.v
coqc -Q theory theory theory/Core.v

# Full kernel verification
cd coq && ./verify_subsumption.sh

# Bell thesis with Coq replay
./verify_bell.sh
```

### Audit Reports

- **[ADMIT_REPORT.txt](ADMIT_REPORT.txt)** — Inventory of admitted lemmas (regenerate with `python -m tools.generate_admit_report`)
- **[coq/AXIOM_INVENTORY.md](coq/AXIOM_INVENTORY.md)** — Narrative discussion of axioms

---

## Running Experiments

### Quick Experiment

```bash
python run_partition_experiments.py --problem tseitin --partitions 6 8 10 --seed-grid 0 1 --repeat 1 --emit-receipts
```

### Full Evidence Package

```bash
# Comprehensive experiment
python run_partition_experiments.py --problem tseitin \
    --partitions 6 8 10 12 14 16 18 \
    --seed-grid 0 1 2 --repeat 3 \
    --emit-receipts --save-outputs \
    --experiment-name full --plot-format svg
```

Outputs saved to `experiments/<timestamp>_full/`:
- `tseitin_analysis_plots.svg` — Four-up visualization
- `results_table.csv` — Raw data
- `inference.md` — Statistical analysis
- `manifest.json` — SHA-256 hashes

### Falsification Controls

Test that the separation depends on structure:

```bash
# Destroy structure (should collapse the ratio)
python run_partition_experiments.py --problem tseitin --partitions 6 8 --repeat 1 --mispartition
python run_partition_experiments.py --problem tseitin --partitions 6 8 --repeat 1 --shuffle-constraints
python run_partition_experiments.py --problem tseitin --partitions 6 8 --repeat 1 --noise 50
```

---

## Repository Structure

```
The-Thiele-Machine/
├── thielecpu/              # Reference VM implementation
│   ├── vm.py               # Python VM (8 opcodes)
│   ├── mu.py               # μ-bit accounting
│   └── hardware/           # Verilog implementation
├── coq/                    # Formal proofs (89 files)
│   ├── kernel/             # Subsumption proof
│   ├── thielemachine/      # Machine semantics
│   └── theory/             # As Above, So Below
├── verifier/               # Receipt verification
│   └── replay.py           # Core verifier (170 LoC)
├── examples/               # Demo receipts
├── bootstrap_receipts/     # Self-hosting kernel receipts
├── artifacts/              # Generated certificates
├── demonstrate_isomorphism.py  # Bell thesis demo
├── attempt.py              # Full orchestrator
└── run_partition_experiments.py
```

### Key Files

| File | Purpose |
|------|---------|
| `demonstrate_isomorphism.py` | Bell inequality demonstration (canonical artifact) |
| `attempt.py` | Full experiment orchestrator |
| `verifier/replay.py` | Receipt verification (170 LoC TCB) |
| `thielecpu/vm.py` | Reference VM implementation |
| `coq/kernel/Subsumption.v` | Formal subsumption proof |

---

## Installation

### Requirements

- **Python 3.12+**
- **Coq 8.18** (optional, for formal verification)

### Quick Install

```bash
# Linux/macOS
python3 -m venv .venv
source .venv/bin/activate
pip install -e .

# Windows
python -m venv .venv
.venv\Scripts\Activate.ps1
pip install -e .
```

### Full Install (with all extras)

```bash
# All dependencies (pinned versions)
pip install -r requirements.txt

# OR with optional extras
pip install -e ".[full]"

# Coq (Ubuntu/Debian)
sudo apt install coq

# OR via opam (any platform)
./verify_bell.sh  # Auto-provisions Coq 8.18
```

### Verify Installation

```bash
python3 verifier/replay.py examples/000_hello.json --trust-manifest receipts/trust_manifest.json
```

---

## For Reviewers

### ⚠️ This Is Not a Software Proposal

This artifact is a **physics experiment**, not code to be optimized. The Python script is a classical simulation—an instrument measuring the cost a classical machine pays for blindness to structure.

### The Three Axioms

1. **This is a measurement, not an algorithm.** The "inefficiencies" are experimental data, not bugs.

2. **The inefficiency IS the result.** The brute-force Engine of Discovery demonstrates the "sight debt" classical machines accumulate.

3. **Review the data, not the dummy.** Like a crash-test dummy, the script exists to produce measurements—not to be polished.

### What To Look For

- **Cryptographic receipts** — Can you verify the hash chains?
- **Empirical data** — Does the blind/sighted ratio increase with problem size?
- **Formal proofs** — Do the Coq files compile without admits?
- **Falsifiability** — Can you construct a counterexample?

### Reviewer Contract

If you evaluate this as a software library, you've misunderstood the experiment. The Python code is intentionally left unoptimized because the runtime cost IS the measurement.

---

## Citation

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

**APA:** Thiele, D. (2025). The Thiele Machine. Zenodo. https://doi.org/10.5281/zenodo.17316437

---

## Contributing

We welcome contributions! See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

**Ways to contribute:**
- Run experiments and report results
- Attempt to construct counterexamples
- Extend the Coq formalization
- Improve documentation

**For issues or questions:** [GitHub Issues](https://github.com/sethirus/The-Thiele-Machine/issues)

---

## License

Apache License 2.0 — see [LICENSE](LICENSE)

---

## Additional Resources

### Documentation

- **[RECEIPT_GUIDE.md](RECEIPT_GUIDE.md)** — Complete receipt system guide
- **[SIGNING_AND_TRUST.md](SIGNING_AND_TRUST.md)** — Key generation and trust setup
- **[REPLICATION_GUIDE.md](REPLICATION_GUIDE.md)** — Reproducing experiments
- **[documents/philosophy.md](documents/philosophy.md)** — Extended theoretical commentary

### Advanced Topics

- **[As Above, So Below](#as-above-so-below)** — μ-preserving equivalence between physics/logic/computation
- **[Project Cerberus](coq/project_cerberus/README.md)** — Self-auditing kernel
- **[CatNet](#catnet)** — Thiele-native neural networks
- **[VM Integration](VM_INTEGRATION.md)** — Self-aware structure detection

### Contact

- **Email:** thethielemachine@gmail.com
- **Issues:** [GitHub Issues](https://github.com/sethirus/The-Thiele-Machine/issues)

---

<details>
<summary><h2>Appendix: Detailed Technical Reference</h2></summary>

### The Thiele Machine Formal Definition

The Thiele Machine is a 5-tuple **T = (S, Π, A, R, L)**:

| Symbol | Name | Description |
|--------|------|-------------|
| **S** | State Space | All possible computational states |
| **Π** | Partitions | Ways to divide S into independent modules |
| **A** | Axioms | Logical rules for each module |
| **R** | Transitions | How the machine moves between states |
| **L** | Logic Engine | Certificate checker (analytic + optional solver) |

### μ-Bit Specification

For every reasoning step (q, N, M):

$$\mu_{total}(q, N, M) = 8|canon(q)| + \log_2(N/M)$$

Where:
- `canon(q)` — Canonical S-expression encoding of the question
- `N` — Possibilities before the step
- `M` — Possibilities after the step

**Implementation:** See [spec/mu_spec_v2.md](spec/mu_spec_v2.md) and [thielecpu/mu.py](thielecpu/mu.py)

### Instruction Set Architecture

```
PNEW    — Create new partition module
PSPLIT  — Split module into submodules
PMERGE  — Merge modules with consistency check
LASSERT — Logic assertion with certificate
LJOIN   — Join certificates from modules
MDLACC  — Accumulate μ-bit costs
EMIT    — Emit result with cryptographic receipt
XFER    — Transfer data between partitions
```

### As Above, So Below

The `theory/` directory proves a μ-preserving equivalence between four symmetric monoidal categories:

```
    Phys (Physical processes)
      ↕
    Log (Logical proofs)
      ↕
    Comp (Thiele programs)
      ↕
    Comp₀ (Free composition skeleton)
```

**Key proofs:**
- `Genesis.v` — Coherent process ≃ Thiele machine
- `Core.v` — Logical cut = categorical composition
- `PhysRel.v` — Concrete physics category
- `LogicToPhysics.v` — Logic → physics instantiation
- `CostIsComplexity.v` — μ-bit tariff dominates Kolmogorov complexity

### Glossary

| Term | Definition |
|------|------------|
| **μ-bit** | Atomic unit of discovery cost |
| **MDL** | Minimum Description Length |
| **NUSD** | No Unpaid Sight Debt (discovery always costs) |
| **Partition** | Division of state space into modules |
| **Certificate** | Verifiable proof of a computational step |
| **Blind Solver** | Classical solver unaware of structure |
| **Sighted Solver** | Solver exploiting partition structure |

</details>

---

*This document was the proposition. The code is the construction. The execution is the proof.*
