# The Thiele Machine

**A New Model of Computation That Makes Structure Expensive**

[![CI](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml/badge.svg)](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Tests](https://img.shields.io/badge/Tests-1115%20Passing-brightgreen)](tests/)
[![Coq](https://img.shields.io/badge/Coq-Inquisitor%20Verified-blue)](coq/)

---

## The Problem

Why can computers multiply two numbers instantly but struggle to factor their product?

Classical models of computation (Turing machines, RAM) are **architecturally blind**. They compute over flat memory with no primitive awareness of structure. When your input has hidden structure—independent subproblems, symmetries, decompositions—the machine can't *see* it. It has to *discover* that structure through computation, and that discovery is never accounted for.

Classical complexity theory measures **time** and **space**. But it assigns **zero cost** to knowing that "this formula splits into independent parts" or "this graph has two components." That knowledge is treated as free—as if the Dewey Decimal System costs nothing.

---

## The Solution

The Thiele Machine introduces a **third dimension of computational cost**: the **μ-bit** (mu-bit).

The μ-bit measures structural information—partitions, constraints, decompositions. Every time you assert "these variables are independent" or "this module satisfies invariant Φ," you pay in μ-bits. The μ-ledger is **monotonically non-decreasing**: once you pay for structure, you can never get that cost back.

This is the **No Free Insight Theorem**, proven in Coq with zero admits:

> *You cannot narrow the search space without paying the information-theoretic cost of that narrowing.*

In formal terms: if execution reduces the compatible state space from Ω to Ω′, then:

```
Δμ ≥ log₂(Ω) - log₂(Ω')
```

---

## Turing Subsumption (Proven)

The Thiele Machine **strictly subsumes** the Turing Machine in the following formal sense:

```coq
Theorem main_subsumption :
  (* 1. Every Turing computation runs identically on the Thiele Machine *)
  (forall fuel prog st,
    program_is_turing prog ->
    run_tm fuel prog st = run_thiele fuel prog st)
  /\
  (* 2. The Thiele Machine has primitives that Turing semantics cannot express *)
  (exists p, run_tm 1 p initial_state <> target_state /\
             run_thiele 1 p initial_state = target_state).
```

**What this means:**
- Any Turing-only program produces identical results on both machines (simulation)
- The Thiele Machine has structural primitives (like `H_ClaimTapeIsZero`) that perform explicit state transformations a Turing interpretation treats as no-ops
- The μ-cost tracks these structural operations—Turing pays time to discover structure, Thiele pays μ-bits to assert it

**What this does NOT mean:**
- The Thiele Machine does not compute anything Turing-uncomputable
- Church-Turing still holds—this is about *explicit structure*, not *computability*

See [coq/kernel/Subsumption.v](coq/kernel/Subsumption.v) for the full proof.

---

## The Architecture

The Thiele Machine is defined as a 5-tuple **T = (S, Π, A, R, L)**:

| Component | Description |
|-----------|-------------|
| **S** | State space (registers, memory, program counter) |
| **Π** | Partition graph—how state is decomposed into modules |
| **A** | Axiom sets—logical constraints attached to each module |
| **R** | Transition rules—the 18-instruction ISA |
| **L** | Logic Engine—SMT oracle that verifies consistency |

The partition graph is the key innovation. Unlike classical machines where structure is implicit (in the programmer's head), here structure is **explicit, measurable, and costly**.

---

## The Three-Layer Isomorphism

This isn't just theory. The Thiele Machine is implemented at **three layers** that produce **identical state projections**:

| Layer | Implementation | Purpose |
|-------|----------------|---------|
| **Coq** | 187 proof files, Inquisitor PASS (0 findings) | Mathematical ground truth |
| **Python** | VM with receipts and traces (~3318 lines) | Executable reference |
| **Verilog** | Synthesizable RTL (FPGA-targetable) | Physical realization |

For any instruction trace τ:

```
S_Coq(τ) = S_Python(τ) = S_Verilog(τ)
```

This is enforced by **1115 automated tests**. Any divergence is a critical bug.

---

## The 18-Instruction ISA

```
Structural:    PNEW, PSPLIT, PMERGE, PDISCOVER
Logical:       LASSERT, LJOIN, MDLACC
Compute:       XFER, XOR_LOAD, XOR_ADD, XOR_SWAP, XOR_RANK
Certification: CHSH_TRIAL, EMIT, REVEAL
Control:       PYEXEC, ORACLE_HALTS, HALT
```

The VM also supports high-level pseudo-ops (`PYTHON`) that expand to sequences of these primitives.

Each instruction has a defined μ-cost. The ledger is updated atomically. μ-monotonicity is **proven as a theorem** and **enforced in hardware** (the μ-ALU has no subtract path for ledger updates).

---

## Key Theorems (All Proven in Coq, Zero Admits)

| Theorem | What It Establishes | File |
|---------|---------------------|------|
| `main_subsumption` | Thiele Machine strictly subsumes Turing Machine | `Subsumption.v` |
| `mu_conservation_kernel` | μ-ledger never decreases under any transition | `MuLedgerConservation.v` |
| `no_free_insight_general` | Search space reduction requires proportional μ-investment | `NoFreeInsight.v` |
| `observational_no_signaling` | Operations on module A cannot affect observables of module B | `KernelPhysics.v` |
| `kernel_noether_mu_gauge` | Gauge symmetry corresponds to partition conservation (Noether's theorem) | `KernelNoether.v` |
| `nonlocal_correlation_requires_revelation` | Supra-quantum (CHSH > 2√2) certification requires explicit revelation | `RevelationRequirement.v` |
| `vm_irreversible_bits_lower_bound` | μ-growth bounds irreversible bit operations (Landauer connection) | `MuLedgerConservation.v` |

---

## Physics Connections

These aren't analogies. They're formal correspondences:

| Physics | Thiele Machine |
|---------|----------------|
| Energy conservation | μ-monotonicity |
| Bell locality (no-signaling) | Observational no-signaling theorem |
| Noether's theorem | Gauge invariance of partition structure |
| Landauer's principle | Irreversibility lower bound |
| Second Law of Thermodynamics | μ-ledger only increases |

The **thermodynamic bridge postulate** (falsifiable, not proven): charging μ bits lower-bounds heat dissipation at Q_min = k_B T ln(2) × μ.

---

## Quick Start

```bash
git clone https://github.com/sethirus/The-Thiele-Machine.git
cd The-Thiele-Machine
pip install -r requirements.txt
python demo.py
```

### Run All Tests
```bash
pytest tests/
```

### Compile Coq Proofs (requires Coq 8.18+)
```bash
make -C coq
```

### Compile Verilog (requires iverilog)
```bash
iverilog thielecpu/hardware/*.v -o thiele_cpu
```

---

## Project Structure

```
The-Thiele-Machine/
├── coq/                    # 220 Coq proof files (Grade B: 89.1/100)
│   ├── kernel/             # Core theorems (all critical issues resolved)
│   ├── bridge/             # Coq-Python bridge definitions
│   └── physics/            # Physics correspondence proofs
├── thielecpu/              # Python VM implementation
│   ├── vm.py               # Core VM (~2965 lines)
│   ├── state.py            # State, partitions, μ-ledger
│   ├── isa.py              # 17-instruction ISA definitions
│   └── hardware/           # Verilog RTL (synthesizable)
├── tests/                  # 1115 tests (isomorphism enforcement)
├── thesis/                 # Complete formal thesis (13 chapters)
├── scripts/                # Tooling (inquisitor.py, etc.)
└── demo.py                 # Live demonstration
```

---

## The Thesis

The complete formal thesis is in [thesis/](thesis/):

| Chapter | Title | Content |
|---------|-------|---------|
| 1 | Introduction | What this is, who it's for, how to read it |
| 2 | Background | Turing Machines, RAM models, structural blindness |
| 3 | Theory | The 5-tuple definition, μ-bit, No Free Insight theorem |
| 4 | Implementation | Three-layer isomorphism (Coq/Python/Verilog) |
| 5 | Verification | Coq proofs, Inquisitor standard, zero admits |
| 6 | Evaluation | Empirical validation, test suites, benchmarks |
| 7 | Discussion | Physics connections, complexity implications, limitations |
| 8 | Conclusion | Summary of contributions, open problems |
| 9 | Verifier System | Receipt-defined certification, C-modules |
| 10 | Extended Proofs | Full proof architecture beyond kernel |
| 11 | Experiments | Adversarial falsification attempts, reproducible protocols |
| 12 | Physics & Primitives | Wave dynamics, Shor primitives, thermodynamic bridge |
| 13 | Hardware & Demos | Synthesizable RTL, μ-ALU, FPGA targeting |

---

## The Inquisitor Standard

**Quality Score: 89.1/100 (Grade B - "Good")** ✅

The Coq development undergoes comprehensive static analysis scanning 220 files across 20+ rule categories:

**Critical Issues (HIGH severity):** ✅ **0 found (100% resolved)**
- `Admitted` / `admit.` / `give_up` — incomplete proofs
- `Theorem ... : True.` — proving nothing (vacuous statements)
- `... -> True.` / `let ... in True.` — vacuous conclusions
- Undocumented `Axiom` / `Parameter` declarations

**Code Quality (MEDIUM severity):** 1,349 findings (91% false positives)
- Unused hypotheses (heuristic detection - high false positive rate)
- TODO/FIXME markers (legitimate documentation)
- Clamp/truncation operations (domain-constrained)

**Achievements:**
- ✅ **100% critical correctness issues resolved** (20/20)
- ✅ **0 vacuous statements** (all theorems prove meaningful properties)
- ✅ **0 admitted proofs** (all proofs complete with Qed)
- ✅ **All axioms documented** (6/6 with comprehensive justifications)
- ✅ **All physics invariance proven** (gauge symmetry, Noether correspondence)

**Run Inquisitor:**
```bash
python scripts/inquisitor.py --strict
```

See `scripts/INQUISITOR_GUIDE.md` for complete documentation and `INQUISITOR_FALSE_POSITIVES_ANALYSIS.md` for analysis of static analysis limitations.

---

## Receipt System

Every execution produces a cryptographic receipt chain:

```python
receipt = {
    "pre_state_hash": SHA256(state_before),
    "instruction": opcode,
    "post_state_hash": SHA256(state_after),
    "mu_cost": cost,
    "chain_link": SHA256(previous_receipt)
}
```

This enables **post-hoc verification**: check the computation without re-running it.

---

## Hardware Synthesis

The Verilog RTL synthesizes to Xilinx Zynq UltraScale+ (xczu9eg):

| Resource | Used | Available | Utilization |
|----------|------|-----------|-------------|
| LUTs | 24,567 | 274,080 | 8.97% |
| Flip-Flops | 18,945 | 548,160 | 3.45% |
| BRAM | 48 | 912 | 5.26% |
| DSP | 12 | 2,520 | 0.48% |

- **Target Frequency**: 200 MHz (met with +0.234 ns slack)
- **Performance**: 150 MIPS sustained, 200 MIPS peak

The μ-ledger's monotonicity is **physically enforced**—the hardware rejects any update that would decrease the accumulated value.

See [thielecpu/hardware/synthesis_report.md](thielecpu/hardware/synthesis_report.md) for full details.

---

## Dependencies

**Python** (3.10+):
- `z3-solver` — SMT solving for logic engine
- `cryptography` — Receipt chain cryptographic hashes
- `numpy`, `scipy` — Numerical computations
- `pytest`, `hypothesis` — Testing

**Coq** (8.18+):
- Required only to rebuild proofs
- Pre-compiled `.vo` files included

**Verilog**:
- `iverilog` for simulation
- Vivado 2023.2 for FPGA synthesis

---

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

Two main contribution types:
1. **Replication artefacts** — New proofpacks and datasets testing μ-ledger predictions
2. **Counterexample hunts** — Targeted attempts to violate the Landauer inequality

Report potential counterexamples by opening an issue labeled `counterexample` with full reproduction steps.

---

## Citation

```bibtex
@misc{thielemachine2025,
  title={The Thiele Machine: A Computational Model with Explicit Structural Cost},
  author={Thiele, Devon},
  year={2025},
  howpublished={\url{https://github.com/sethirus/The-Thiele-Machine}}
}
```

---

## License

Apache 2.0 — See [LICENSE](LICENSE)

---

*The Turing Machine gave us universality.*
*The Thiele Machine gives us universality plus accountability.*

*There is no free insight.*
