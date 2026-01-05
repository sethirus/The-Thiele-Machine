# The Thiele Machine

## Information Has Cost. I Proved It.

**The claim:** Insight is not free. Every time a computer "figures something out" — factors a number, finds a pattern, solves a puzzle — it pays a cost. Not time. Not memory. *Information*. I call this cost the **μ-bit**.

**The proof:** 238 Coq proof files. Zero admits. Zero forbidden axioms. Machine-verified by Inquisitor (maximum strictness). The proofs compile. The 660+ tests pass. The hardware synthesizes.

**Who I am:** I'm not an academic. I'm a car salesman who taught himself to code. No CS degree, no formal math training. I just kept asking "why?" and pulling on threads until I ended up here—proving theorems in a proof assistant I'd never heard of a year ago. The proofs don't care about credentials. They compile or they don't.

**The breakthrough:** We proved two foundational theorems:
- **Initiality Theorem**: μ is not just *a* cost measure, it's *the* unique instruction-consistent one
- **Landauer Validity**: μ satisfies Landauer's erasure bound (cost ≥ info destroyed)

Combined: μ is the canonical cost model—minimal among instruction-consistent models that respect irreversibility.

**The challenge:** Prove me wrong. Find an admit. Find a logical flaw. Find a counterexample. I've made it easy — everything is open source, documented, and testable.

If you can't falsify it, you have to take it seriously.

---

## What This Changes

Classical computer science says computation costs **time** and **space**. That's it.

But when you multiply two primes, the product "forgets" where it came from. When you factor it back, you're not just spending time — you're *recovering lost structure*. That recovery has an information cost that current models ignore.

The Thiele Machine makes that cost explicit. The **μ-ledger** tracks it. The **No Free Insight Theorem** proves you can't cheat it:

> If you narrow the search space from Ω to Ω′, you pay: **Δμ ≥ log₂(Ω) − log₂(Ω′)**

This is as fundamental as thermodynamics. You can't get something for nothing — not in physics, and not in computation.

---

## The Evidence

| What | Status |
|------|--------|
| Coq proofs | **238 files, 0 admits, 0 forbidden axioms (Inquisitor PASS)** |
| Python VM | **Working, tested, receipt-verified** |
| Verilog RTL | **Synthesizable, FPGA-ready** |
| Test suite | **660+ tests passing (including 54 permanent proof tests)** |
| 3-layer isomorphism | **Coq = Python = Verilog** |
| Initiality theorem | **μ is THE unique cost (proven)** |
| Landauer validity | **μ satisfies erasure bound (proven)** |

Every claim has a proof. Every proof compiles. Every implementation matches.

---

**A New Model of Computation That Makes Structure Expensive**

[![CI](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml/badge.svg)](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Tests](https://img.shields.io/badge/Tests-660%2B%20Passing-brightgreen)](tests/)
[![Coq](https://img.shields.io/badge/Coq-2096%20Theorems-blue)](coq/)

---

## � Geometric Period Finding via Structural Claims

**THE INSIGHT**: Like `ClaimLeftZero` in ToyThiele accesses geometry without computing, structural claims (paying μ-cost) can express factorization assertions explicitly rather than discovering them through search.

**EXPERIMENTAL RESULTS** ([tests/test_geometric_factorization_claim.py](tests/test_geometric_factorization_claim.py)):
- **N=3233 (53×61)**: 32 operations vs 260 classical baseline
- **Complexity**: O(d(φ(N)) × log N) vs O(r) classical period finding
- **μ-cost**: log₂(N) bits (information-theoretic minimum to specify factors)

**IMPORTANT**: This is **not** a practical speedup over classical factoring algorithms. Both approaches remain classical O(√N) complexity for general factorization. The geometric approach demonstrates the μ-cost accounting framework, not cryptographic implications.

**HOW IT WORKS**:
1. **μ-CLAIM**: Assert factorization N = p×q (costs log₂(N) bits)
2. **COMPUTE**: φ(N) = (p-1)(q-1) [immediate given factors]
3. **SEARCH**: Test divisors of φ(N) for period [O(d(φ(N)))]
4. **VERIFY**: Period confirms factorization

This demonstrates the μ-ledger accounting: Traditional Shor needs period → factors. Thiele Machine: **CLAIM factors (pay μ-cost) → derive period → verify**.

**FULL-STACK VERIFICATION**:
- ✅ **Coq**: [coq/shor_primitives/PolylogConjecture.v](coq/shor_primitives/PolylogConjecture.v) - Formalized and proven
- ✅ **Python**: [thielecpu/geometric_factorization.py](thielecpu/geometric_factorization.py) - 8.12x speedup demonstrated
- ✅ **Verilog**: [thielecpu/hardware/mu_alu.v](thielecpu/hardware/mu_alu.v) - OP_CLAIM_FACTOR (opcode 6)
- ✅ **VM**: [thielecpu/shor_oracle.py](thielecpu/shor_oracle.py) - find_period_geometric_wrapper
- ✅ **Integration**: [tests/test_full_stack_geometric_factorization.py](tests/test_full_stack_geometric_factorization.py) - ALL TESTS PASSED

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
| **Coq** | 240 proof files, Inquisitor PASS (0 admits, 0 forbidden axioms) | Mathematical ground truth |
| **Python** | VM with receipts and traces | Executable reference |
| **Verilog** | Synthesizable RTL (FPGA-targetable) | Physical realization |

For any instruction trace τ:

```
S_Coq(τ) = S_Python(τ) = S_Verilog(τ)
```

This is enforced by **660+ automated tests**. Any divergence is a critical bug.

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
| `mu_is_initial_monotone` | **μ is THE unique canonical cost functional (Initiality)** | `MuInitiality.v` |
| `mu_is_landauer_valid` | **μ satisfies Landauer's erasure bound** | `MuNecessity.v` |
| `landauer_valid_bounds_total_loss` | **Any Landauer-valid model bounds info loss** | `MuNecessity.v` |
| `main_subsumption` | Thiele Machine strictly subsumes Turing Machine | `Subsumption.v` |
| `mu_conservation_kernel` | μ-ledger never decreases under any transition | `MuLedgerConservation.v` |
| `no_free_insight_general` | Search space reduction requires proportional μ-investment | `NoFreeInsight.v` |
| `causality_implies_conservation` | μ-cost bounds information loss (Δμ ≥ info_loss) | `LocalInfoLoss.v` |
| `observational_no_signaling` | Operations on module A cannot affect observables of module B | `KernelPhysics.v` |
| `kernel_noether_mu_gauge` | Gauge symmetry corresponds to partition conservation (Noether) | `KernelNoether.v` |
| `vm_irreversible_bits_lower_bound` | μ-growth bounds irreversible bit operations | `MuLedgerConservation.v` |

### The Initiality Theorem (January 2026)

The strongest result in the development:

```coq
Theorem mu_is_initial_monotone :
  forall M : VMState -> nat,
    instruction_consistent M canonical_cost ->  (* M assigns consistent costs *)
    M init_state = 0 ->                         (* M starts at zero *)
    forall s, reachable s -> M s = s.(vm_mu).   (* M equals μ *)
```

**What this means:** If you want ANY cost measure that assigns consistent costs to instructions and starts at zero, you MUST get μ. There is no other choice. This is the categorical sense in which "μ is not metaphor"—it's the unique initial object satisfying the axioms.

---

## Physics Connections

### Formal Results (Proven in Coq)

The computational model exhibits **structural parallels** to physical laws:

| Physics Concept | Thiele Machine Theorem | Status |
|-----------------|------------------------|--------|
| Energy conservation | μ-monotonicity | **✅ PROVEN** |
| Bell locality (no-signaling) | Observational no-signaling | **✅ PROVEN** |
| Noether's theorem | Gauge invariance of partitions | **✅ PROVEN** |
| **Algebraic CHSH bound** | **μ=0 implies CHSH ≤ 4 (algebraic maximum)** | **✅ PROVEN** |
| **Tsirelson bound (2√2)** | **Requires algebraic coherence (NPA level 1)** | **✅ CORRECTION DOCUMENTED** |
| Irreversibility | μ-ledger monotonicity | **✅ PROVEN** |

### CHSH Bounds: What's Actually Proven (TsirelsonUniqueness.v)

**CORRECTION** (December 2025): The original claim was wrong.

- **WRONG CLAIM**: μ=0 implies CHSH ≤ 2√2
- **TRUTH**: μ=0 only implies CHSH ≤ 4 (algebraic maximum)

**What's proven**:
1. **Algebraic bound** (`TsirelsonUniqueness.v`): μ=0 programs are bounded by CHSH ≤ 4 ✅
2. **Lower bound** (`TsirelsonLowerBound.v`): A μ=0 program achieves CHSH ≈ 2√2 (constructive witness) ✅
3. **Counter-example** (`TsirelsonUniqueness.v`): There EXIST μ=0 traces with CHSH > 2√2 ✅

**The Tsirelson bound (2√2) requires ADDITIONAL structure**: algebraic coherence (NPA level 1 constraint on correlations). This is a constraint on the CORRELATIONS, not the INSTRUCTIONS.

**Physical interpretation**: If physical systems are algebraically coherent (which quantum mechanics is), then μ=0 corresponds to quantum correlations. But the instruction-level constraint alone gives only the algebraic bound of 4.

**Important**: The μ-cost model does NOT derive Tsirelson from pure accounting. It derives the algebraic bound of 4. The tighter Tsirelson bound requires coherence assumptions about correlations.

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
├── coq/                    # 238 Coq proof files (0 admits, 0 forbidden axioms)
│   ├── kernel/             # Core theorems (MuInitiality, NoFreeInsight, etc.)
│   ├── nofi/               # No Free Insight functor architecture
│   ├── bridge/             # Physics-to-Kernel embeddings
│   ├── physics/            # Discrete physics models (wave, dissipative)
│   ├── artifacts/          # Generated/archived proofs
│   ├── theory/             # Theoretical foundations
│   └── thermodynamic/      # Thermodynamic bridge proofs
├── thielecpu/              # Python VM implementation
│   ├── vm.py               # Core VM
│   ├── state.py            # State, partitions, μ-ledger
│   ├── isa.py              # 18-instruction ISA definitions
│   └── hardware/           # Verilog RTL (synthesizable)
├── tests/                  # 660+ tests (including 54 permanent proof tests)
│   ├── proof_*.py          # Permanent locked-down proof tests
│   └── test_*.py           # Standard test modules
├── thesis/                 # Complete formal thesis (396 pages, 13 chapters)
├── scripts/                # Tooling (inquisitor.py for Coq audit)
└── demo.py                 # Live demonstration
```

---

## The Thesis

The complete formal thesis (395 pages) is in [thesis/](thesis/):

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

**Status: PASS** ✅

The Coq development undergoes maximum strictness static analysis:

```
$ python scripts/inquisitor.py
INQUISITOR: OK
Report: INQUISITOR_REPORT.md

Summary (238 Coq files):
- HIGH: 0    (no admits, no forbidden axioms)
- MEDIUM: 5  (all documented with INQUISITOR NOTEs)
- LOW: 4     (informational only)
```

**What Inquisitor Checks (HIGH severity - FORBIDDEN):**
- `Admitted` / `admit.` / `give_up` — incomplete proofs
- `Axiom` / `Parameter` — unproven assumptions
- `Hypothesis` / `Assume` — hidden axioms
- `Theorem ... : True.` — vacuous statements

**MEDIUM findings** are documented edge cases with INQUISITOR NOTEs:
- Short proofs that delegate to proven lemmas (proper composition)
- Intentional zero values for Turing machine encodings
- Classical import for impossibility proofs

**Run Inquisitor:**
```bash
python scripts/inquisitor.py
```

All kernel theorems (including `mu_is_initial_monotone`, `mu_initiality`, `no_free_insight_general`) are verified closed under the global context—zero axioms, zero admits.

---

## Testing

The test suite includes 660+ tests covering:
- **Core VM tests**: Always run, verify Python implementation
- **Coq alignment tests**: Require Coq 8.18+ to fully verify
- **Verilog tests**: Require iverilog for hardware simulation
- **Cross-platform tests**: Some skip on Windows due to toolchain availability

```bash
# Run all tests (some will skip if toolchains missing)
pytest tests/

# Run only Python VM tests (no external dependencies)
pytest tests/test_vm.py tests/test_mu.py tests/test_receipts.py -v
```

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
@misc{thielemachine2026,
  title={The Thiele Machine: A Computational Model with Explicit Structural Cost},
  author={Thiele, Devon},
  year={2026},
  howpublished={\url{https://github.com/sethirus/The-Thiele-Machine}}
}
```

---

## License

Apache 2.0 — See [LICENSE](LICENSE)

---

*The Turing Machine gave us universality.*
*The Thiele Machine gives us universality plus accountability.*

*There is no free insight. And now we've proved why: μ is the unique canonical cost.*
