# The Thiele Machine

**A Computational Model with Explicit Structural Cost**

[![CI](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml/badge.svg)](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Coq](https://img.shields.io/badge/Coq-273%20Proof%20Files-blue)](coq/)

---

## The Claim

**Insight is not free.** Every time a computer "figures something out"—factors a number, finds a pattern, solves a puzzle—it pays a cost. Not time. Not memory. *Information*. This cost is the **mu-bit**.

Classical complexity theory measures time and space but assigns **zero cost** to structural knowledge. The Thiele Machine makes that cost explicit, measurable, and enforceable.

## Quick Start

```bash
git clone https://github.com/sethirus/The-Thiele-Machine.git
cd The-Thiele-Machine
pip install -r requirements.txt
pip install -e . --no-deps
pytest tests/
```

### Compile Coq Proofs (requires Coq 8.18+)
```bash
make -C coq
```

### Run Hardware Simulation (requires iverilog)
```bash
iverilog thielecpu/hardware/rtl/*.v -o thiele_cpu
```

---

## The Evidence

| Component | Status |
|-----------|--------|
| **Coq proofs** | 273 files (~59K lines), 0 Admitted, 52 documented axioms |
| **Python VM** | Working, tested, cryptographic receipts |
| **Verilog RTL** | Synthesizable with open-source tools |
| **Test suite** | 575 tests across 72 test files |
| **3-layer isomorphism** | Coq = Python = Verilog (bisimulation proven) |

---

## Key Theorems (Proven in Coq)

| Theorem | What It Establishes | File |
|---------|---------------------|------|
| `mu_is_initial_monotone` | mu is THE unique canonical cost functional | `MuInitiality.v` |
| `mu_is_landauer_valid` | mu satisfies Landauer's erasure bound | `MuNecessity.v` |
| `no_free_insight_general` | Search space reduction requires proportional mu-investment | `NoFreeInsight.v` |
| `mu_conservation_kernel` | mu-ledger never decreases under any transition | `MuLedgerConservation.v` |
| `main_subsumption` | Thiele Machine strictly subsumes Turing Machine | `Subsumption.v` |
| `local_box_CHSH_bound` | Classical CHSH bound: mu=0 implies |S| <= 2 | `MinorConstraints.v` |

### The Initiality Theorem

The strongest result: if you want ANY cost measure that assigns consistent costs to instructions and starts at zero, you MUST get mu. There is no other choice.

```coq
Theorem mu_is_initial_monotone :
  forall M : VMState -> nat,
    instruction_consistent M canonical_cost ->
    M init_state = 0 ->
    forall s, reachable s -> M s = s.(vm_mu).
```

### The No Free Insight Theorem

You cannot narrow the search space without paying the information-theoretic cost:

```
delta_mu >= log2(Omega) - log2(Omega')
```

---

## The Architecture

The Thiele Machine is defined as a 5-tuple **T = (S, Pi, A, R, L)**:

| Component | Description |
|-----------|-------------|
| **S** | State space (registers, memory, program counter) |
| **Pi** | Partition graph—how state decomposes into modules |
| **A** | Axiom sets—logical constraints per module |
| **R** | Transition rules—the 18-instruction ISA |
| **L** | Logic Engine—SMT oracle for consistency |

### The 18-Instruction ISA

```
Structural:    PNEW, PSPLIT, PMERGE, PDISCOVER
Logical:       LASSERT, LJOIN, MDLACC
Compute:       XFER, XOR_LOAD, XOR_ADD, XOR_SWAP, XOR_RANK
Certification: CHSH_TRIAL, EMIT, REVEAL
Control:       PYEXEC, ORACLE_HALTS, HALT
```

Each instruction has a defined mu-cost. The ledger updates atomically. Monotonicity is proven in Coq and enforced in hardware.

---

## Three-Layer Isomorphism

The Thiele Machine is implemented at three layers producing **identical state projections**:

| Layer | Implementation | Purpose |
|-------|----------------|---------|
| **Coq** | 273 proof files, 0 admits, 52 axioms | Mathematical ground truth |
| **Python** | VM with receipts and traces | Executable reference |
| **Verilog** | Synthesizable RTL (FPGA-targetable) | Physical realization |

For any instruction trace tau:
```
S_Coq(tau) = S_Python(tau) = S_Verilog(tau)
```

This is enforced by automated tests. Any divergence is a critical bug.

---

## Hardware Synthesis

The Verilog RTL synthesizes with Yosys (open-source):

| Module | Cells | Description |
|--------|-------|-------------|
| **mu-ALU** | 4,324 | Q16.16 fixed-point arithmetic |
| **Minimal CPU** | 526 | Core execution |
| **Core CPU** | 235 | Partition logic |
| **Full CPU** | 770 | Complete design |

Full synthesis with advanced features (64 partitions, 1024-element memory) requires Vivado.

---

## Project Structure

```
The-Thiele-Machine/
├── coq/                    # 273 Coq proof files (~59K lines)
│   ├── kernel/             # Core theorems (MuInitiality, NoFreeInsight, etc.)
│   ├── thielemachine/      # Main VM proofs
│   ├── bridge/             # Physics embeddings
│   └── ...
├── thielecpu/              # Python VM implementation
│   ├── vm.py               # Core execution engine
│   ├── state.py            # State machine, partitions, mu-ledger
│   ├── isa.py              # 18-instruction ISA
│   └── hardware/           # Verilog RTL
├── tests/                  # 575 tests across 72 files
├── scripts/                # Build, verification, analysis tools
├── tools/                  # mu-Profiler and utilities
├── thesis/                 # Complete thesis (PDF + LaTeX)
└── verifier/               # Cryptographic receipt verification
```

---

## The Inquisitor Standard

All Coq proofs pass maximum-strictness static analysis:

```bash
python scripts/inquisitor.py
```

**Checks:**
- Zero `Admitted` / `admit.` / `give_up` in kernel
- All axioms documented with mathematical references
- Compilation success

**Results:** 52 documented axioms (external mathematical results from quantum mechanics, linear algebra, numerical analysis).

---

## mu-Profiler

Analyze Python code for information revelation costs:

```python
from tools.mu_profiler import analyze, profile

result = analyze(my_algorithm)
print(f"mu-cost: {result['mu_cost']}")
print(f"Complexity: {result['complexity']}")

@profile
def my_function(data):
    return process(data)
```

See [tools/README_mu_profiler.md](tools/README_mu_profiler.md) for documentation.

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

This enables post-hoc verification without re-execution.

---

## Dependencies

**Python** (3.10+):
- `z3-solver` — SMT solving
- `cryptography`, `pynacl` — Receipt verification
- `numpy`, `scipy` — Numerical computation
- `pytest`, `hypothesis` — Testing

**Coq** (8.18+):
- Required only to rebuild proofs

**Verilog**:
- `iverilog` for simulation
- Vivado 2023.2 for FPGA synthesis

---

## Documentation

| Resource | Location |
|----------|----------|
| Main README | This file |
| Coq Proofs | [coq/README.md](coq/README.md) |
| mu-Cost Framework | [coq/MU_COST_REVISION.md](coq/MU_COST_REVISION.md) |
| Hardware | [thielecpu/hardware/README.md](thielecpu/hardware/README.md) |
| Thesis | [thesis/main.pdf](thesis/main.pdf) |

---

## Contributing

Two contribution types:
1. **Replication artifacts** — New proofpacks testing mu-ledger predictions
2. **Counterexample hunts** — Attempts to violate the Landauer inequality

Report potential counterexamples via issue labeled `counterexample`.

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
