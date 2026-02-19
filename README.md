# The Thiele Machine

**A Computational Model with Explicit Structural Cost**

[![CI](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml/badge.svg)](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Coq](https://img.shields.io/badge/Coq-304%20Proof%20Files-blue)](coq/)

---

## The Claim

**Insight is not free.** Every time a computer figures something out---factors a number, finds a pattern, solves a puzzle---it pays a cost. Not time. Not memory. *Information*. This cost is the **mu-bit** ($\mu$).

Classical complexity theory measures time and space but assigns zero cost to structural knowledge. The Thiele Machine makes that cost explicit, measurable, and enforceable.

Every claim in this repository has a concrete falsifier. If you think something is wrong, the proofs won't compile.

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

### Run Hardware Simulation (iverilog or verilator)
```bash
iverilog thielecpu/hardware/rtl/*.v -o thiele_cpu

# optional alternate simulator
verilator --binary --timing -Ithielecpu/hardware/rtl \
  -DYOSYS_LITE --top-module thiele_cpu_tb \
  thielecpu/hardware/rtl/thiele_cpu_unified.v \
  thielecpu/hardware/testbench/thiele_cpu_tb.v
```

When using Python co-simulation (`thielecpu.hardware.cosim.run_verilog`), select backend with `THIELE_RTL_SIM=iverilog|verilator`.

### Simulation Semantics

- Curvature/deflection experiments in this repository are computational-model observations (μ-metric behavior), not claims of literal spacetime curvature in physical silicon.
- Singular behavior differs by layer:
  - Python VM: Bianchi violations raise `BianchiViolationError` (fail-fast exception).
  - Verilog RTL: `bianchi_alarm` latches a kill-switch and freezes instruction progress in fetch.

### FPGA Bitstream (Open-Source ECP5)
The CI pipeline uses an open-source FPGA flow: `yosys` $\to$ `nextpnr-ecp5` $\to$ `ecppack` (fpga-trellis) to generate an ECP5 bitstream artifact. The flow builds the full CPU with `YOSYS_LITE` enabled to keep parameterized region sizes tractable for PnR, while preserving the full instruction set and control logic.

---

## The Evidence

| Component | Status |
|-----------|--------|
| **Coq proofs** | 304 files, ~85,800 lines, 2,177 theorems/lemmas, **zero admits**, **zero axioms** beyond foundational logic |
| **Python VM** | 20,810 lines. Working reference implementation with cryptographic receipts |
| **Verilog RTL** | 8 source files, ~2,500 hand-written lines (+ synthesis output). Synthesizable, FPGA-targetable |
| **Test suite** | 891 tests across 108 test files |
| **3-layer isomorphism** | Coq $=$ Python $=$ Verilog. Same program, same state, three layers |
| **Inquisitor audit** | All 304 Coq files pass maximum-strictness static analysis with zero findings |

---

## Mathematics

### The $\mu$-Cost Functional

The Thiele Machine extends the Turing Machine with a monotonically non-decreasing cost ledger. For any instruction $i$ with cost $\delta_i \geq 0$:

$$\mu(s') = \mu(s) + \delta_i$$

where $s \xrightarrow{i} s'$ is a state transition. The ledger satisfies:

$$\forall s_0 \xrightarrow{*} s_n : \quad \mu(s_n) \geq \mu(s_0)$$

### The Initiality Theorem

If $M$ is any cost measure satisfying:
1. **Instruction-consistency**: $M(s') = M(s) + c(i)$ for fixed cost function $c$
2. **Zero initialization**: $M(s_0) = 0$

Then $M \equiv \mu$. The $\mu$-ledger is the *unique* canonical cost functional.

$$\forall M : \text{VMState} \to \mathbb{N}, \quad M(s_0) = 0 \wedge M(s') = M(s) + c(i) \implies M = \mu$$

### The No Free Insight Theorem

Search space reduction requires proportional $\mu$-investment:

$$\Delta\mu \geq \log_2 |\Omega| - \log_2 |\Omega'|$$

where $\Omega$ is the initial search space and $\Omega' \subset \Omega$ is the reduced search space after computation.

### The $\mu$-Ledger Conservation Law

For any trace $\tau = [i_1, \ldots, i_n]$:

$$\mu(s_n) = \mu(s_0) + \sum_{k=1}^{n} \delta_{i_k}$$

Since each $\delta_{i_k} \geq 0$, the ledger is monotonically non-decreasing. This is the computational analogue of the second law of thermodynamics: *information cost never decreases*.

### Irreversible Bits and Landauer's Principle

Each instruction carries an irreversibility count:

$$\text{irr}(i) = \begin{cases} 0 & \text{if } \delta_i = 0 \quad \text{(reversible)} \\ 1 & \text{if } \delta_i > 0 \quad \text{(irreversible)} \end{cases}$$

The total irreversible bit count over a trace bounds the minimum energy dissipation via Landauer's principle:

$$E_{\min} = k_B T \ln 2 \cdot \sum_{k=1}^{n} \text{irr}(i_k)$$

### Physics Embeddings

Three discrete physics models are embedded into the VM with constructive proofs:

**Reversible lattice gas** (zero $\mu$-cost):
$$\text{decode}(\text{run\_vm}(1, \tau, \text{encode}(L))) = \text{physics\_step}(L)$$
$$\forall L: \quad |\text{particles}(\text{stepped}(L))| = |\text{particles}(L)| \quad \wedge \quad p(\text{stepped}(L)) = p(L)$$

**Wave propagation** (zero $\mu$-cost):
$$E(\text{wave\_step}(s)) = E(s), \qquad p(\text{wave\_step}(s)) = p(s)$$

**Dissipative lattice** (positive $\mu$-cost):
$$\forall s, i: \quad \delta_i \geq 1 \implies \mu(s') \geq \mu(s) + 1$$

For reversible embeddings, the irreversible bit count is provably zero:
$$\text{irreversible\_count}(\text{fuel}, \tau, s) = 0$$

### CHSH and Quantum Bounds

The CHSH score $S$ satisfies regime-dependent bounds derived from $\mu$-accounting:

| Regime | $\mu$-cost | Bound | Win Rate |
|--------|-----------|-------|----------|
| Classical | $\mu = 0$ | $S \leq 2$ | 75% |
| Quantum | $\mu > 0$ | $S \leq 2\sqrt{2} \approx 2.828$ | 85.35% |
| Supra-quantum | $\mu = \mu_{\max}$ | $S = 4$ | 100% |

The Tsirelson bound emerges from $\mu$-conservation:

$$S_{\text{quantum}} \leq 2\sqrt{2} = \frac{5657}{2000} \cdot \frac{2000}{2000} \approx 2.8284$$

### Discrete Geometry

The Christoffel symbols on a lattice with metric $g_{\mu\nu}(w)$:

$$\Gamma^{\rho}_{\mu\nu} = \frac{1}{2}\left(\partial_\mu g_{\nu\rho} + \partial_\nu g_{\mu\rho} - \partial_\rho g_{\mu\nu}\right)$$

For uniform mass distribution $g_{\mu\nu} = 2m\,\delta_{\mu\nu}$ (constant), all Christoffel symbols vanish: $\Gamma^{\rho}_{\mu\nu} = 0$. Non-uniform mass creates curvature---the discrete analogue of Einstein's field equations.

### Stress-Energy and PNEW Dynamics

High information density (stress-energy) drives more PNEW operations:

$$T_{\mu\nu} \sim \text{encoding\_length}(m) + |\text{region}(m)|$$

$$\text{PNEW frequency} \propto T_{\mu\nu}$$

This is the "information curves spacetime" principle: dense information regions undergo more structural refinement.

---

## Key Theorems (Proven in Coq)

| Theorem | What It Establishes | File |
|---------|---------------------|------|
| `mu_is_initial_monotone` | $\mu$ is THE unique canonical cost functional | `kernel/MuInitiality.v` |
| `mu_is_landauer_valid` | $\mu$ satisfies Landauer's erasure bound | `kernel/MuNecessity.v` |
| `no_free_insight_general` | Search space reduction requires proportional $\mu$-investment | `kernel/NoFreeInsight.v` |
| `mu_conservation_kernel` | $\mu$-ledger never decreases under any transition | `kernel/MuLedgerConservation.v` |
| `main_subsumption` | Thiele Machine strictly subsumes Turing Machine | `kernel/Subsumption.v` |
| `local_box_CHSH_bound` | Unitary execution bound: $\mu=0 \implies S \leq 2$ | `kernel/MinorConstraints.v` |
| `thiele_simulates_turing` | Proper simulation of Turing computation | `kernel/ProperSubsumption.v` |
| `lattice_gas_embeddable` | Reversible lattice gas embeds into VM | `thielemachine/PhysicsEmbedding.v` |
| `wave_embeddable` | Wave model embeds into VM | `thielemachine/WaveEmbedding.v` |
| `dissipative_embeddable` | Dissipative model embeds with $\mu$-gap | `thielemachine/DissipativeEmbedding.v` |

---

## The Architecture

The Thiele Machine is defined as a 5-tuple $\mathbf{T} = (S, \Pi, A, R, L)$:

| Component | Description |
|-----------|-------------|
| $S$ | State space (VMState: registers, memory, pc, $\mu$-ledger, partition graph) |
| $\Pi$ | Partition graph---how state decomposes into modules |
| $A$ | Axiom sets---logical constraints per module |
| $R$ | Transition rules---the 18-instruction ISA |
| $L$ | Logic Engine---SAT/UNSAT certificate verification |

### The 18-Instruction ISA

```
Structural:    PNEW, PSPLIT, PMERGE, PDISCOVER
Logical:       LASSERT, LJOIN, MDLACC, EMIT, REVEAL
Compute:       XFER, XOR_LOAD, XOR_ADD, XOR_SWAP, XOR_RANK
Quantum:       CHSH_TRIAL
Special:       PYEXEC, ORACLE_HALTS
Control:       HALT
```

Every instruction takes an explicit $\mu_\delta \geq 0$. Every transition increments the $\mu$-ledger by that delta. Monotonicity is proven in Coq and enforced in hardware.

---

## Three-Layer Isomorphism

The Thiele Machine is implemented at three layers producing **identical state projections**:

| Layer | Implementation | Purpose |
|-------|----------------|---------|
| **Coq** | 304 proof files, ~85,800 lines, zero admits | Mathematical ground truth |
| **Python** | 20,810 lines, receipts and traces | Executable reference |
| **Verilog** | 8 source files, ~2,500 hand-written lines, synthesizable RTL | Physical realization |

For any instruction trace $\tau$:

$$S_{\text{Coq}}(\tau) = S_{\text{Python}}(\tau) = S_{\text{Verilog}}(\tau)$$

---

## Quantum Axioms from $\mu$-Accounting

Quantum mechanics is not postulated. It falls out of $\mu$-conservation:

| File | Theorems | What It Derives |
|------|----------|-----------------|
| `NoCloning.v` | 7 | Perfect cloning costs $\mu > 0$ |
| `NoCloningFromMuMonotonicity.v` | 3 | Machine-native no-cloning |
| `Unitarity.v` | 6 | Zero-cost evolution is CPTP |
| `BornRule.v` | 10 | $P = |a|^2$ from linearity |
| `BornRuleFromSymmetry.v` | 31 | Born rule from tensor consistency |
| `Purification.v` | 7 | Mixed states need references |
| `TsirelsonGeneral.v` | 15 | $S \leq 2\sqrt{2}$ from coherence |
| `TsirelsonFromAlgebra.v` | 11 | Self-contained algebraic Tsirelson |

---

## Falsification

Every claim has a concrete falsifier. To disprove:

- **$\mu$-conservation:** Find ANY instruction where $\mu_\delta < 0$.
- **No Free Insight:** Certify $P_{\text{strong}}$ from `clean_start` with no revelation event.
- **No-signaling:** Find an instruction on module $A$ that changes module $B$'s observables.
- **Tsirelson bound:** Find a quantum-admissible box with $S > 5657/2000$.
- **No-cloning:** Build a zero-cost perfect cloner.
- **3-layer isomorphism:** Find a program where Python $\neq$ Coq $\neq$ RTL.

If you find any of these, the Coq proofs won't compile.

---

## Project Structure

```
The-Thiele-Machine/
+-- coq/                    # 304 Coq proof files (~85,800 lines)
|   +-- kernel/             # Core theorems (MuInitiality, NoFreeInsight, etc.)
|   +-- modular_proofs/     # Turing/Minsky simulation proofs
|   +-- nofi/               # No Free Insight functor architecture
|   +-- physics/            # Discrete, wave, and dissipative models
|   +-- thielemachine/      # VM proofs and physics embeddings
|   +-- thiele_manifold/    # PhysicsIsomorphism and embedding framework
|   +-- isomorphism/        # Categorical Universe proof
|   +-- bridge/             # Domain-to-kernel bridges
|   `-- ...                 # 26+ subdirectories total
+-- thielecpu/              # Python VM (20,810 lines)
|   +-- vm.py               # Core execution engine
|   +-- state.py            # State machine, partitions, mu-ledger
|   +-- isa.py              # 18-instruction ISA
|   `-- hardware/           # Verilog RTL (8 source files)
+-- build/                  # Compiled OCaml VM runner and artifacts
+-- tests/                  # 891 tests across 108 test files
+-- scripts/                # Build, verification, inquisitor
+-- tools/                  # mu-Profiler and extracted VM runner
+-- verifier/               # Physics divergence verification
`-- thesis/                 # Complete thesis (PDF + LaTeX)
```

---

## The Inquisitor Standard

All Coq proofs pass maximum-strictness static analysis:

```bash
python scripts/inquisitor.py
```

25+ lint rules enforced on every Coq file:
- Zero `Admitted` / `admit` / `give_up` across all 304 proof files
- Zero custom axioms beyond `AssumptionBundle.v`
- All proofs end with `Qed` or `Defined`
- Standard library axioms only (functional extensionality, classical decidability)

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
- `z3-solver` --- SMT solving
- `cryptography`, `pynacl` --- Receipt verification
- `numpy`, `scipy` --- Numerical computation
- `pytest`, `hypothesis` --- Testing

**Coq** (8.18+):
- Required only to rebuild proofs

**Verilog**:
- `iverilog` for simulation
- `yosys` + `nextpnr-ecp5` + `ecppack` for open-source FPGA synthesis

---

## Contributing

Two contribution types:
1. **Replication artifacts** --- New proofpacks testing $\mu$-ledger predictions.
2. **Counterexample hunts** --- Attempts to violate the Cost Invariant.

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

Apache 2.0 --- See [LICENSE](LICENSE)

---

*The Turing Machine gave us universality.*
*The Thiele Machine gives us universality plus accountability.*
