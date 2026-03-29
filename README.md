# The Thiele Machine

**A CPU where structural knowledge costs something — proven from Coq proofs down to synthesized hardware.**

[![CI](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml/badge.svg)](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Coq](https://img.shields.io/badge/Coq-171%20Proof%20Files-blue)](coq/)

---

## The Problem: Computers Are Blind

The Turing Machine — the mathematical model every computer is built on — can only see one thing at a time. It's like navigating a maze by looking only at the floor tile you're standing on. You *can* find the exit. But you'll walk a lot more than someone with a map.

This blindness has a concrete cost. If a problem has hidden structure — independent subproblems, graph decompositions, separable variables — a blind computer can't see it. It searches anyway. Exponentially. A problem with two independent halves that could be solved separately in $O(2^{n/2} + 2^{n/2})$ gets solved blindly in $O(2^n)$.

This is the **Time Tax**: classical models assign zero cost to structural knowledge, so they pay in exponential time when structure exists but is hidden.

**The question nobody formally answered: what does it cost to *see* structure?**

---

## The Answer: Structure Costs $\mu$-bits

The Thiele Machine is a CPU that can see structure — but has to pay for it. Every certified claim about the state of the world costs at least one $\mu$-bit. You cannot strengthen a predicate for free. You cannot certify knowledge you haven't paid for. The ledger is inside the CPU itself, enforced by hardware, and proven unforgeable in Coq.

This is not a bookkeeping convention. It is an architectural invariant:

- The $\mu$-counter is monotonically non-decreasing by construction — proven for all 47 opcodes
- Cert-setting instructions (LASSERT, CERTIFY, EMIT, REVEAL) cost $\geq 1$ unconditionally — the `S cost` wrapper makes it mathematically impossible to write a zero-cost certified observation
- The $\mu$-ledger is **unique**: the initiality theorem proves any cost measure satisfying the same constraints must equal $\mu$ — there is no alternative

**Insight is not free. The hardware will not let it be.**

---

## The Surprise: Physics Fell Out

This project started as a computer science question about the cost of structural knowledge. The physics was not the goal — it was a consequence.

When you enforce information cost rigorously enough to put it in hardware and prove it in Coq, certain results appear that were not expected:

**Proven (zero Admitted, no project-local axioms):**
- **No-Cloning** — Perfect copying requires $2I \leq I + \mu$. If $\mu = 0$, this is $2I \leq I$, which is false for any $I > 0$. The quantum no-cloning theorem falls out as arithmetic on the ledger. No wavefunctions required.
- **Classical CHSH bound $|S| \leq 2$** — Proven by exhaustive enumeration of all 16 deterministic local strategies. Any observer constrained by the $\mu$-ledger cannot exceed this classically.
- **Tsirelson algebraic bound** — The quantum limit $2\sqrt{2}$ is derived from coherence constraints on the partition observer model.

**Structural analogy (honest scope — see [Physics Claims](#physics-claims-honest-scope) below):**
- Landauer's principle ($k_B T \ln 2$ per bit erased) motivates the $\mu$-cost model but is not derived from it
- Einstein field equations and spacetime geometry are formal structural parallels, explicitly documented as such — not emergence theorems

The bottom rungs of this ladder are proven mathematics. The top rungs are fascinating open questions. The distinction is documented precisely.

---

## The Claim

**Certified insight is not free.** A program can compute for free — arithmetic, memory, control flow can all be declared zero-cost. But the moment a program wants to *certify* what it found — to record a verified claim as reusable structural knowledge — it pays at least one $\mu$-bit. That floor is enforced by hardware and proven in Coq. You cannot certify for free. You cannot fake the ledger. You cannot reach zero.

This is not a claim about P vs NP or about making SAT faster. It is a precise, machine-checked theorem about certified predicate strengthening: **you cannot go from a weaker certified claim to a stronger one without running a cert-setter instruction, and every cert-setter costs at least 1**. The `S cost` wrapper in `VMStep.v` makes this a mathematical fact, not a policy.

Classical complexity theory measures time and space. The Thiele Machine adds a third axis — $\mu$-cost — that tracks the price of certified structural knowledge, mechanically enforced from Coq proofs down to synthesized hardware.

Every claim has a concrete falsifier. If you think something is wrong, the proofs won't compile.

---

## Quick Start

```bash
git clone https://github.com/sethirus/The-Thiele-Machine.git
cd The-Thiele-Machine
pip install -r requirements.txt
pip install -e . --no-deps
make ocaml-runner          # build extracted OCaml VM binary
pytest tests/              # full test suite
```

### Run the Cross-Layer Test Suite

```bash
make test-all              # core opcode parity, cosim, bisimulation, fuzz
make canonical-e2e         # extraction → RTL synthesis → Verilator smoke tests
```

### Assemble and Run a Program

```bash
# Assemble an example
python scripts/thiele_asm.py examples/fibonacci.asm -o fibonacci.bin

# Run it through the extracted OCaml VM
./build/extracted_vm_runner fibonacci.bin
```

### Write Your Own Program

```asm
; hello.asm  —  μ-cost grows monotonically
LOAD_IMM r0 42 1     ; r0 = 42, cost 1
LOAD_IMM r1 0  1     ; r1 = 0,  cost 1
ADD r2 r0 r1 1       ; r2 = r0 + r1, cost 1
HALT 0
```

See `scripts/thiele_asm.py` for the full 47-opcode ISA, encoding format, and example programs in `examples/`.

### Compile the Coq Proofs (requires Coq 8.18+)

```bash
make -C coq                # compile all 171 .v files
make ocaml-runner          # extract and link the OCaml VM runner
```

The standalone proof file — a single file with zero project imports and zero admits — compiles separately:

```bash
coqc -R vendor/kami/Kami Kami coq/ThieleMachineComplete.v
```

### Hardware Simulation

```bash
make rtl-check             # iverilog compilation check of RTL
make rtl-cosim             # iverilog co-simulation tests

# Verilator (faster, used in CI)
THIELE_RTL_SIM=verilator pytest tests/test_chsh_verilator_hardware_bridge.py
THIELE_RTL_SIM=verilator pytest tests/test_logic_z3_verilator_bridge.py
```

---

## The Evidence

| Component | Status |
|-----------|--------|
| **Coq proofs** | 171 active `.v` files, zero admits anywhere in the active tree, zero project-local axioms per Inquisitor audit |
| **Standalone proof** | `coq/ThieleMachineComplete.v` — one file, zero project imports, zero admits, full machine in 11 sections |
| **OCaml runtime** | `build/extracted_vm_runner` built by mechanical extraction from Coq through `coq/Extraction.v` |
| **Python VM** | `thielecpu/vm.py` — generated wrapper, delegates all execution to OCaml binary |
| **Verilog RTL** | 3 source files: `thiele_cpu_kami.v` (Kami-generated, all 47 opcodes), `thiele_cpu_top.v` (FPGA wrapper), `RegFile.v` |
| **Test suite** | 52 pytest files, 728 tests collected, covering opcode parity, cosim, bisimulation, Coq gates, fuzz, and RTL |
| **Inquisitor audit** | Active tree passes maximum-strictness static analysis, report in `INQUISITOR_REPORT.md` |

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

### The No Free Insight Theorem (Generalized)

The theorem exists in four increasingly general forms:

**Phase A (single cert field):** Any transition that increases `csr_cert_addr` or `vm_certified` ran a cert-setter instruction with cost ≥ 1. Proven for full trace sequences (not just single steps).

**Phase B (umbrella, all channels):** `no_free_certified_insight` — any trace whose cert evidence changes contains at least one cert-setter with cost ≥ 1 and μ grew by ≥ 1. The insight taxonomy (`InsightTaxonomy.v`) formally separates structural ops (MORPH, PNEW — free) from certification ops (MORPH_ASSERT, CERTIFY — always cost ≥ 1).

**Phase C (classical shadow):** The classical projection (registers + μ + err) is strictly lossy. Two states with identical classical shadows can be separated by a morphism-layer probe. Proven constructively via `shadow_separation_theorem` in `ShadowProjection.v`.

**Phase H (universal, any substrate):** `universal_nfi_any_substrate` in `UniversalCertificationCost.v` — parameterized over both state type and instruction type. If any certification system satisfies "one cert step costs ≥ 1," then any trace from uncertified to certified has total cost ≥ 1. Thiele is one instance; a proof assistant (cost = proof size), consensus protocol (cost = work), or physical measurement (cost = thermodynamic work) are all potential instances.

See `coq/kernel/NoFreeInsight.v` for the original statement, `kernel/InsightTaxonomy.v` for the umbrella, and `kernel/UniversalCertificationCost.v` for the substrate-independent form.

### The $\mu$-Conservation Law

For any trace $\tau = [i_1, \ldots, i_n]$:

$$\mu(s_n) = \mu(s_0) + \sum_{k=1}^{n} \delta_{i_k}$$

Since each $\delta_{i_k} \geq 0$, the ledger is monotonically non-decreasing by construction.

### CHSH and Quantum Bounds

The classical/factorizable CHSH bound at zero structural cost is anchored in the kernel:

| Regime | $\mu$-cost | Bound | Win Rate |
|--------|-----------|-------|----------|
| Classical (factorizable) | $\mu = 0$ | $\|S\| \leq 2$ | 75% max |
| Algebraic (any box) | any | $\|S\| \leq 4$ | — |

The Tsirelson-related proof work (`TsirelsonGeneral.v`, `TsirelsonFromAlgebra.v`) derives the $2\sqrt{2}$ bound from coherence assumptions. These are formal derivations inside the proof stack, not evidence that the executable machine is a quantum computer.

**The W2 chain (unforgeable trial counters):** `CHSHStatisticalBridge.v` connects the hardware CHSH trial counters to Bell incompatibility formally:

1. `CHSH_TRIAL` instructions are the *only* instructions that increment WitnessCounts buckets (`record_trial` in VMStep.v — proven in H7 via `chsh_trial_count_lower_bound`)
2. `chsh_stat_from_wc` computes $S = E(0,0)+E(0,1)+E(1,0)-E(1,1)$ directly from aggregate buckets
3. `chsh_stat_violation_not_local`: if the computed $|S| > 2$, no local deterministic strategy could have produced those counts — Bell incompatibility follows

The WitnessCounts hardware registers are updated unconditionally by the RTL on each `CHSH_TRIAL` instruction. They cannot be forged by any program trace. The formal chain from instruction execution to Bell incompatibility is zero-Admitted.

---

## Key Theorems (Proven in Coq)

| Theorem | What It Establishes | File |
|---------|---------------------|------|
| `mu_is_initial_monotone` | $\mu$ is the unique canonical cost functional | `kernel/MuInitiality.v` |
| `no_free_insight_general` | Supra-certification requires structure addition | `kernel/NoFreeInsight.v` |
| `vm_apply_mu` | Single-step $\mu$-conservation for all 47 opcodes | `kernel/VMStep.v` |
| `run_vm_mu_monotonic` | Multi-step $\mu$ never decreases | `kernel/SimulationProof.v` |
| `main_subsumption` | Thiele instruction set properly extends Turing instruction set (syntactic, not computational-power, separation) | `kernel/Subsumption.v` |
| `local_box_CHSH_bound` | Factorizable correlations satisfy $\|S\| \leq 2$ | `kernel/MinorConstraints.v` |
| `tsirelson_from_row_bounds` | Correlators satisfying NPA-1 row constraints satisfy $S^2 \leq 8$ | `kernel/TsirelsonGeneral.v` |
| `vm_lob_bypass` | `pnew_chain n` charges exactly $n \times \text{cost}$ $\mu$ | `ThieleMachineComplete.v` |
| `relational_compose_assoc` | Relational composition is associative | `kernel/CategoryLaws.v` |
| `compose_assoc_for_graph` | `graph_compose_morphisms` satisfies associativity | `kernel/CategoryBridge.v` |
| `tensor_bifunctor` | `graph_tensor_morphisms` is a bifunctor (interchange law) | `kernel/CategoryMonoidal.v` |
| `categorical_separation` | Two states can be computationally equivalent but categorically distinct | `kernel/PartitionSeparation.v` |
| `no_free_certified_insight` | Any trace that changes cert evidence contains a cert-setter instruction with cost ≥ 1; umbrella theorem covering all cert channels and all structural ops | `kernel/InsightTaxonomy.v` |
| `shadow_separation_theorem` | Two states share identical classical (register+mu+err) shadow but are separated by a MORPH_DELETE probe — classical layer cannot distinguish what the categorical layer can | `kernel/ShadowProjection.v` |
| `D5_thiele_strictly_extends_classical` | Thiele extends classical Turing (any classical trace is embeddable) and is strict (categorical ops are not classically reachable) | `kernel/TuringStrictness.v` |
| `universal_nfi_any_substrate` | For any `CertificationSystem` satisfying the cost axiom (one cert step costs ≥ 1), any trace from uncertified to certified has total cost ≥ 1 — holds for proof assistants, consensus protocols, physical measurements, or neural networks, not just Thiele | `kernel/UniversalCertificationCost.v` |
| `chsh_stat_violation_not_local` | A WitnessCounts aggregate with `chsh_stat > 2` is incompatible with any local deterministic strategy — connects unforgeable hardware trial counters (H7) to Bell incompatibility | `kernel/CHSHStatisticalBridge.v` |

---

## Architecture

### Ground Truth Chain

```
coq/kernel/VMStep.v          ← single ground truth (47 opcodes, semantics)
  │
  ├── coq/Extraction.v
  │     └── build/thiele_core.ml        (OCaml, mechanical extraction)
  │           └── build/extracted_vm_runner  (binary, via make ocaml-runner)
  │                 └── thielecpu/vm.py      (Python thin wrapper, DO NOT EDIT)
  │
  └── coq/kami_hw/ThieleCPUCore.v
        └── scripts/kami_extract.sh
              └── build/kami_hw/mkModule1_synth.v
                    └── thielecpu/hardware/rtl/thiele_cpu_kami.v  (tracked RTL)
```

**Standalone completeness artifact:**

```
coq/ThieleMachineComplete.v   ← zero project imports, zero admits, 11 sections
  ├── build/thiele_core_complete.ml      (archive only — NOT the runtime)
  └── build/kami_hw/Target_complete.ml   (archive only — NOT the runtime)
```

The standalone file proves every component is reachable from a single self-contained Coq source. It is a proof-completeness artifact. `Extraction.v` and `KamiExtraction.v` are the sole runtime extraction points.

### The 47-Opcode ISA

```
Structural:    PNEW PSPLIT PMERGE PDISCOVER
Logical:       LASSERT LJOIN MDLACC EMIT REVEAL
Compute:       XFER LOAD_IMM LOAD STORE ADD SUB
XOR ALU:       XOR_LOAD XOR_ADD XOR_SWAP XOR_RANK
Control:       JUMP JNEZ CALL RET HALT
I/O:           CHECKPOINT READ_PORT WRITE_PORT HEAP_LOAD HEAP_STORE
Certification: CERTIFY
Bitwise/ALU:   AND OR SHL SHR MUL LUI
Model/Other:   CHSH_TRIAL ORACLE_HALTS
Tensor:        TENSOR_SET TENSOR_GET
Categorical:   MORPH COMPOSE MORPH_ID MORPH_DELETE MORPH_ASSERT MORPH_TENSOR MORPH_GET
```

Every instruction takes an explicit $\mu_\delta \geq 0$. Every transition increments the $\mu$-ledger by that delta. Monotonicity is proven in Coq and enforced in hardware.

The 7 **Categorical** opcodes (0x27–0x2D) add a formal category layer on top of partition modules: typed morphisms between modules, relational composition, tensor product of disjoint morphisms, and identity morphisms. `MORPH_ASSERT` is a cert-setter: it charges $S(\text{cost}) \geq 1$ unconditionally — you cannot certify a structural relation for free, not even attempt it. Category laws (associativity, unitality, bifunctoriality) are proven in `CategoryLaws.v`, `CategoryBridge.v`, `CategoryMonoidal.v` — zero Admitted.

**Instruction encoding:** `[31:24] opcode | [23:16] op_a | [15:8] op_b | [7:0] cost`

### Hardware Limits (Kami RTL)

| Resource | RTL (hardware) | Software (Coq/OCaml) |
|---|---|---|
| Instruction memory | 65,536 words | unbounded |
| Data memory | 65,536 words | unbounded |
| Registers | 32 × 32-bit | 32 × `nat` |
| Partition table | 64 slots | configurable |
| $\mu$ counter | 32-bit | unbounded `nat` |
| Cost field | 8-bit (max 255) | 8-bit (same encoding) |

**Implications:**
- $\mu$ wrapping at $2^{32}$ means very long-running programs may silently overflow the hardware counter. Coq proofs assume unbounded `nat`; the 32-bit refinement is sound for programs whose total $\mu$ stays below $2^{32}$.
- `ORACLE_HALTS` charges a fixed 1,000,000 $\mu$ in hardware (conservative refinement). See `coq/kami_hw/VerilogRefinement.v`.

---

## Three-Layer Isomorphism

| Layer | Implementation | Role |
|-------|----------------|------|
| **Coq** | 171 `.v` files, zero admits | Mathematical ground truth |
| **OCaml** | Mechanically extracted from Coq | Authoritative executable |
| **Verilog** | Kami-generated, Yosys-synthesizable | Physical realization |

The Python VM (`thielecpu/vm.py`) is a generated thin wrapper that delegates all execution to the OCaml binary. It serializes program state to/from the runner — no opcode semantics live in Python.

The intended invariant is semantic agreement on covered execution paths:

$$S_{\text{Coq/Extracted}}(\tau) \approx S_{\text{Python/OCaml}}(\tau) \approx S_{\text{RTL}}(\tau)$$

---

## Project Structure

```
The-Thiele-Machine/
├── coq/                         # Active proof tree (171 .v files)
│   ├── kernel/                  # 128 core kernel files
│   ├── kami_hw/                 # 10 hardware abstraction/extraction files
│   ├── nofi/                    # NoFI interface (5 files)
│   ├── physics/                 # Formal physics embeddings (5 files)
│   ├── self_reference/          # Self-reference (9 files)
│   ├── thiele_manifold/         # Manifold bridge (4 files)
│   ├── thermodynamic/           # Thermodynamic bridge (2 files)
│   ├── spacetime/               # Spacetime (1 file)
│   ├── tests/                   # Coq-level tests (3 files)
│   ├── Extraction.v             # Runtime OCaml extraction (authoritative)
│   └── ThieleMachineComplete.v  # Standalone completeness proof
├── thielecpu/                   # Python layer
│   ├── vm.py                    # Generated thin wrapper (DO NOT EDIT)
│   ├── receipt.py               # TRS-1.0 receipt protocol
│   └── hardware/
│       ├── cosim.py             # Co-simulation harness
│       ├── rtl/                 # Verilog RTL (3 files)
│       └── testbench/           # Verilog testbench
├── build/                       # Extracted OCaml, compiled runner, Kami artifacts
├── rtl_harness/                 # Python bridge for Verilator co-simulation
├── tests/                       # 52 pytest files
├── scripts/                     # thiele_asm.py, inquisitor.py, kami_extract.sh, ...
├── examples/                    # Assembly programs and run scripts
│   └── programs/                # Named example programs (10 files)
├── archive/                     # Superseded Coq files (not in build)
└── vendor/                      # kami, bbv (Coq dependencies)
```

---

## The Inquisitor Standard

All active Coq proofs pass maximum-strictness static analysis:

```bash
python scripts/inquisitor.py
```

25+ lint rules enforced on every active Coq file:
- Zero `Admitted` / `admit` / `give_up` in the audited tree
- Zero project-local axioms in the audited tree
- All proofs end with `Qed` or `Defined`
- Standard library axioms only (`FunctionalExtensionality`, classical decidability)

Current report: `INQUISITOR_REPORT.md`

---

## The Knowledge Receipt

The categorical layer makes the machine a **knowledge auditor**: it tracks not just *what* the final state is but *how* knowledge was derived. Run the demo:

```bash
python demo_knowledge_receipt.py
```

Four acts:

1. **The Forged Claim** — `MORPH_ASSERT 99 two-hop cert 0`. Morphism 99 doesn't exist. The machine errors *and* charges $S(0)=1$ for the failed attempt. You cannot even try to certify for free.

2. **The Earned Path** — Build A→B→C via MORPH + COMPOSE. Read source/target back via MORPH_GET. The composition chain is navigable.

3. **The Certified Claim** — Same chain, add `MORPH_ASSERT`. `cert_addr` becomes nonzero. $S(4)=5$ charged, unavoidably.

4. **The Separation** — Two programs, identical `r0=1, r1=3, mu=8, err=False`. `MORPH_DELETE 0` succeeds on one, errors on the other. **Classically identical. Categorically distinct.** Proven in `coq/kernel/PartitionSeparation.v`, zero Admitted.

The $\mu$-receipt is unforgeable: if your $\mu$ < minimum verification cost, you didn't do the work. This is the NoFI theorem made executable.

---

## Physics Claims: Honest Scope

The physics-adjacent results in this repo are **formal structural analogs**, not derivations of physical law. Every claim is classified:

- **(S) Structural** — theorems about the mathematical model, unconditionally true given the definitions.
- **(C) Conditional** — "if physical axiom X holds, then Y follows." The logic is verified; whether X holds in nature is empirical.
- **(R) Consistency** — algebraic identities verifying internal coherence.

**What is genuinely proven:**
- $\mu$-conservation, NoFI, initiality — **(S)**, fully axiom-free
- NoFI generalized to any substrate — **(S)**, `universal_nfi_any_substrate` in `UniversalCertificationCost.v`
- Classical shadow is strictly lossy — **(S)**, `shadow_separation_theorem` in `ShadowProjection.v`
- Thiele strictly extends classical Turing — **(S)**, `D5_thiele_strictly_extends_classical` in `TuringStrictness.v`
- CHSH classical bound $\|S\| \leq 2$ at zero cost — **(S)**
- CHSH violation → Bell incompatibility (W2 chain) — **(S)**, `chsh_stat_violation_not_local` in `CHSHStatisticalBridge.v`
- Tsirelson algebraic bound $S^2 \leq 8$ from NPA-1 row constraints — **(S)**
- Categorical laws (associativity, tensor bifunctor) — **(S)**
- Categorical separation (morphism layer strictly richer than registers) — **(S)**

**What is a formal analog, not a physical derivation:**
- Einstein field equations in `EinsteinEquations4D.v` — the theorem holds *by construction*: the metric is position-independent (Christoffel symbols vanish identically), off-diagonal stress is defined as zero ("isotropic assumption"), and $G := 1/(8\pi)$ is a unit choice. Both sides reduce to zero in vacuum. This is a **(R)** consistency result, not an emergence theorem.
- The discrete Gauss-Bonnet chain (`EinsteinEmergence.v`) explicitly states: "The connection to physical gravity is an analogy."
- Born rule, Planck/speed-of-light relations — **(C)** or **(R)**, as documented in `thesis/thiele_machine_math_spec.tex`.

**Known structural gaps in the Einstein formalization:**
1. The discrete derivative (`RiemannTensor4D.v`) does not distinguish coordinate directions — all four partial derivatives collapse to the same finite difference against the first neighbor. A proper 4D discrete spacetime requires a 4-simplex neighborhood with labeled directions.
2. The metric is defined globally (position-independent), so all Christoffel symbols vanish by construction and the Einstein tensor is identically zero. The off-diagonal stress is separately defined as zero. The equation $G_{\mu\nu} = 8\pi G T_{\mu\nu}$ holds as $0 = 0$.

These gaps are documented in `coq/kernel/EinsteinEquations4D.v` and do not affect any core machine theorem ($\mu$-conservation, NoFI, initiality, categorical laws).

---

## The Falsification Targets

Every core claim has a concrete falsifier:

- **$\mu$-conservation:** Find any instruction where $\mu_\delta < 0$.
- **No Free Insight:** Certify $P_{\text{strong}}$ from a clean start with no revelation event.
- **No-signaling:** Find an instruction on module $A$ that changes module $B$'s observables.
- **Tsirelson bound:** Find a quantum-admissible box with $S > 2\sqrt{2}$.
- **No-cloning:** Build a zero-cost perfect cloner.
- **Cross-layer agreement:** Find a supported path where OCaml and RTL disagree on normalized observable state.

If you find any of these, the Coq proofs won't compile.

---

## Dependencies

**Python** (3.10+):
- `z3-solver` — SMT solving (used in test suite; LASSERT verification is on-chip at runtime)
- `cryptography`, `pynacl` — receipt verification
- `numpy`, `scipy` — numerical computation
- `pytest`, `hypothesis` — testing

**Coq** (8.18+):
- Required to rebuild proofs

**OCaml** (4.14+):
- `ocamlfind`, `str` — required for `make ocaml-runner`

**Verilog / Hardware:**
- `iverilog` — simulation and RTL check
- `verilator` — faster co-simulation (CI default)
- `yosys` — synthesis validation and gate checks
- `bsc` (Bluespec) + `nextpnr-ecp5` + `ecppack` — full FPGA flow (optional)

---

## Contributing

Two contribution types:
1. **Replication artifacts** — New programs testing $\mu$-ledger predictions.
2. **Counterexample hunts** — Attempts to violate the Cost Invariant.

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

*The Thiele Machine is a Turing-complete model augmented with explicit, formally verified mu-cost accounting.*
