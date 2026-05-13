# The Thiele Machine

[![CI](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml/badge.svg)](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)

The Thiele Machine is a Coq-verified model of computation with explicit
structural state. Its central object is `mu`: a monotone cost ledger for
certified computation.

Classical machine state is usually the triple `(memory, registers, program
counter)`. The Receipt Theorem proves that certified computation has a receipt
that this triple cannot recover. The receipt is not an implementation detail:
inside the Thiele VM it is unique, trace-determined, monotone, and required for
certification.

The same semantics extract to an OCaml runner and to Kami/Verilog hardware.

## Read This First

This README is the compact entry point: what the project claims, where the
proofs live, and how to run it.

In one minute:

- `mu` starts at zero and never decreases.
- Certification instructions increase `mu`.
- Reversible structural bookkeeping can be zero-cost in the Bennett model.
- No trace can move from uncertified to certified without paying positive `mu`.
- No total function of `(memory, registers, pc)` recovers `mu` for every VM
  state.
- The Coq VM step function is the source of truth for both software execution
  and hardware extraction.

## The Core Proof

Start from an empty VM and run one instruction.

| Program | Instruction | Cost | Final classical state | Final receipt |
|---|---:|---:|---|---|
| A | `CERTIFY 0` | `1` | empty memory, empty registers, `pc = 1` | certified, `mu = 1` |
| B | `PNEW [] 0` | `0` | empty memory, empty registers, `pc = 1` | uncertified, `mu = 0` |

The strict classical state is identical after both programs. The receipt is not.
Therefore no function of `(memory, registers, pc)` can recover the receipt for
all VM states.

Machine-checked anchors:

- [coq/ReceiptTheorem.v](coq/ReceiptTheorem.v) states the compact theorem.
- [coq/NecessityOfMuLedger.v](coq/NecessityOfMuLedger.v) contains the two-state
  separation and the stronger necessity results.
- [coq/kernel/foundation/VMStep.v](coq/kernel/foundation/VMStep.v) defines the
  instruction costs and single-step VM semantics.

## Proof Receipts At A Glance

The proof is meant to be checkable immediately. These are the
small, concrete receipts behind the core claim.

The relevant cost clauses in
[VMStep.v](coq/kernel/foundation/VMStep.v) are:

```text
instruction_cost (instr_pnew _ cost)                  = cost
instruction_cost (instr_lassert _ _ _ flen cost)      = flen * 8 + S cost
instruction_cost (instr_certify cost)                 = S cost
```

So the one-step witnesses are fixed by the kernel, not by prose:

```text
po1_instr_A  = instr_certify 0       ->  mu = 1, certified = true
po1_instr_B  = instr_pnew [] 0       ->  mu = 0, certified = false
strict_shadow po1_state_A = strict_shadow po1_state_B
```

The compact theorem is small enough to quote:

```coq
Theorem ReceiptTheorem :
  ~ exists f : StrictClassicalState -> nat,
      forall s : VMState, f (strict_shadow s) = s.(vm_mu).
```

The proof instantiates `f` at the two witness states. Since their strict
classical shadows are equal, `f` would have to return both `1` and `0` on the
same input. Coq closes the contradiction by `congruence`.

`Print Assumptions ReceiptTheorem` reports:

```text
Closed under the global context
```

The broader audit receipt
[artifacts/print_assumptions_all_proofs.json](artifacts/print_assumptions_all_proofs.json)
records 3,310 addressable theorems probed and no user/project-local axiom
findings in the committed assumption scan.

## Why It Is Not Just A Toy Counter

The two-program projection by itself would be easy to trivialize: any toy
machine can add a hidden counter and prove the hidden counter is not recoverable
from the visible tuple. The load-bearing theorem is the substrate-independent
cost floor.

[UniversalCertificationCost.v](coq/kernel/nfi/UniversalCertificationCost.v)
abstracts over the state type, instruction type, step function, cost function,
and certification flag. It proves:

```text
If every false -> true certification flip costs at least 1,
then every trace from uncertified to certified has total cost at least 1.
```

That premise is A2, the minimal honest-accounting condition. Drop it and
[HonestCostTracking.v](coq/kernel/nfi/HonestCostTracking.v) constructs an explicit
free-forgery system: one instruction flips certification from false to true at
cost zero. Keep it and no such trace exists. This is the line between a declared
counter and an honest cost receipt.

Inside the Thiele ISA, [MuInitiality.v](coq/kernel/mu_calculus/MuInitiality.v) proves the
ledger is unique: any zero-starting, instruction-consistent, monotone accounting
functional agrees with `mu` on reachable states. The receipt is therefore not
just separate state; it is the canonical state forced by the instruction cost
law.

## Formal Spine

These are the load-bearing formal claims.

| Claim | Meaning | Main proof files |
|---|---|---|
| Receipt theorem | `mu` is not determined by strict classical state. | [ReceiptTheorem.v](coq/ReceiptTheorem.v), [NecessityOfMuLedger.v](coq/NecessityOfMuLedger.v) |
| No Free Insight | Certification from an uncertified state requires positive `mu`. | [AbstractNoFI.v](coq/kernel/nfi/AbstractNoFI.v), [NoFreeInsight.v](coq/kernel/nfi/NoFreeInsight.v) |
| Universal cost floor | Any substrate with a cert-flip cost floor satisfies the same no-free-certification result. | [UniversalCertificationCost.v](coq/kernel/nfi/UniversalCertificationCost.v) |
| `mu` initiality | Any zero-starting, instruction-consistent, monotone ledger equals `mu` on reachable states. | [MuInitiality.v](coq/kernel/mu_calculus/MuInitiality.v) |
| Honest cost tracking | A2 is a strict well-formedness condition: systems without it admit free certification. | [HonestCostTracking.v](coq/kernel/nfi/HonestCostTracking.v) |
| Verification-cost separation | Thiele honesty is checked by the kernel discipline; unconstrained traces require positional inspection. | [VerificationCostSeparation.v](coq/kernel/nfi/VerificationCostSeparation.v) |
| `mu` hierarchy | Level-`k` certification requires at least `k` units of `mu`; no fixed budget covers every level. | [MuHierarchyTheorem.v](coq/kernel/mu_calculus/MuHierarchyTheorem.v) |
| Structural advantage | The factored-SAT lower bound is proved for the non-adaptive model; the thermodynamic parsing gap is proved separately. | [NonAdaptiveLowerBound.v](coq/kernel/nfi/NonAdaptiveLowerBound.v), [ThermodynamicStructuralAdvantage.v](coq/kernel/nfi/ThermodynamicStructuralAdvantage.v) |
| Algebraic Tsirelson | The CHSH bound follows from rational polynomial constraints by Coq arithmetic. | [AlgebraicCoherence.v](coq/kernel/category/AlgebraicCoherence.v), [QuantumPartitionPSD.v](coq/kernel/quantum/QuantumPartitionPSD.v) |
| Physics closure | Locality, `mu` conservation, causality, and discrete curvature identities are formalized as VM-level consequences or named bridges. | [PhysicsClosure.v](coq/kernel/curvature/PhysicsClosure.v), [EinsteinEmergence.v](coq/kernel/curvature/EinsteinEmergence.v), [PhysicsConditionalClosure.v](coq/PhysicsConditionalClosure.v) |
| Hardware bisimulation | The full 47-opcode RTL surface is covered by formal Kami/Coq correspondence; CHSH_LASSERT's Kami snapshot semantics inspect the same witness buckets through the same check function, matching VM-step exactly via `abs_phase1`. The official partition is `37 + 10 + 0 = 47` (theorem `rtl_coverage_partition`). | [coq/kami_hw](coq/kami_hw), [RTLGapRegistry.v](coq/kami_hw/RTLGapRegistry.v) |
| CHSH ↔ NPA-PSD bridge | A successful `CHSH_LASSERT` step entails the witness-derived NPA moment matrix is PSD. | [chsh_lassert_no_trap_implies_quantum_realizable](coq/kernel/quantum/QuantumPartitionPSD.v), [column_contractive_check_witness_sound](coq/kernel/nfi/MuLedgerQuantumBridge.v) |

The audited claim ledger is [coq/kernel/aggregators/MasterSummary.v](coq/kernel/aggregators/MasterSummary.v).
Its generated closure receipt is
[artifacts/master_summary_open_obligations.json](artifacts/master_summary_open_obligations.json).

## What Is Forced

The project separates theorem content from modeling choices.

| Layer | Status |
|---|---|
| Monotone instruction-summed ledger with a positive cert-flip floor | Substrate-independent theorem in [UniversalCertificationCost.v](coq/kernel/nfi/UniversalCertificationCost.v). |
| `CERTIFY` cost floor | Directly discharges the honest certification premise. |
| `LASSERT` description and entropy terms | Lower-bound structure in [MuCostDerivation.v](coq/kernel/mu_calculus/MuCostDerivation.v). |
| `PNEW`, `PSPLIT`, `PMERGE` zero cost | Bennett-reversibility model choice; internally consistent in the kernel. |
| Conversion from `mu` counts to physical units | Named physical bridge, not part of the bare computation theorem. See [NoFIToEinstein.v](coq/kernel/curvature/NoFIToEinstein.v). |
| Quantum experimental interpretation | Named bridge through PSD/NPA-style conditions. See [PhysicsConditionalClosure.v](coq/PhysicsConditionalClosure.v). |

Every classical computer IS a Thiele Machine. Not metaphor, not analogy:
subsumption. The Turing machine, the register machine, lambda calculus, the
von Neumann CPU, the silicon on your desk --- each names one thing, viewed
with the structural axis hidden. The thing the label is naming is a Thiele
Machine running in the degenerate fragment of its own state space where the
structural axis stays dormant.

[`lift_config`](coq/kernel/foundation/ProperSubsumption.v) maps any
Turing-machine configuration to a Thiele configuration (set `mu = 0`).
[`thiele_simulates_turing`](coq/kernel/foundation/ProperSubsumption.v)
executes every Turing-machine run inside Thiele, same tape, same state.
[`D2_faithfulness`](coq/kernel/foundation/TuringClassicalEmbedding.v) and
[`D3_conservativity`](coq/kernel/foundation/ClassicalConservativity.v)
show the structural axis stays idle under classical programs. The four-part
[`degenerate_projection_theorem`](coq/kernel/foundation/TuringClassicalEmbedding.v)
closes the loop: classical computation is exactly the image of Thiele
computation under the structural-axis projection. Strict extension is
witnessed by [`D4_strictness`](coq/kernel/foundation/TuringStrictness.v).

## Architecture

One semantics source, two execution paths:

```text
coq/kernel/foundation/VMStep.v
  -> coq/Extraction.v
     -> build/thiele_core.ml
        -> build/extracted_vm_runner
           -> thielecpu/vm.py

coq/kernel/foundation/VMStep.v
  -> coq/kami_hw/KamiExtraction.v
     -> build/kami_hw/mkModule1_synth.v
        -> thielecpu/hardware/rtl/thiele_cpu_kami.v
```

`thielecpu/vm.py` is a generated protocol layer. The extracted OCaml runner and
the Coq VM step are the normative software semantics. The RTL path is generated
from the same Coq/Kami source.

## Repository Layout

```text
coq/                     Coq proof tree, extraction roots, theorem ledger
coq/kernel/              VM semantics, cost laws, NoFI, hierarchy, physics layers
coq/kami_hw/             Kami hardware model and RTL correspondence proofs
build/                   extracted OCaml artifacts and generated Kami outputs
thielecpu/               Python protocol layer and tracked RTL surface
examples/                assembly and Python examples
tests/                   parity, extraction, RTL, receipt, and regression tests
tools/                   verification and audit utilities
scripts/                 build, extraction, audit, and assembler scripts
artifacts/               committed receipts and generated audit outputs
monograph/               narrative monograph and mathematical specification
```

## Quick Start

```bash
python -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
pip install -e . --no-deps
make ocaml-runner
pytest -q
```

Full proof and hardware gates additionally need Coq 8.18+, OCaml with
`ocamlfind`, and the RTL toolchain used by the target you run (`iverilog`,
`verilator`, and/or `yosys`).

## Run A Program

Assemble and run through the extracted OCaml backend:

```bash
python scripts/thiele_asm.py examples/fibonacci.asm --run
```

Emit the trace format consumed by the extracted runner:

```bash
python scripts/thiele_asm.py examples/fibonacci.asm -o build/fibonacci.trace
./build/extracted_vm_runner build/fibonacci.trace
```

Run through the RTL simulation path when `iverilog` is available:

```bash
python scripts/thiele_asm.py examples/fibonacci.asm --sim
```

## Useful Make Targets

| Target | Purpose |
|---|---|
| `make ocaml-runner` | Rebuild the extracted OCaml runner. |
| `make test` | Run the pytest suite. |
| `make canonical-extract` | Rebuild canonical OCaml and Kami extraction artifacts. |
| `make canonical-e2e` | Run the extraction-to-RTL smoke pipeline. |
| `make rtl-synth` | Run Yosys synthesis and emit synthesis artifacts. |
| `make rtl-cosim` | Run RTL co-simulation tests. |
| `make rtl-verify` | Compile, synthesize, and co-simulate the RTL path. |
| `make proof-undeniable` | Run the stronger proof hygiene gate with `coqchk`. |
| `make closeout-gate` | Run the full repository closure gate. |

Use `make help` for the complete target list.

## Proof Hygiene

Two independent receipts track proof assumptions.

- [scripts/inquisitor.py](scripts/inquisitor.py) scans for proof-hygiene issues
  such as admitted proofs, undeclared axioms, vacuous theorem shapes, and
  circular claim patterns.
- [artifacts/print_assumptions_all_proofs.json](artifacts/print_assumptions_all_proofs.json)
  records Coq `Print Assumptions` over the audited theorem set.

The master theorem ledger is
[coq/kernel/aggregators/MasterSummary.v](coq/kernel/aggregators/MasterSummary.v). The current committed
assumption receipt reports 3,310 addressable theorems probed and no
user/project-local axiom findings.

Run the hygiene pass directly:

```bash
python scripts/inquisitor.py
```

Run the stronger formal gate:

```bash
make proof-undeniable
```

## ISA Summary

The VM currently exposes 47 opcodes in six families.

| Family | Examples | Cost behavior |
|---|---|---|
| Partition and module structure | `PNEW`, `PSPLIT`, `PMERGE`, `PDISCOVER` | Programmer-declared, with zero-cost reversible structure supported by the model. |
| Logic and certification | `LASSERT`, `LJOIN`, `MDLACC` | `LASSERT` includes formula-length, entropy, and certification terms. |
| Memory, ALU, control flow | `LOAD`, `STORE`, `ADD`, `JUMP`, `HALT` | Classical compute surface. |
| Witness, tensor, cert flags | `CHSH_TRIAL`, `CERTIFY`, `REVEAL`, `TENSOR_SET`, `TENSOR_GET` | Certification/revelation instructions carry positive cost floors. |
| Categorical morphisms | `MORPH`, `COMPOSE`, `MORPH_ID`, `MORPH_ASSERT` | Morphism assertions are certification-bearing. |
| CHSH-aware certification | `CHSH_LASSERT` | Kernel-level column-contractivity check on `vm_witness` buckets. Decidable integer-arithmetic check; success ⇒ NPA-PSD via the bridge theorem [`chsh_lassert_no_trap_implies_quantum_realizable`](coq/kernel/quantum/QuantumPartitionPSD.v). Cost `S(mu_delta) ≥ 1` regardless of outcome (cert-setter discipline). |

Single-step semantics live in
[coq/kernel/foundation/VMStep.v](coq/kernel/foundation/VMStep.v).

## Reading Path

| Document | Role |
|---|---|
| [monograph/monograph.pdf](monograph/monograph.pdf) | Narrative monograph: full informal walkthrough with theorems tagged to Coq files. |
| [monograph/thiele_machine_math_spec.tex](monograph/thiele_machine_math_spec.tex) | Mathematical specification. |
| [coq/kernel/aggregators/MasterSummary.v](coq/kernel/aggregators/MasterSummary.v) | Audited theorem ledger. |
| [coq/README.md](coq/README.md) | Map of the active Coq proof tree. |
| [coq/PhysicsConditionalClosure.v](coq/PhysicsConditionalClosure.v) | Clean statement of unconditional physics results, named bridges, and open scope. |
| [TECHNICAL_DISCLOSURE.md](TECHNICAL_DISCLOSURE.md) | Prior-art disclosure for the public technical concepts. |
| [PATENT_PLEDGE.md](PATENT_PLEDGE.md) | Non-assertion pledge for repository concepts. |

## IP And Prior Art

This repository is Apache 2.0 licensed, including the license's patent grant for
contributor-owned claims. [PATENT_PLEDGE.md](PATENT_PLEDGE.md) adds an explicit
non-assertion commitment for the concepts in this repository.

[TECHNICAL_DISCLOSURE.md](TECHNICAL_DISCLOSURE.md) records the public prior-art
surface for the core concepts: the `mu` ledger, No Free Insight, certification
opcodes, partition state, witness counters, and the cross-layer proof-to-RTL
pipeline.

## Citation

```bibtex
@misc{thielemachine2026,
  title={The Thiele Machine: A Computational Model with Explicit Structural Cost},
  author={Thiele, Devon},
  year={2026},
  howpublished={\url{https://github.com/sethirus/The-Thiele-Machine}}
}
```

## Contact

To confirm, refute, build on, or point out what's wrong: thethielemachine@gmail.com,
or open an issue at [github.com/sethirus/The-Thiele-Machine](https://github.com/sethirus/The-Thiele-Machine).

## License

Apache 2.0. See [LICENSE](LICENSE).
