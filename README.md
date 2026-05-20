# The Thiele Machine

[![CI](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml/badge.svg)](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)

The Thiele Machine is a computational substrate where certification cost (μ) is tracked at the step relation rather than at the program layer. The principal structural result, Coq-verified, is asymmetric: every Thiele state has a canonical program projection onto a classical-equivalent state, and every classical state has multiple Thiele preimages with no canonical lift between them. The projection is the canonical map; the lift is not. The fields the projection drops — `vm_certified`, `csr_cert_addr`, μ — are provably not functions of the classical projection ([`cert_not_function_of_forget`](coq/kernel/witness/ProjectionNonExistence.v), [`mu_not_function_of_bare_observable`](coq/kernel/witness/ProjectionNonExistence.v)). Every Thiele machine has a Turing projection; no Turing machine has a canonical Thiele lift; and the directionality is proved, not stipulated.

Everything in this repository other than the substrate proof tree is a **realization** of the substrate — a particular instantiation in some computational medium. The OCaml runner extracted from the Coq kernel is a realization. The Kami RTL design synthesised through Bluespec and yosys is a realization. The FPGA bitstream is a realization. They are scaffolding for the substrate claim, not the claim itself. The substrate is the categorical object; its realizations are how you make contact with it.

## The argument

The classical theory of computation has two axes — time and space. The substrate adds a third, certification cost (μ), tracked at the step relation rather than at the program layer, and proves the classical models are its forgetful projection. The argument is four steps, each backed by a Coq theorem. If you find it unconvincing, the most useful response identifies which step is wrong — there's no step-zero objection that lands without engaging the structure.

**1. A2 constrains state fields the bare classical signatures don't have.**

A2 is the rule: every step that flips a certification predicate from false to true forces the executed instruction's cost ≥ 1. The certification predicate and the cost function are not in the bare Turing-machine signature (state, alphabet, transition table), nor in register machines or lambda calculi. If you extend a classical signature with cert and cost fields and a step rule that respects A2, you have moved to a different substrate — the `CertificationSystem` record at [coq/kernel/nfi/UniversalCertificationCost.v:30-65](coq/kernel/nfi/UniversalCertificationCost.v#L30-L65), over which `universal_nfi_any_substrate` concludes a trace-level cost floor of ≥ 1. [`cert_not_function_of_forget`](coq/kernel/witness/ProjectionNonExistence.v) sharpens the boundary: the certification flag is not a derived function of the bare classical projection, so A2's cert-predicate cannot be recovered from classical fields by any clever predicate. The claim is not that A2 is unwritable in the absolute sense — it is that A2 is a constraint on state fields the bare classical signatures lack, so any model carrying A2 is no longer the bare classical model.

**2. Therefore the substrate is forced.**

Any model that formalizes certification cost at the step rule must carry state that classical models do not. There is no "TM plus A2" — there is no A2 on a TM, by `cert_not_function_of_forget`. The structural axis (`vm_mu`, `vm_certified`, `csr_cert_addr`) is the minimum state for A2 to be a sentence in the first place. [`mu_not_function_of_bare_observable`](coq/kernel/witness/ProjectionNonExistence.v) proves the cost-ledger separation has no analog in the bare classical signature.

**3. Classical computation is the projection, and the projection is not invertible.**

[`lift_config`](coq/kernel/foundation/ProperSubsumption.v#L153) sends every Turing-machine configuration to a Thiele configuration. [`thiele_simulates_turing`](coq/kernel/foundation/ProperSubsumption.v#L172) runs every Turing-machine trace inside the substrate, same tape, same state. [`degenerate_projection_theorem`](coq/kernel/foundation/TuringClassicalEmbedding.v) closes the loop in one direction: classical computation is the image of substrate computation under the projection that forgets the structural axis. [`fiber_has_two_preimages`](coq/kernel/witness/BlindnessRepresentation.v) closes the other direction: every classical state has multiple Thiele preimages, so any lift back is non-canonical and requires external choice of cost schedule, graph state, and certification flag. [`D4_strictness`](coq/kernel/foundation/TuringStrictness.v) witnesses substrate states with no classical preimage. Same computable functions on both sides; classical machines aren't a parallel option, they are what the substrate looks like under the projection that hides the structural axis.

**4. Name the step.**

Step 1 is a sentence about what a classical step relation can carry, witnessed by `cert_not_function_of_forget`. Step 2 follows, witnessed by `mu_not_function_of_bare_observable`. Step 3 is mechanized in Coq with the theorem names above; the projection/lift asymmetry is witnessed by `fiber_has_two_preimages`. Pattern-matching the argument to a metaphor is an alternative reading rather than a rebuttal — the proofs stand or fall on whether the cited theorems hold, not on what they sound like.

The four steps are the entire foundational claim. They do not need 51 opcodes, do not need an FPGA, do not need CHSH. The minimum instruction set that witnesses the substrate is two opcodes: any classical compute primitive (so subsumption has something to project to) plus one opcode that flips certification (so A2 has something to enforce). `instr_certify` is the load-bearing opcode for A2; the rest of the ISA is exploration of what the substrate can express, not what it requires.

Everything else in this repository is a realization of the substrate, not the substrate itself:

- The 51-opcode ISA is one realization (47 RTL-realized + 4 Q_{1+AB} cert-opcodes that are VM-only by design, contributing the OCaml/RTL parity tests' tolerated slack of 4). The substrate claim does not depend on any of the non-`CERTIFY` opcodes.
- The CHSH↔NPA equivalence at the opcode level is a separate mathematical result that composes with the substrate. It is not part of the substrate proof.
- The Coq → OCaml → Kami → Verilog → FPGA pipeline is a realization of the substrate in silicon. It is not part of the substrate proof. The current bitstream flow targets Kintex-7 K325T (Digilent Genesys 2). `column_contractive_check_witness` is implemented in Kami as a 23-phase FSM that time-shares one 384×384 SignUU multiplier (Coq spec for `instr_chsh_lassert` is single-step; the multi-cycle execution is a Kami-implementation detail, invisible to the spec — same pattern as `instr_lassert`). With DSP inference disabled in yosys (`-nodsp`), the design maps to ≈151K LUT6 against K325T's 203K budget. See [fpga/run_synthesis_xc7.sh](fpga/run_synthesis_xc7.sh) and the `chsh_lassert_fsm` rule in [coq/kami_hw/ThieleCPUCore.v](coq/kami_hw/ThieleCPUCore.v).
- The Bekenstein/Landauer bridges are motivation, explicitly labeled as such in the monograph.

## Clarification: simulation vs. substrate

A common reading is that A2 can be enforced in software on a TM, so the substrate distinction is a hardware/software boundary rather than a fundamental one. That reading conflates simulation with substrate. The distinction is one sentence:

**A Turing machine cannot refuse to execute a buggy A2-simulator. A Thiele substrate cannot execute one.**

Load a Thiele simulator onto a TM with a bug — a program that certifies without incrementing μ. The TM runs it faithfully. Its step rule has no field for A2, so it cannot detect the bug; it computes whatever you wrote, A2-respecting or not. Load the same buggy program onto a Thiele substrate. The step rule traps. A2 is not interpreted by the simulator and could be skipped — it is the transition law itself. The TM is structurally incapable of refusal because its step rule has nothing to refuse on. The substrate is structurally incapable of execution because its step rule has A2 built in.

That is the difference between simulating a substrate and being a substrate. Subsumption is a step-rule claim, not a software-layer claim. "Thiele is simulable on a TM" is true and is not the question. "Thiele's step rule can be written down on a TM" is the question, and the answer is no.

## In one minute

The four steps above are mechanized by the following operational facts about
the substrate:

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

Every classical computer is a Thiele Machine in the sense made precise by
subsumption: the Turing machine, the register machine, lambda calculus, the
von Neumann CPU, every CPU on every desk --- each names one thing, viewed with
the structural axis hidden. The thing the label is naming is a Thiele Machine
running in the degenerate fragment of its own state space where the structural
axis stays dormant.

[`lift_config`](coq/kernel/foundation/ProperSubsumption.v) maps any
Turing-machine configuration to a Thiele configuration (set `mu = 0`).
[`thiele_simulates_turing`](coq/kernel/foundation/ProperSubsumption.v)
executes every Turing-machine run inside Thiele, same tape, same state.
[`D2_faithfulness`](coq/kernel/foundation/TuringClassicalEmbedding.v) and
[`D3_conservativity`](coq/kernel/foundation/ClassicalConservativity.v)
show the structural axis stays idle under classical programs. The four-part
[`degenerate_projection_theorem`](coq/kernel/foundation/TuringClassicalEmbedding.v)
closes the loop in one direction: classical computation is the image of Thiele
computation under the structural-axis projection. The other direction is closed
by [`fiber_has_two_preimages`](coq/kernel/witness/BlindnessRepresentation.v) —
every classical state has multiple Thiele preimages, so any lift back is
non-canonical and requires external choice. Strict extension is witnessed by
[`D4_strictness`](coq/kernel/foundation/TuringStrictness.v).

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

The VM exposes 51 opcodes total: 47 are RTL-realized (bisimulation-proven against the Kami model) and 4 are Q_{1+AB} cert-opcodes that are VM-only by design — they contribute the OCaml/RTL parity tests' tolerated slack of 4 (theorem `rtl_coverage_partition`: 37 + 10 + 0 = 47). The 47 RTL opcodes fall into six families.

| Family | Examples | Cost behavior |
|---|---|---|
| Partition and module structure | `PNEW`, `PSPLIT`, `PMERGE`, `PDISCOVER` | Programmer-declared, with zero-cost reversible structure supported by the model. |
| Logic and certification | `LASSERT`, `LJOIN`, `MDLACC` | `LASSERT` includes formula-length, entropy, and certification terms. |
| Memory, ALU, control flow | `LOAD`, `STORE`, `ADD`, `JUMP`, `HALT` | Classical compute surface. |
| Witness, tensor, cert flags | `CHSH_TRIAL`, `CERTIFY`, `REVEAL`, `TENSOR_SET`, `TENSOR_GET` | Certification/revelation instructions carry positive cost floors. |
| Categorical morphisms | `MORPH`, `COMPOSE`, `MORPH_ID`, `MORPH_ASSERT` | Morphism assertions are certification-bearing. |
| CHSH-aware certification | `CHSH_LASSERT` | Kernel-level column-contractivity check on `vm_witness` buckets. Decidable integer-arithmetic check; success ⇒ NPA-PSD via the bridge theorem [`chsh_lassert_no_trap_implies_quantum_realizable`](coq/kernel/quantum/QuantumPartitionPSD.v). Cost `S(mu_delta) ≥ 1` regardless of outcome (cert-setter discipline). |

The 4 VM-only Q_{1+AB} opcodes (`instr_chsh_lassert_1ab*`) extend `CHSH_LASSERT` with the Q_{1+AB} moment-matrix family. They run on the OCaml/Python VM but have no RTL counterpart in the current build; the substrate claim doesn't require them.

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
