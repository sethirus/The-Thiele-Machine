# The Thiele Machine

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17316437.svg)](https://doi.org/10.5281/zenodo.17316437)
[![Latest release](https://img.shields.io/github/v/release/sethirus/The-Thiele-Machine?label=release)](https://github.com/sethirus/The-Thiele-Machine/releases/latest)
[![CI](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml/badge.svg)](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Coq](https://img.shields.io/badge/Coq-0%20project--local%20axioms-EF4135?logo=coq&logoColor=white)](coq/)
[![Inquisitor](https://img.shields.io/badge/Inquisitor-0%20findings-brightgreen)](scripts/inquisitor.py)
[![RTL bisimulation](https://img.shields.io/badge/RTL%20bisimulation-47%2F47%20Qed-orange)](coq/kami_hw/RTLGapRegistry.v)

A normal computer can stamp "verified" on anything. The stamp is just code, and code can be buggy, skipped, or lying. Nothing in the machine prevents a program from claiming a result it didn't earn.

This is a machine where that move is impossible. Not difficult, not unlikely — impossible at the level of the step rule. A transition from "unverified" to "verified" cannot happen unless that transition pays a positive cost. The check isn't in software; it's in the law of motion. There is no checker to bypass, because there is no checker.

Every ordinary computer tracks time and memory. None of them track *proof*. Two programs that both end with `verified = true` are indistinguishable to the machine running them, even if one did the work and the other forged it. This machine adds one axis of state and one rule, and that asymmetry disappears.

This is not faster computation. It is not new computable functions. It is the same set of things you can compute, with one new constraint on *how* you can claim to have computed them.

I call it a Thiele machine. The name attaches me to the claim, if I'm wrong, I take the hit; if I'm right, the label is the least of it.

**See it in code:** [examples/demo_knowledge_receipt.py](examples/demo_knowledge_receipt.py) — four acts: a forged claim refused, an earned path, a certified claim, and two classically-identical programs separated by one probe instruction.

Everything in this repository other than the proof tree of the idea above is a **realization** of it: a particular instantiation in some computational medium. The OCaml runner extracted from the Coq kernel is a realization. The Kami RTL design synthesised through Bluespec and yosys is a realization. The FPGA bitstream is a realization. They are scaffolding for the claim, not the claim itself. The thing being claimed is the abstract object; the realizations are how you make contact with it.


## In three lines

Each line is a thing I am willing to be wrong about by name. Wrong conclusion means wrong premise — the law you learned in tenth grade and have not been asked to unlearn since. There is no third move.

1. If flipping a certification bit costs ≥ 1 (A2).
2. And classical machines have no state slot to enforce this constraint at the step-transition level.
3. Then classical machines are a structurally blind, strictly lossy projection of a substrate that does.

That's the whole claim. A napkin holds it. Delete the repository and the three lines still hold. The four steps below are this argument unfolded with kernel citations — same content, more words.

Where to look. The first line is A2, and A2 is two clauses and an integer. A step that flips cert costs at least one, the rule fits on the napkin with the conclusion, and the check is finite, public, and yours to run. The second line is the kind of fact you defeat by writing down a different Turing machine, and I'd genuinely love for someone to. Here's how it goes when I try. A state type with a field the step rule reads to see whether the last move flipped cert has already left the classical world, which was the claim. A state type that stays classical has the fields it has, and I can list them; none of them is that field. There aren't any. That is not philosophy, that is just the signature, sitting there.

The next move is the simulator: decline the field, run my rule as a program on the tape, increment cert in the program. Granted. The TM produces every trace I produce, beat for beat. It produces the buggy ones too — faithful is what TMs do. The substrate cannot run the buggy version. That gap — same trace minus the *can't* — is line 3. Simulation is not the escape from the projection. Simulation *is* the projection with the loss made operational.

The stakes are that specific. Coq is a notebook of receipts; the arithmetic comes out the way it comes out.


## The argument, formally

The opener says it in plain English. Here it is as four steps for the technical reader, each backed by a Coq theorem. The classical theory of computation has two axes: time and space. This machine adds a third, certification cost (μ), tracked at the step relation rather than at the program layer, and proves the classical models are its forgetful projection. If a step doesn't land for you, that's the interesting place to push — and the honest news is that there's no step-zero objection that does any work without engaging the structure, which is the whole reason I bothered to lay the steps out one at a time.

**1. A2 constrains state fields the bare classical signatures don't have.**

A2 is the rule: every step that flips a certification predicate from false to true forces the executed instruction's cost ≥ 1. The certification predicate and the cost function are not in the bare Turing-machine signature (state, alphabet, transition table), nor in register machines or lambda calculi. Being Turing-equivalent doesn't add them: equivalence preserves which functions you compute, not what the step can read, so the whole class lacks the field by the property that makes it the class. If you extend a classical signature with cert and cost fields and a step rule that respects A2, you have moved to a different substrate: the `CertificationSystem` record at [coq/kernel/nfi/UniversalCertificationCost.v:30-65](coq/kernel/nfi/UniversalCertificationCost.v#L30-L65), over which `universal_nfi_any_substrate` concludes a trace-level cost floor of ≥ 1. [`cert_not_function_of_forget`](coq/kernel/witness/ProjectionNonExistence.v) sharpens the boundary: the certification flag is not a derived function of the bare classical projection, so A2's cert-predicate cannot be recovered from classical fields by any clever predicate. The claim is not that A2 is unwritable in the absolute sense. It is that A2 is a constraint on state fields the bare classical signatures lack, so any model carrying A2 is no longer the bare classical model.

**2. Price certification in the step rule, and the extra state is forced.**

Any model that formalizes certification cost at the step rule must carry state that classical models do not. There is no "TM plus A2": there is no A2 on a TM, by `cert_not_function_of_forget`. The structural axis (`vm_mu`, `vm_certified`) is the minimum state for A2 to be a sentence in the first place. [`mu_not_function_of_bare_observable`](coq/kernel/witness/ProjectionNonExistence.v) proves the cost-ledger separation has no analog in the bare classical signature.

**3. Classical computation is the projection, and the projection is not invertible.**

[`lift_config`](coq/kernel/foundation/ProperSubsumption.v#L153) sends every Turing-machine configuration to a Thiele configuration. [`thiele_simulates_turing`](coq/kernel/foundation/ProperSubsumption.v#L172) runs every Turing-machine trace inside the substrate, same tape, same state. [`degenerate_projection_theorem`](coq/kernel/foundation/TuringClassicalEmbedding.v) closes the loop in one direction: classical computation is the image of substrate computation under the projection that forgets the structural axis. [`fiber_has_two_preimages`](coq/kernel/witness/BlindnessRepresentation.v) closes the other direction: every classical state has multiple Thiele preimages, so any lift back is non-canonical and requires external choice of cost schedule, graph state, and certification flag. [`D4_strictness`](coq/kernel/foundation/TuringStrictness.v) witnesses substrate states with no classical preimage. Same computable functions on both sides; classical machines are the canonical projection — the forgetting is the choice-free direction, the lift back is not — the smaller structure, the substrate with the structural axis dropped.

**4. Which step is doing the work.**

Step 1 is a sentence about what a classical step relation can carry, witnessed by `cert_not_function_of_forget`. Step 2 follows, witnessed by `mu_not_function_of_bare_observable`. Step 3 is mechanized in Coq with the theorem names above; the projection/lift asymmetry is witnessed by `fiber_has_two_preimages`. But that asymmetry alone is not where the weight sits, and I want to be precise about this, because it's the spot the whole claim gets attacked. Any field-drop has a unique forgetful map and a non-canonical lift — tagged-ℤ has exactly that asymmetry too, and it buys a richer extension, nothing more. Three machine-checked facts the asymmetry can't reach are what make the gap bite: (μ, cert) is the proved-minimal extension over (mem, regs, pc): cert isn't a function of the rest, μ isn't a function of the rest ([`P_full_is_minimal_complete_extension`](coq/kernel/nfi/NecessityAbstract.v#L748)), the state a step rule needs to read the cert from and charge the μ to; A2 is the *exact least* local pricing law for the cert-flip — miss a cert-flip and you fail the floor on a one-step trace, charge a non-cert-flip and you overcharge, so the only exact non-overcharging substitute *is* A2, proved holding trust fixed ([`substitution_test_rejects_non_a2_exact_substitute`](coq/kernel/nfi/CommitmentPredicateAdequacy.v#L388), [`substitution_test_exact_substitute_is_a2`](coq/kernel/nfi/CommitmentPredicateAdequacy.v#L402), packaged in [`a2_equal_trust_substitution_payoff`](coq/kernel/nfi/A2Payoff.v#L47)); and a classical step rule can only run a fallible checker of A2, never carry it as the law. So here's what it comes to: classical is the smaller structure, the state left when you forget the law, and the field it's missing is the one you'd most want a machine to enforce in the step. It's tempting to pattern-match the whole thing to a metaphor and move on, and I get the reflex, but check the cited theorems rather than the vibe: they stand or fall on whether they hold, not on what they sound like.

The four steps are the entire foundational claim. They do not need 51 opcodes, do not need an FPGA, do not need CHSH. The minimum instruction set that witnesses the substrate is two opcodes: any classical compute primitive (so subsumption has something to project to) plus one opcode that flips certification (so A2 has something to enforce). `instr_certify` is the load-bearing opcode for A2; the rest of the ISA is exploration of what the substrate can express, not what it requires.

Everything else in this repository is a realization of the substrate, not the substrate itself:

- The 51-opcode ISA is one realization (47 synth-realized + 4 Q_{1+AB} cert-opcodes that live in the Kami HW abstraction with kernel-equivalence proven but are excluded from the synthesized bitstream by silicon budget, contributing the OCaml/RTL parity tests' tolerated slack of 4). The substrate claim does not depend on any of the non-`CERTIFY` opcodes.
- The CHSH↔NPA equivalence at the opcode level is a separate mathematical result that composes with the substrate. It is not part of the substrate proof.
- The Coq → OCaml → Kami → Verilog → FPGA pipeline is a realization of the substrate in silicon. It is not part of the substrate proof. The current bitstream flow targets Kintex-7 K325T (Digilent Genesys 2). `column_contractive_check_witness` is implemented in Kami as a 23-phase FSM that time-shares one 384×384 SignUU multiplier (Coq spec for `instr_chsh_lassert` is single-step; the multi-cycle execution is a Kami-implementation detail, invisible to the spec, same pattern as `instr_lassert`). With DSP inference disabled in yosys (`-nodsp`), the design maps to ≈151K LUT6 against K325T's 203K budget and routes cleanly (router2 converges at zero overuse, max frequency 49.33 MHz against the 12 MHz target). The CI `fpga-bitstream` job has produced a real ≈11.4 MB `.bit` file end-to-end through yosys → nextpnr-xilinx → fasm2frames → xc7frames2bit, loadable on the Genesys 2 with `openFPGALoader --board genesys2 build/thiele_xc7k325t.bit`. See [fpga/run_synthesis_xc7.sh](fpga/run_synthesis_xc7.sh) and the `chsh_lassert_fsm` rule in [coq/kami_hw/ThieleCPUCore.v](coq/kami_hw/ThieleCPUCore.v).
- The Bekenstein/Landauer bridges are motivation, explicitly labeled as such in the monograph.

## The verifier corollary

Step 3 says classical computation is the substrate's forgetful projection. Run that through verifier theory and the same projection produces a verification impossibility.

A verifier whose transcript is `list StrictClassicalState` — the strict-shadow trace — cannot soundly decide a claim that depends on μ. The two single-step witnesses from the Core Proof project to the same classical trace; one satisfies the μ=1 claim, one does not. Soundness forces the claim to hold for every state that could explain the transcript, including the one where it fails. Completeness forces acceptance on the honest run. Both bars cannot be cleared. The bare-setting impossibility is `bare_setting_no_sound_complete_verifier`, in [coq/VerifierImpossibility.v](coq/VerifierImpossibility.v).

Three structurally distinct ways to clear both bars, each with a concrete sufficient verifier in the kernel:

- **Substrate** — the transcript carries the full `VMState`; the verifier reads `vm_mu` directly. `substrate_escape_succeeds`, in [coq/VerifierEscape_Substrate.v](coq/VerifierEscape_Substrate.v).
- **Hardness** — the transcript carries an unforgeable commitment; the verifier accepts under a hardness hypothesis. `hardness_escape_succeeds`, in [coq/VerifierEscape_Hardness.v](coq/VerifierEscape_Hardness.v).
- **Interaction** — the verifier challenges the prover for a response that pins the claim. `interactive_escape_succeeds`, in [coq/VerifierEscape_Interaction.v](coq/VerifierEscape_Interaction.v).

The substrate channel is the option the structural axis makes available. The other two are what classical cryptography and complexity already use. The trichotomy is closed at the bottom by `V_does_not_factor_through_classical` in [coq/VerifierExhaustiveness.v](coq/VerifierExhaustiveness.v): any sound + complete verifier on the μ-sensitive claim, over any transcript type, cannot be a function of the transcript's classical projection. Verification must access non-classical structure. The three escapes are three concrete ways to expose it; the theorem is blunt about it — there's no fourth way, exposure is the price of admission.

## Clarification: simulation vs. substrate

A common reading is that A2 can be enforced in software on a TM, so the substrate distinction is a hardware/software boundary rather than a fundamental one. That reading conflates simulation with substrate. The distinction is one sentence:

**A Turing machine cannot refuse to execute a buggy A2-simulator. A Thiele substrate cannot execute one.**
Load a Thiele simulator onto a TM with a bug: a program that certifies without incrementing μ. The TM runs it faithfully. Its step rule has no field for A2, so it cannot detect the bug; it computes whatever you wrote, A2-respecting or not. Load the same buggy program onto a Thiele substrate. The step rule traps. A2 is not interpreted by the simulator and could be skipped: it is the transition law itself. The TM is structurally incapable of refusal because its step rule has nothing to refuse on. The substrate is structurally incapable of execution because its step rule has A2 built in.

That is the difference between simulating a substrate and being a substrate. Subsumption is a step-rule claim, not a software-layer claim. "Thiele is simulable on a TM" is true and is not the question. "Thiele's step rule can be written down on a TM" is the question, and the answer is no.

## In one minute

The four steps above are mechanized by the following operational facts:

- `mu` starts at zero and never decreases.
- Certification instructions increase `mu`.
- Reversible structural bookkeeping can be zero-cost in the Bennett model.
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
records 3,823 addressable theorems probed and no user/project-local axiom
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
| Physics closure | Locality, `mu` monotonicity (mu never decreases under any step), causality, and discrete curvature identities are formalized as VM-level consequences or named bridges. | [PhysicsClosure.v](coq/kernel/curvature/PhysicsClosure.v), [EinsteinEmergence.v](coq/kernel/curvature/EinsteinEmergence.v), [PhysicsConditionalClosure.v](coq/PhysicsConditionalClosure.v) |
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
von Neumann CPU, every CPU on every desk: each names one thing, viewed with
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
assumption receipt reports 3,823 addressable theorems probed and no
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

The VM exposes 51 opcodes total: 47 are synth-realized (bisimulation-proven against the Kami model and carried through to the FPGA bitstream) and 4 are Q_{1+AB} cert-opcodes that live in the Kami HW abstraction with kernel-equivalence proven but are excluded from the synthesized Verilog by silicon budget. They contribute the OCaml/RTL parity tests' tolerated slack of 4 (theorem `rtl_coverage_partition`: 37 + 10 + 0 = 47). The 47 synth-realized opcodes fall into six families.

| Family | Examples | Cost behavior |
|---|---|---|
| Partition and module structure | `PNEW`, `PSPLIT`, `PMERGE`, `PDISCOVER` | Programmer-declared, with zero-cost reversible structure supported by the model. |
| Logic and certification | `LASSERT`, `LJOIN`, `MDLACC` | `LASSERT` includes formula-length, entropy, and certification terms. |
| Memory, ALU, control flow | `LOAD`, `STORE`, `ADD`, `JUMP`, `HALT` | Classical compute surface. |
| Witness, tensor, cert flags | `CHSH_TRIAL`, `CERTIFY`, `REVEAL`, `TENSOR_SET`, `TENSOR_GET` | Certification/revelation instructions carry positive cost floors. |
| Categorical morphisms | `MORPH`, `COMPOSE`, `MORPH_ID`, `MORPH_ASSERT` | Morphism assertions are certification-bearing. |
| CHSH-aware certification | `CHSH_LASSERT` | Kernel-level column-contractivity check on `vm_witness` buckets. Decidable integer-arithmetic check; success ⇒ NPA-PSD via the bridge theorem [`chsh_lassert_no_trap_implies_quantum_realizable`](coq/kernel/quantum/QuantumPartitionPSD.v). Cost `S(mu_delta) ≥ 1` regardless of outcome (cert-setter discipline). |

The 4 Q_{1+AB} opcodes (`instr_chsh_lassert_1ab*`) extend `CHSH_LASSERT` with the Q_{1+AB} moment-matrix family. They are defined in the Kami HW abstraction with kernel-equivalence proven (`coq/kami_hw/Abstraction.v`, `EmbedStep.v`) and run on the OCaml/Python VM, but they are excluded from the synthesized Verilog because the base `CHSH_LASSERT` 23-phase FSM already uses ~74% of the K325T's LUTs and the silicon budget cannot absorb four more wide-arithmetic FSMs (silicon, not semantics). The substrate claim doesn't require them.

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
  title        = {The Thiele Machine: A Computational Model with Explicit Structural Cost},
  author       = {Thiele, Devon},
  year         = {2026},
  version      = {2.0.1},
  doi          = {10.5281/zenodo.17316437},
  publisher    = {Zenodo},
  howpublished = {\url{https://doi.org/10.5281/zenodo.17316437}}
}
```

## Contact

To confirm, refute, build on, or point out what's wrong: thethielemachine@gmail.com,
or open an issue at [github.com/sethirus/The-Thiele-Machine](https://github.com/sethirus/The-Thiele-Machine).

## License

Apache 2.0. See [LICENSE](LICENSE).
