# The Thiele Machine

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17316437.svg)](https://doi.org/10.5281/zenodo.17316437)
[![Latest release](https://img.shields.io/github/v/release/sethirus/The-Thiele-Machine?label=release)](https://github.com/sethirus/The-Thiele-Machine/releases/latest)
[![CI](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml/badge.svg)](https://github.com/sethirus/The-Thiele-Machine/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Coq](https://img.shields.io/badge/Coq-0%20project--local%20axioms-EF4135?logo=coq&logoColor=white)](coq/)
[![Inquisitor](https://img.shields.io/badge/Inquisitor-0%20findings-brightgreen)](scripts/inquisitor.py)
[![RTL bisimulation](https://img.shields.io/badge/RTL%20bisimulation-47%2F47%20Qed-orange)](coq/kami_hw/GraphReconstructionBridge.v)

**I didn't invent a machine. I found one.**

That is how I see this work. I think there is structure here that our usual picture of computation leaves out, and I built a machine to put that conviction on the table.

A computation gives you an answer. What did it establish on the way there? Which distinctions did it keep? What did it cost to establish them? I want those questions inside the mathematics, where somebody can take the argument apart and check it.

Certification is one point I could pin down. There is more here than one point, and I am not done looking. The Thiele Machine carries structural state, a cost ledger, and rules for particular events. I wrote the definitions, built the executable machine, and proved what happens when you throw some of that information away.

I call what remains a **shadow**. For the projections in the proofs, the blindness is real: different executions become indistinguishable, and no clever decoder can recover a distinction the observation has erased. Keep the full information in another encoding and you can recover it. That makes the question sharper: what should an account of computation keep?

I think this reaches further than a useful accounting machine. I think there is something foundational here. That is my conviction, and the larger argument is still mine to earn. The proofs already give you something concrete to challenge: accounting laws, pricing results, structural separation, certificate checks, and implementations you can run.

## Run it. Don't take my word.

I don't trust my own eye to catch a gap in an argument I want to believe, so I
made the machine check the whole thing. You shouldn't trust me either. Run it.
Coq 8.18+ and Python 3, clean checkout:

```bash
make verify        # about ten seconds
make verify-research  # observation policies, event floors, and descent from traces
```

No Coq where you are? Most review environments, laptops and LLM sandboxes
alike, have none, and the argument doesn't get to hide behind a toolchain.
There is a tier for that: Python's standard library and nothing else.

```bash
python3 minimal/nofi_demo.py   # exhaustive sweeps + measured algorithms against the cost floor; exits 0
python3 -c "import json; d=json.load(open('artifacts/print_assumptions_all_proofs.json')); print(d['summary'])"
```

The second command prints the committed assumption receipt: 4,028 theorems
probed, zero *project-local* axiom findings. The badge says project-local, and
that is the precise claim: it is not "zero axioms". 2,979 of those theorems are
closed under the global context outright; the remaining **1,049 lean on four Coq
standard-library axioms**: `ClassicalDedekindReals.sig_not_dec`,
`ClassicalDedekindReals.sig_forall_dec`, dependent functional extensionality,
and `Classical_Prop.classic`.
Those library assumptions are disclosed in the receipt; what is zero is axioms *I* wrote.
Regenerate the receipt yourself with `make assumption-receipt`. **The output of
these two commands is the ground floor for any review, human or AI. An
assessment without it is an assessment of the prose, not of the repository.**

`make verify` compiles [minimal/MuCore.v](minimal/MuCore.v): a minimal instance of the cost and projection arguments
in one file, standard library only, nothing of mine to import. A machine state
is the classical part you already know, memory and registers and a program
counter, plus two fields this bare configuration omits: a cost ledger μ, and a bit that says
*certified*. One law, called A2: any single step that flips that bit from false
to true costs at least 1, charged right there in the step, not in some checker
you could skip. Ten theorems fall out of that, and every one ends with `Print
Assumptions` reporting `Closed under the global context`. Zero axioms. Zero
`Admitted`. If a theorem were leaning on a hidden assumption, that line would
rat it out and `make verify` would stop. It doesn't.

It compiles [minimal/Napkin.v](minimal/Napkin.v) too: the three-line napkin argument written out as seven theorems, each closing the same way, zero axioms. The napkin doesn't just hold; it compiles.

Then it runs [minimal/nofi_demo.py](minimal/nofi_demo.py), which rebuilds the
quantitative floor with none of my code anywhere near it. The examples compare finite-map image sizes and query costs under explicit models; they do not measure physical erasure or derive the VM cost law from Landauer. Binary search rides it at 100%
efficiency, linear scan pays fifty times over for the same answer, and nothing
beats it. The number comes out identical whoever runs it. That's the point of
handing you a thing that runs instead of a thing to believe.

The full kernel includes these arguments, additional structural results, and the execution model. MuCore's
header maps each minimal theorem to its full-kernel counterpart, and the
[Formal Spine](#formal-spine) table maps every load-bearing claim to its file.

## The argument, formally

1. **A local law constrains admissible executions.** For any `CertificationSystem`, A2 requires positive instruction cost on a false-to-true transition of its designated predicate. `universal_nfi_any_substrate` proves the corresponding trace-level floor. The state space and predicate are abstract; the VM's `vm_certified` field is one instance.
2. **Pricing adequacy can be characterized.** `CommitmentPredicateAdequacy.v` proves which local charged-event predicates cover certification flips. Requiring both the floor and no overcharge *relative to flip count* characterizes exact unit event pricing. For a finite family of unit event floors, the least joint charge is one whenever any event fires. Several events can share that unit; independent coordinates alone do not force additive charges. This does not derive the choice of event or the entire VM cost schedule from A2.
3. **Selected projections lose relevant distinctions.** The receipt and separation theorems exhibit equal observations with different ledgers, certification values, or graph structure. No decoder of those observations can recover the differing property on every state. The general condition is exact: the query must be constant on each observation class. Given a representative of every class, that condition also constructs a decoder. It applies to arbitrary queries, including ones unrelated to certification.
4. **The construction supports further mathematics and implementations.** Ledger uniqueness follows for a fixed schedule and initial value. `thiele_trace_fold_initial` gives unique instruction-list evaluation from a chosen basepoint; evaluation defines a unique target value per reachable VM state exactly when equal VM outcomes give equal target outcomes. Constructing a reachable simulation also takes representative traces and certification agreement. An A2 target retaining full instruction history can fail this condition even when certification agrees exactly. Quantum certificate algebra, compiler results, and hardware commutation have their own explicit contracts.

The VM realizes these laws. Generic `CERTIFY` sets a flag and charges for doing so; it checks no proposition. `MORPH_ASSERT` checks morphism existence and uses property text as a checksum label; it does not interpret an arbitrary proposition or validate its certificate string. `CHSH_LASSERT` has a separate soundness theorem for its restricted PSD test. Payment and semantic truth must be assessed separately.

The mathematical [elliptope completion and gate](coq/kernel/quantum/ElliptopeGate.v) extend beyond the runtime check's fixed orthogonal slice. Binding that completion gate into the executable ISA remains open engineering. The Coq hardware model has full-state trace commutation under `WFDrivenRun`, the preconditions of the actual executed run; generated RTL retains its named compiler/backend trust boundary.

## The verifier corollary

For the selected strict-shadow transcript, the witness collision yields a verification impossibility.

A verifier whose transcript is `list StrictClassicalState`, the strict-shadow trace, cannot soundly decide a claim that depends on μ. The two single-step witnesses from the Core Proof project to the same classical trace; one satisfies the μ=1 claim, one does not. Soundness forces the claim to hold for every state that could explain the transcript, including the one where it fails. Completeness forces acceptance on the honest run. Both bars cannot be cleared. The bare-setting impossibility is `bare_setting_no_sound_complete_verifier`, in [coq/VerifierImpossibility.v](coq/VerifierImpossibility.v).

Three sufficient constructions are formalized under their respective premises; the hardness construction has the weaker soundness guarantee stated in its theorem:

- **Substrate**: the transcript carries the full `VMState`; the verifier reads `vm_mu` directly. `substrate_escape_succeeds`, in [coq/VerifierEscape_Substrate.v](coq/VerifierEscape_Substrate.v).
- **Hardness**: the transcript carries an unforgeable commitment; the verifier accepts under a hardness hypothesis. `hardness_escape_succeeds`, in [coq/VerifierEscape_Hardness.v](coq/VerifierEscape_Hardness.v).
- **Interaction**: the verifier challenges the prover for a response that pins the claim. `interactive_escape_succeeds`, in [coq/VerifierEscape_Interaction.v](coq/VerifierEscape_Interaction.v).

The substrate channel is the option the structural axis makes available. The other two are what classical cryptography and complexity already use. The bottom of the trichotomy is `V_does_not_factor_through_classical` in [coq/VerifierExhaustiveness.v](coq/VerifierExhaustiveness.v), and its exact scope matters: **given a transcript type whose classical projection collides two witnesses** (`proj t_A = proj t_B`, supplied as a hypothesis), no sound + complete verifier on the μ-sensitive claim can be a function of that projection. Where the collision exists, verification must access non-classical structure, and the three escapes are three concrete ways to expose it.

The collision is a hypothesis, not a conclusion: on a transcript rich enough to separate the witnesses it is unsatisfiable, and the statement is vacuous there. So the trichotomy is closed at the bottom *where the projection collides*, which is the case the argument is about. "There is no fourth way" is the informal reading of that, not a theorem. Full meta-theoretic exhaustiveness, whether substrate, hardness, and interaction partition the space of non-classical structures, sits outside Coq's object-level type theory. This file reduces that meta-question to the structural-enrichment question; it does not settle it, and the file header says so.

## Observation, enforcement, and representation

A transition law can enforce an invariant while exposing a projection that omits its evidence. Conversely, storing a ledger does not establish that all transitions maintain it correctly. The relevant comparison specifies the permitted transitions, the observation interface, and the trusted implementation.

Even a reset can preserve information in a larger state: recording the previous state in a history list makes each fixed-instruction transition injective. A program counter collapsing to one therefore does not establish global erasure or a physical dissipation bound.

Conventional encodings can represent the full state, and particular machines can enforce invariants through their prescribed transitions. Turing equivalence concerns computational power; it neither supplies nor forbids the particular accounting discipline. In this document, a ledgerless shadow means the specified observation or fragment with those distinctions omitted.

The concrete kernel permits zero-cost structural operations as well as paid events. It therefore does not prove that every change of observable has positive cost. Its ledger starts at zero and sums the declared schedule; selected certification operations have mandatory positive floors.

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
records 4,028 addressable theorems probed and no user/project-local axiom
findings in the committed assumption scan.

## Beyond the minimal witness

The minimal witness demonstrates a collision under a projection. The abstract accounting theorem ranges over arbitrary state and instruction types, and pricing adequacy classifies local rules relative to the designated event. The broader development also studies structural entitlement, graph operations, verifier interfaces, quantum certificate algebra, and realizations in software and hardware.

These results motivate studying the framework; they do not eliminate its modeling choices. The verifier impossibility follows from the observation collision. The Python examples check finite combinatorial and algorithmic instances. The CHSH soundness bridge uses additional algebra. Their combination is not an independent derivation of physical A2.

The pointer-observable models investigate why particular commitment events are recorded by other parties. The models and their counterexamples are part of the research argument. They do not establish that forgery resistance forces metering, nor that all public verifiability implies actual record storage by every observer. Certification remains one worked example, and a universally forced choice of priced events remains open.

## Formal Spine

These are the load-bearing formal claims. The fourth column is the artifact
that refutes the row, each one constructible in Coq or Python, no philosophy
required.

| Claim | Meaning | Main proof files | Refute it |
|---|---|---|---|
| Minimal core | The whole substrate claim in one self-contained file: A2, the cost floor, receipt separation, and the classical machine as the zero-cost fragment. Zero axioms, compiles in seconds. Run `make verify`. | [minimal/MuCore.v](minimal/MuCore.v) | An `f : shadow -> nat` with `f (strict_shadow s) = st_mu s` for all `s`; Coq accepts it where `no_mu_oracle` proves none exists. |
| Receipt theorem | `mu` is not determined by strict classical state. | [ReceiptTheorem.v](coq/ReceiptTheorem.v), [NecessityOfMuLedger.v](coq/NecessityOfMuLedger.v) | An `f : StrictClassicalState -> nat` with `f (strict_shadow s) = vm_mu s` for every `VMState`; `ReceiptTheorem` falls. |
| No Free Insight | Certification from an uncertified state requires positive `mu`. | [AbstractNoFI.v](coq/kernel/nfi/AbstractNoFI.v), [NoFreeInsight.v](coq/kernel/nfi/NoFreeInsight.v) | A VM step taking `vm_certified` false→true at instruction cost 0; `no_free_certification_certified` falls. |
| Universal cost floor | Any substrate with a cert-flip cost floor satisfies the same no-free-certification result. | [UniversalCertificationCost.v](coq/kernel/nfi/UniversalCertificationCost.v) | A `CertificationSystem` trace from uncertified to certified with `cs_total_cost = 0`; `universal_nfi_any_substrate` falls. |
| `mu` initiality | Any zero-starting, instruction-consistent, monotone ledger equals `mu` on reachable states. | [MuInitiality.v](coq/kernel/mu_calculus/MuInitiality.v) | A `CostFunctional` (zero-starting, instruction-consistent, monotone) differing from `mu` on a reachable state; `mu_is_universal` falls. |
| Honest cost tracking | A2 is a strict well-formedness condition: systems without it admit free certification. | [HonestCostTracking.v](coq/kernel/nfi/HonestCostTracking.v) | A `CertificationSystem` (A2 in scope) with a non-empty cert-flip trace at total cost 0, or a proof that every `CostBearingSystem` satisfies A2; `honest_cost_tracking_strict_restriction` falls either way. |
| Verification-cost separation | Slice coherence is checked by the kernel discipline; unconstrained traces require positional inspection. | [VerificationCostSeparation.v](coq/kernel/nfi/VerificationCostSeparation.v) | A correct `PositionalVerifier` for free-world traces that skips inspecting some cert position; `free_world_honesty_verifier_must_inspect_every_cert_position` falls. |
| `mu` hierarchy | Level-`k` certification requires at least `k` units of `mu`; no fixed budget covers every level. | [MuHierarchyTheorem.v](coq/kernel/mu_calculus/MuHierarchyTheorem.v) | A level-`k` certification trace with total `mu` < `k`; `level_k_certification_cost_floor` falls. |
| Structural advantage | The factored-SAT lower bound is proved for the non-adaptive model; the thermodynamic parsing gap is proved separately. | [NonAdaptiveLowerBound.v](coq/kernel/nfi/NonAdaptiveLowerBound.v), [ThermodynamicStructuralAdvantage.v](coq/kernel/nfi/ThermodynamicStructuralAdvantage.v) | A non-adaptive solver deciding the factored instance while probing fewer than `2^n` assignments; `non_adaptive_sat_lower_bound` falls. |
| Algebraic Tsirelson | The CHSH bound follows from rational polynomial constraints by Coq arithmetic. | [AlgebraicCoherence.v](coq/kernel/category/AlgebraicCoherence.v), [QuantumPartitionPSD.v](coq/kernel/quantum/QuantumPartitionPSD.v) | An `algebraically_coherent` correlator with `S² > 8`; `algebraically_coherent_tsirelson_general` falls. |
| Physics closure | Locality, `mu` monotonicity (mu never decreases under any step), causality, and discrete curvature identities are formalized as VM-level consequences or named bridges. The flat/vacuum EFE closure (`full_efe_uniform_two_vertex`) is a discrete-geometry identity (both sides vanish), not a derivation of general relativity. | [PhysicsClosure.v](coq/kernel/curvature/PhysicsClosure.v), [EinsteinEmergence.v](coq/kernel/curvature/EinsteinEmergence.v), [PhysicsConditionalClosure.v](coq/PhysicsConditionalClosure.v) | A state `s` and instruction `i` with `(vm_apply s i)` paying less than `instruction_cost i` in `mu`, or a step writing outside its target module; `vm_apply_mu` (or the locality lemma) falls. |
| Intermediate hardware-model correspondence | The load-bearing theorem is [`driven_step_wf`](coq/kami_hw/GraphReconstructionBridge.v#L3872): for every instruction, the abstracted Kami hardware step equals `vm_apply` under `WFDrivenPrecondition`: `abs_full_snapshot (kami_step ks i) = vm_apply (abs_full_snapshot ks) i`, discharged by per-opcode lemmas. CHSH_LASSERT's Kami snapshot semantics inspect the same witness buckets through the same check function, matching VM-step exactly via `abs_phase1`. (The bookkeeping identity `37 + 10 + 0 = 47` is recorded separately as `rtl_coverage_partition`; it is Peano arithmetic and proves nothing about opcodes, so cite `driven_step_wf`, not the partition.) | [GraphReconstructionBridge.v](coq/kami_hw/GraphReconstructionBridge.v#L3872), [coq/kami_hw](coq/kami_hw) | A cosim input on which synthesised RTL diverges from the Kami step for any synth-realised opcode (run `tests/test_verilog_cosim.py`); `rtl_step_correct` is violated empirically. |
| CHSH ↔ NPA-PSD bridge | A successful `CHSH_LASSERT` step entails the witness-derived NPA moment matrix is PSD. | [chsh_lassert_no_trap_implies_quantum_realizable](coq/kernel/quantum/QuantumPartitionPSD.v), [column_contractive_check_witness_sound](coq/kernel/nfi/MuLedgerQuantumBridge.v) | A successful `CHSH_LASSERT` step whose witness-derived moment matrix is not PSD; `chsh_lassert_no_trap_implies_quantum_realizable` falls. |
| Elliptope completion | The completion-based PSD correlator model (physical quantum identification uses external mathematics): every LHV correlator inside (deterministic + n-ary mixtures), Tsirelson `S² ≤ 8` for the whole set, PR box excluded, classical ⊂ elliptope strict. | [ElliptopeCompletion.v](coq/kernel/quantum/ElliptopeCompletion.v) | An elliptope-realizable tuple with `S² > 8` (`elliptope_tsirelson` falls), a sign pattern whose completed Gram form goes negative (`deterministic_strategy_elliptope` falls), or a PSD completion of the PR box (`pr_box_not_elliptope` falls). |
| Elliptope gate | Decidable Z-arithmetic membership check, two branches (fraction-free Sylvester for strict interior, rational LDL^T certificate reaching singular and boundary completions); passing provably entails elliptope membership; the µ=0 tightness witness, (1,0,1,0), and the on-Tsirelson-curve Pythagorean point (3/5,4/5,4/5,−3/5) accepted by computation; the PR box never accepted. | [ElliptopeGate.v](coq/kernel/quantum/ElliptopeGate.v) | Inputs making `elliptope_check_full` return true with correlators outside the set; `elliptope_check_full_sound` falls. |
| Pointer-observable criterion | Observer ecosystems, redundant records, and uniqueness relative to rivals, with five minimal model instances. Event and observer choices remain modeling inputs. | [PointerObservable.v](coq/kernel/frontier/PointerObservable.v), [PointerObservableReductions.v](coq/kernel/frontier/PointerObservableReductions.v) | An independently justified ecosystem where the criterion fails would challenge its proposed applicability. |
| Counterexamples to stronger criteria | Abstract observer models refute implications from forgery resistance to metering or record proliferation. The remaining public-record criterion is a proposal: public verifiability alone does not imply actual storage. | [PointerObservableCounterexamples.v](coq/kernel/frontier/PointerObservableCounterexamples.v) | Check the observer and security abstractions against their intended applications; these model proofs do not validate deployed protocols. |
| PoS finality reduction | Nothing-at-stake is the kernel's free forgery: a zero-stake-at-finalize gadget admits no A2 field, and any slashing gadget (finalize risks ≥ 1) pays the finality floor: `universal_nfi_any_substrate` instantiated. | [PoSFinality.v](coq/kernel/reductions/PoSFinality.v) | A zero-stake-at-finalize gadget that admits an A2 proof, or a slashing gadget with a finalizing trace of total stake-at-risk 0; `nothing_at_stake_is_free_forgery` or `slashing_finality_floor` falls. |
| Gas-metering reduction | A gas schedule satisfies the commitment floor + no-overcharge iff its charging predicate is the commitment predicate with exact unit pricing; the kernel VM itself inhabits the class. | [GasMetering.v](coq/kernel/reductions/GasMetering.v) | A `GasSchedule` satisfying floor + no-overcharge whose charge predicate differs from cert-flip on some reachable step; `gas_schedule_exactness` falls. |
| TEE attestation reduction | Sound+complete attestation of a μ-dependent claim cannot factor through the bare transcript; the replay attack is the two-preimage witness; exposing the measurement register restores a sound, complete, unit-cost verifier. | [TEEAttestation.v](coq/kernel/reductions/TEEAttestation.v) | A sound+complete attestation verifier `V : TEEReport -> bool` with a proof of `factors_classical report_projection V`; `attestation_cannot_factor_through_bare_transcript` falls. |
| Transparency-log reduction | The CT design is the hardness escape: log-backed transcripts admit a unit-cost grounded verifier while the log-free equivalent is impossible; split-view is the impossibility's witness pair. | [TransparencyLog.v](coq/kernel/reductions/TransparencyLog.v) | A sound+complete log-free (bare-transcript) verifier with the same soundness target; `log_free_verifier_impossible` falls. |
| Proof-carrying reduction | Rounds restore sound, complete, unit-cost verification of the μ-claim; level-`k` certification costs ≥ `k` μ (events only, not gate counts or circuit size), with tightness witnessed. | [ProofCarryingVerifier.v](coq/kernel/reductions/ProofCarryingVerifier.v) | A level-`k` certified trace with total μ < `k`, or a sound+complete zero-round bare verifier; `level_k_verification_floor` or `bare_pcc_impossible` falls. |

The audited claim ledger is [coq/kernel/aggregators/MasterSummary.v](coq/kernel/aggregators/MasterSummary.v).
Its generated closure receipt is
[artifacts/master_summary_open_obligations.json](artifacts/master_summary_open_obligations.json).

## What is established and what remains open

| Result | Scope |
|---|---|
| Universal certification floor | Every system satisfying the specified A2 premise. |
| Exact event pricing | Relative to certification-flip count and the stated local-pricing interface. |
| Ledger uniqueness | Given the instruction schedule and zero initial value, on reachable states. |
| Trace-fold initiality | Unique evaluation of instruction lists; uniqueness of existing compatible state maps is separate. |
| Irrecoverability and verifier separation | For projections/transcripts that identify witnesses disagreeing on the queried property. |
| Quantum certificate soundness | Specified slice or completion PSD conditions; not physical entanglement generation. |
| Hardware trace commutation | The Coq hardware model under `WFDrivenRun`; downstream compiler/RTL trust remains explicit. |
| Physical interpretation | Open. `F1_physical_premises_incompatible` proves the current full-ISA F1 premise pair has no instance. |

The classical embedding results describe the formal fragments and simulation contracts in their cited files. Multiple preimages rule out recovering the original full state from the projection. They do not rule out a section that chooses default metadata, or a different encoding that preserves the metadata.

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
minimal/                 the substrate claim in one self-contained Coq file + clean-room demo
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

Clone with the vendored Coq libraries. The hardware-bridge proofs depend on
**Kami** and **bbv**, which are git submodules; without them `make coq-gate`
fails rather than skipping:

```bash
git clone --recurse-submodules https://github.com/sethirus/The-Thiele-Machine.git
# already cloned without --recurse-submodules:
git submodule update --init --recursive
```

Verify the core claim first (Coq 8.18+ and Python 3 only):

```bash
make verify
```

Then the full development environment:

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
`verilator`, and/or `yosys`). The exact versions are the ones CI earns its
badges with: plain apt on `ubuntu-latest`, currently Ubuntu 24.04, which
ships Coq 8.18.0.

```bash
sudo apt-get install -y coq coinor-csdp ocaml ocaml-findlib   # proof gates
sudo apt-get install -y iverilog verilator yosys              # RTL gates only
```

`coinor-csdp` is not garnish: the algebraic Tsirelson theorem closes its
sum-of-squares certificate through `psatz`, and `psatz` asks CSDP for the
certificate.

### Full proof build (the `coq-gate`)

The project uses native tools and repository sources. Docker, container images,
and a container daemon are not part of the build or review workflow.

For a complete source-only rebuild with dependency checking:

```bash
python3 scripts/reproduce_coq.py --jobs 1
```

This copies only source/configuration into a fresh directory under
`artifacts/reproduction/`, builds the vendored bbv and Kami libraries plus the
project (including the pinned MM2 dependency), runs the review probes, and
checks the selected compiled libraries with `coqchk`. It records input hashes,
native tool versions, commands, individual exit codes and raw logs. It does not
install libraries globally or download anything. The native prerequisites above
must already be available; this is a source-contained project, not a bundled OS
or compiler distribution. See [native reproduction](docs/REPRODUCTION.md).

For incremental development in the checkout:

```bash
export COQPATH="$PWD/vendor/bbv/src:$PWD/vendor/kami"
make -C vendor/bbv
make -C vendor/kami
make coq-gate
```

`COQPATH` selects the repository libraries, so no global `make install` is
needed. `make verify` and `pytest` alone do not compile the full Coq corpus.

The actual CPU proof surface includes executable semantics for all 12 Kami rules, finite selected execution traces, reset facts and preservation of register names and kinds (`CoreRules`, `CoreExecution`, `CoreTyping`, `DispatchReset`). Full value/resource invariants, abstract retirement correspondence and compiler semantic preservation remain separate obligations. [Assurance and scope](docs/ASSURANCE.md) identifies each boundary.

The unbounded VM has a checked 122-instruction self-interpreter for twelve arithmetic and control instructions over four guest registers. Program and input vary as executable data. Its contracts cover positive host simulation, both directions of result correctness, malformed code and divergence; guest structural fields remain unchanged. [VM contracts](docs/VM_CONTRACTS.md) records the exact fragment and observations.

For that model, the checked Rice reduction proves undecidability for extensional predicates separating the divergent program from a well-formed program, including halting on zero and returning zero. Guest-program deciders are covered. It supplies no internal recursion theorem and does not discharge the conditional bounded VM diagonal. [VM contracts](docs/VM_CONTRACTS.md) records the assumptions and checked results.

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
| `make verify` | One-command verification of the core claim (minimal Coq core + clean-room measurement). |
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
assumption receipt reports 12,336 addressable theorems probed and no
user/project-local axiom findings. The split: 5,520 close under the global
context outright, and the remaining 6,816 lean only on Coq-stdlib axiom
families: `functional_extensionality_dep` (6,526), the classical-reals pair
`sig_forall_dec` (1,010) and `sig_not_dec` (277), and `classic` (67). Those
families enter through the real-number and physics layers; the minimal core
uses none of them. "Zero axioms" here means zero project-local axioms, the
same convention the monograph uses, and the receipt is what enforces it.
A test ([tests/test_proof_hygiene_numbers.py](tests/test_proof_hygiene_numbers.py))
holds this paragraph to the committed artifact, number by number.

Run the hygiene pass directly:

```bash
python scripts/inquisitor.py
```

Run the stronger formal gate:

```bash
make proof-undeniable
```

## ISA Summary

The VM exposes 51 opcodes total: 47 are synth-realized (implemented in the generated RTL; full physical retirement refinement remains open) and 4 are Q_{1+AB} cert-opcodes that live in the Kami HW abstraction with kernel-equivalence proven but are excluded from the synthesized Verilog by silicon budget. They contribute the OCaml/RTL parity tests' tolerated slack of 4 (theorem `rtl_coverage_partition`: 37 + 10 + 0 = 47). The 47 synth-realized opcodes fall into six families.

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
| [coq/PhysicsConditionalClosure.v](coq/PhysicsConditionalClosure.v) | VM accounting results and a conditional Tsirelson theorem from a full PSD completion. |
| [TECHNICAL_DISCLOSURE.md](TECHNICAL_DISCLOSURE.md) | Prior-art disclosure for the public technical concepts. |
| [PATENT_PLEDGE.md](PATENT_PLEDGE.md) | Non-assertion pledge for repository concepts. |

## IP And Prior Art

The software in this repository is Apache 2.0 licensed, including the license's
patent grant for contributor-owned claims. [PATENT_PLEDGE.md](PATENT_PLEDGE.md)
adds an explicit non-assertion commitment for the concepts in this repository.

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
  version      = {3.2.2},
  doi          = {10.5281/zenodo.17316437},
  publisher    = {Zenodo},
  howpublished = {\url{https://doi.org/10.5281/zenodo.17316437}}
}
```

## Contact

To confirm, refute, build on, or point out what's wrong: thethielemachine@gmail.com,
or open an issue at [github.com/sethirus/The-Thiele-Machine](https://github.com/sethirus/The-Thiele-Machine).
A submission that names a theorem gets, within 14 days, one of exactly two
replies: "correct, fixing it," or the line where the construction fails.

The kernel's machine semantics are feature-frozen at v3.0: no new opcodes, no
step-relation changes, no cost-law changes. Accepted changes: refutation
fixes, hygiene, toolchain compatibility, and machine-untouched
characterization tiers over the frozen semantics (v3.1.0's elliptope gate and
pointer-observable criterion are this kind: correlator-level and
frontier-criterion theorems that leave the step relation and cost law
untouched). New machine features belong in new repositories citing this one.

## License

The software is licensed Apache-2.0; see [LICENSE](LICENSE). The monograph and
distillation are licensed CC-BY-SA-4.0. That split is intentional: the code
carries a patent grant, the writing carries share-alike.
