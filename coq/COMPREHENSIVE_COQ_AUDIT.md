# Comprehensive Coq proof audit (full tree)

_Audit date: November 24, 2025. Toolchain installed via `apt-get install -y coq` (8.18.0)._ 

## Commands executed
- `make -C coq core` — passed; exercises `_CoqProject` core targets and archived interpreter dependencies.
- `make -C coq optional` — passed; compiles CatNet, isomorphism, P=NP sketch, Project Cerberus, Shor primitives, and VSCoq test.
- `make -C coq bridge-timed BRIDGE_TIMEOUT=300` — timed out while compiling `thielemachine/verification/ThieleUniversalBridge.v`.

## Admit/axiom inventory snapshot
- Admits: 6 total (all outside `_CoqProject`): four in `thielemachine/verification/ThieleUniversalBridge_Axiom_Tests.v` and two in
  `thielemachine/coqproofs/debug_no_rule.v`.
- Axioms: 6 total (all bridge-related): five in `thielemachine/verification/ThieleUniversalBridge.v` plus one in
  `thielemachine/verification/modular/Bridge_LengthPreservation.v`.

## Per-file analysis
Each entry notes the build tier exercised in this audit, whether the file was compiled by the commands above, and any remaining
admits or axioms.

### Root-level proofs
| File | Tier/Build status | Notes |
| --- | --- | --- |
| `coq/ThieleMap.v` | Not in audited builds | Roadmap wrapper for simulation/subsumption; no admits/axioms reported. |
| `coq/test*.v` (test, test_lia, test_rewrite_pow) | Not in audited builds | Standalone arithmetic/rewriting smoke tests; no admits/axioms flagged. |
| `coq/tmp_*.v` (tmp_bell_head, tmp_check*, tmp_dbg, tmp_ineq, tmp_mul_succ_check, tmp_pow_test, tmp_probe*) | Not in audited builds | Sandbox arithmetic/probe scripts; not part of `_CoqProject`; no admits/axioms detected. |

### Kernel
| File | Tier/Build status | Proof purpose and main results |
| --- | --- | --- |
| `kernel/Kernel.v` | Core — compiled via `make core` | Defines the kernel Turing-machine state, tape primitives, and instruction semantics, providing the executable small-step model that later correctness proofs refine. |
| `kernel/KernelTM.v` | Core — compiled via `make core` | Packages the kernel machine as a reusable Coq `TM` instance and proves the compatibility lemmas needed to run kernel programs in the generic simulator. |
| `kernel/KernelThiele.v` | Core — compiled via `make core` | Bridges the kernel TM to the Thiele encoding by constructing the concrete Thiele program and establishing that kernel instructions are faithfully mapped. |
| `kernel/VMState.v` | Core — compiled via `make core` | States the VM configuration record and proves well-formedness properties (length accounting, tape/head invariants) preserved by execution. |
| `kernel/VMEncoding.v` | Core — compiled via `make core` | Encodes VM instructions as bitstrings and proves that decoding followed by encoding is stable, enabling round-trip correctness for compiled programs. |
| `kernel/VMStep.v` | Core — compiled via `make core` | Proves the determinism and progress properties of single VM steps, tying the operational semantics to the encoding/decoding functions. |
| `kernel/SimulationProof.v` | Core — compiled via `make core` | Builds the end-to-end simulation between the abstract kernel TM and the encoded VM, showing that each kernel transition is realized by the VM trace. |
| `kernel/MuLedgerConservation.v` | Core — compiled via `make core` | Shows the `mu_cost` ledger is monotonically conserved/updated across steps and now packages the irreversible-bit lower bound as `mu_ledger_bounds_irreversible_events` plus the delta form `run_vm_irreversibility_gap` (Landauer hook). |
| `kernel/Subsumption.v` | Core — compiled via `make core` | Wraps the subsumption theorem: any kernel machine execution can be simulated by the VM without loss of observable behavior, closing the kernel correctness loop. |
| `kernel/PDISCOVERIntegration.v` | Not in `_CoqProject` | Stub integration hook for a PDISCOVER trace; currently not built but kept for future alignment with the kernel semantics. |

### Modular proofs
| File | Tier/Build status | Proof purpose and main results |
| --- | --- | --- |
| `modular_proofs/CornerstoneThiele.v` | Core — compiled via `make core` | Establishes the “cornerstone” composition lemmas showing that Thiele components compose while preserving semantics needed by higher simulations. |
| `modular_proofs/Encoding.v` | Core — compiled via `make core` | Defines the bit-level encoding of machine configurations and proves soundness of the encode/decode pipeline. |
| `modular_proofs/EncodingBounds.v` | Core — compiled via `make core` | Quantifies bounds on encoding sizes and proves they are respected through simulation steps, enabling resource-aware reasoning. |
| `modular_proofs/Minsky.v` | Core — compiled via `make core` | Formalizes the Minsky machine variant used in the modular pipeline and proves its operational semantics. |
| `modular_proofs/Simulation.v` | Core — compiled via `make core` | Connects the encoded Thiele machine to the Minsky model, proving a simulation that preserves outputs and halting behavior. |
| `modular_proofs/TM_Basics.v` | Core — compiled via `make core` | Collects reusable lemmas about Turing-machine tapes, steps, and combinators that the rest of the modular proofs import. |
| `modular_proofs/Thiele_Basics.v` | Core — compiled via `make core` | Introduces the Thiele-specific state space and proves basic invariants (tape layout, register accesses) needed downstream. |
| `modular_proofs/TM_to_Minsky.v` | Core — compiled via `make core` | Constructs the translation from the TM description to the Minsky representation and proves semantic preservation of each transition. |

### Archived interpreter dependencies
| File | Tier/Build status | Proof purpose and main results |
| --- | --- | --- |
| `../archive/research/incomplete_subsumption_proof/thieleuniversal/coqproofs/CPU.v` | Core — compiled via `make core` | Defines the universal TM CPU state/step relation used by the archived bridge and proves progress for each instruction class. |
| `../archive/research/incomplete_subsumption_proof/thieleuniversal/coqproofs/TM.v` | Core — compiled via `make core` | States the base universal TM syntax/semantics that the CPU refinement targets. |
| `../archive/research/incomplete_subsumption_proof/thieleuniversal/coqproofs/UTM_Encode.v` | Core — compiled via `make core` | Encodes UTM instructions into bit-level representations and proves decoding correctness. |
| `../archive/research/incomplete_subsumption_proof/thieleuniversal/coqproofs/UTM_Rules.v` | Core — compiled via `make core` | Lists the rule table for the universal machine and proves lookup properties needed by the bridge. |
| `../archive/research/incomplete_subsumption_proof/thieleuniversal/coqproofs/UTM_Program.v` | Core — compiled via `make core` | Builds the concrete universal program sequence and shows it satisfies the expected structural invariants. |
| `../archive/research/incomplete_subsumption_proof/thieleuniversal/coqproofs/UTM_CoreLemmas.v` | Core — compiled via `make core` | Provides supporting lemmas (tape movement, register updates) that feed into the bridge simulation. |

### Thiele machine core proofs
| File | Tier/Build status | Proof purpose and main results |
| --- | --- | --- |
| `thielemachine/coqproofs/AmortizedAnalysis.v` | Core — compiled via `make core` | Proves bounds showing Thiele program traces incur amortized linear cost in tape length and rule lookups. |
| `thielemachine/coqproofs/Axioms.v` | Core — compiled via `make core` | Collects section-local hypotheses for oracle experiments and shows the core semantics remain parametric in those assumptions. |
| `thielemachine/coqproofs/BellInequality.v` | Core — compiled via `make core` | Formalises the Bell inequality constraints used in the Thiele framework and derives the algebraic bounds on correlators. |
| `thielemachine/coqproofs/BellCheck.v` | Core — compiled via `make core` | Implements the executable Bell-inequality checker and proves it agrees with the symbolic constraints. |
| `thielemachine/coqproofs/LawCheck.v` | Core — compiled via `make core` | Provides decision procedures for legal program structure and proves their soundness against the abstract rules. |
| `thielemachine/coqproofs/PhaseThree.v` | Core — compiled via `make core` | Completes the Phase 3 pipeline, showing receipts emitted by the Thiele machine satisfy the final acceptance criteria. |
| `thielemachine/coqproofs/Bisimulation.v` | Core — compiled via `make core` | Establishes a bisimulation between two Thiele semantics presentations, proving observational equivalence. |
| `thielemachine/coqproofs/Confluence.v` | Core — compiled via `make core` | Shows the small-step semantics are confluent so execution order does not affect results of well-formed programs. |
| `thielemachine/coqproofs/EncodingBridge.v` | Core — compiled via `make core` | Relates the abstract Thiele encoding to the concrete VM encoding, proving consistent interpretation of instructions. |
| `thielemachine/coqproofs/ListHelpers.v` | Core — compiled via `make core` | Supplies list lemmas (prefix/suffix, take/drop) used throughout tape and receipt reasoning. |
| `thielemachine/coqproofs/NUSD.v` | Core — compiled via `make core` | Mechanises the NUSD (non-uniform state diagram) constructs and proves structural properties used by scheduler proofs. |
| `thielemachine/coqproofs/PartitionLogic.v` | Core — compiled via `make core` | Proves the lattice/partition logic properties underpinning the receipt separation arguments. |
| `thielemachine/coqproofs/Oracle.v` | Core — compiled via `make core` | Defines the oracle interface and proves it composes safely with the Thiele execution semantics. |
| `thielemachine/coqproofs/QHelpers.v` | Core — compiled via `make core` | Collects rational arithmetic helpers for Bell/quantum-style inequalities used elsewhere in the development. |
| `thielemachine/coqproofs/Separation.v` | Core — compiled via `make core` | Proves separation theorems ensuring independent Thiele processes can be reasoned about modularly. |
| `thielemachine/coqproofs/SpecSound.v` | Core — compiled via `make core` | Shows that the executable specification agrees with the declarative spec, yielding soundness of the implementation. |
| `thielemachine/coqproofs/StructuredInstances.v` | Core — compiled via `make core` | Builds structured program instances and proves they satisfy the preconditions of the main simulation theorems. |
| `thielemachine/coqproofs/HardwareBridge.v` | Core — compiled via `make core` | Connects RTL traces to the Thiele semantics by proving the decoder and step relation mirror the abstract machine. |
| `thielemachine/coqproofs/ThieleProc.v` | Core — compiled via `make core` | Packages Thiele programs as categorical morphisms and proves identity/composition laws via the `run_closed` semantics. |
| `thielemachine/coqproofs/HyperThiele_Oracle.v` | Core — compiled via `make core` | Describes the hyper oracle extension and proves it refines the base oracle interface without breaking semantics. |
| `thielemachine/coqproofs/HyperThiele_Halting.v` | Core — compiled via `make core` | Constructs the halting oracle witness and proves halting equivalence under the `H_correct` hypothesis. |
| `thielemachine/coqproofs/ThieleMachine.v` | Core — compiled via `make core` | States the abstract Thiele machine semantics and proves consistency of its transition system. |
| `thielemachine/coqproofs/ThieleMachineConcrete.v` | Core — compiled via `make core` | Builds the concrete VM-level Thiele machine and shows it refines the abstract model. |
| `thielemachine/coqproofs/ThieleMachineConcretePack.v` | Core — compiled via `make core` | Bundles the concrete machine with derived lemmas (determinism, progress) for downstream proofs. |
| `thielemachine/coqproofs/ThieleMachineModular.v` | Core — compiled via `make core` | Connects the modular Minsky encoding to the Thiele machine, proving module-wise correctness. |
| `thielemachine/coqproofs/ThieleMachineUniv.v` | Core — compiled via `make core` | Gives the universal Thiele machine wrapper and proves universality properties relative to the modular encoding. |
| `thielemachine/coqproofs/UTMStaticCheck.v` | Core — compiled via `make core` | Implements static well-formedness checks for UTM programs and proves the checkers are sound. |
| `thielemachine/coqproofs/Subsumption.v` | Core — compiled via `make core` | Shows the Thiele machine formally subsumes the target Turing model, completing the containment proof. |
| `thielemachine/coqproofs/Simulation.v` | Core — compiled via `make core` | Wraps the main simulation, restating no-rule invariants and showing the bridge definitions instantiate the generic proof. |
| `thielemachine/coqproofs/ThieleMachineSig.v` | Not in audited builds | Signature/interface for the Thiele machine; not compiled in this audit. |
| `thielemachine/coqproofs/HyperThiele.v` | Not in audited builds | Exploratory hyper-Thiele variant kept out of `_CoqProject`. |
| `thielemachine/coqproofs/Impossibility.v` | Not in audited builds | Notes an impossibility direction related to the Thiele constructions; outside default build. |
| `thielemachine/coqproofs/ListModules.v` | Not in audited builds | Module-list scaffolding, not exercised in the compiled targets. |
| `thielemachine/coqproofs/debug_no_rule.v` | Excluded from builds | Contains two admitted lemmas retained for experimentation. |

### Verification bridge and modular refactor
| File | Tier/Build status | Notes |
| --- | --- | --- |
| `thielemachine/verification/ThieleUniversalBridge.v` | Bridge — timed out under `make bridge-timed` | Contains five axioms for remaining FindRule checkpoints; no admits. Build blocked by archived trace replay timeout. |
| `thielemachine/verification/ThieleUniversalBridge_Axiom_Tests.v` | Not in audited builds | Test harness for bridge axioms; four admitted placeholders remain. |
| `thieleuniversal/coqproofs/ThieleUniversal.v` | Bridge tier — not reached due to timeout | Thin wrapper around simulation lemmas; admit/axiom-free but not compiled in this run because `ThieleUniversalBridge.v` timed out. |
| Modular subdirectory (`modular/Bridge_BasicLemmas.v`, `Bridge_BridgeCore.v`, `Bridge_BridgeHeader.v`, `Bridge_Invariants.v`, `Bridge_LengthPreservation.v`, `Bridge_LoopExitMatch.v`, `Bridge_LoopIterationNoMatch.v`, `Bridge_MainTheorem.v`, `Bridge_ProgramEncoding.v`, `Bridge_RegisterLemmas.v`, `Bridge_SetupState.v`, `Bridge_StepLemmas.v`, `Bridge_TransitionFetch.v`, `Bridge_TransitionFindRuleNext.v`) | Not in audited builds | Staging refactor of bridge proof. Admit-free, but `Bridge_LengthPreservation.v` retains one axiom mirroring the register-bound claim; all excluded from `_CoqProject`. |

### Optional studies (built via `make optional`)
| File | Tier/Build status | Proof purpose and main results |
| --- | --- | --- |
| `catnet/coqproofs/CatNet.v` | Optional — compiled | Models category-theoretic networks and proves associativity/identity laws for the CatNet combinators. |
| `isomorphism/coqproofs/Universe.v` | Optional — compiled | Exhibits a universe-level isomorphism and proves the forward/backward morphisms compose to identities. |
| `p_equals_np_thiele/proof.v` | Optional — compiled | Presents the P=NP sketch by encoding SAT-style gadgets in the Thiele machine and proving the reduction steps. |
| `project_cerberus/coqproofs/Cerberus.v` | Optional — compiled | Formalizes a Cerberus-inspired security protocol and proves confidentiality/integrity properties for its transitions. |
| `physics/DiscreteModel.v` | Optional — compiled | Defines a reversible lattice gas with particle-count and momentum invariants plus a transport lemma for any matching implementation. |
| `physics/DissipativeModel.v` | Optional — compiled | Supplies a dissipative lattice that erases heat in one sweep; energy is monotone and strictly drops on hot configurations. |
| `physics/WaveModel.v` | Optional — compiled | Models reversible left/right propagation on a cyclic lattice with conserved energy and a momentum-like invariant, plus an explicit inverse step. |
| `shor_primitives/Euclidean.v` | Optional — compiled | Proves correctness of the Euclidean algorithm on integers to support quantum order-finding primitives. |
| `shor_primitives/Modular.v` | Optional — compiled | Develops modular arithmetic lemmas and proves the invariants needed for Shor period computations. |
| `shor_primitives/PeriodFinding.v` | Optional — compiled | Shows the period-finding routine returns a divisor of the target order under the modular arithmetic hypotheses. |
| `self_reference/SelfReference.v` | Optional — compiled | Models abstract self-referential systems and constructively produces a dimensionally richer meta-level witness. |
| `spacetime/Spacetime.v` | Optional — compiled | Treats spacetime as a 4D system with events/worldlines and shows any spacetime self-reference requires a richer meta-level. |
| `thiele_manifold/ThieleManifold.v` | Optional — compiled | Builds an infinite-dimensional tower where each level reasons about the one below, proves self-reference is handled by lifting, and shows the π₄ projection to spacetime is lossy with positive μ-cost. |
| `thiele_manifold/ThieleManifoldBridge.v` | Optional — compiled | Instantiates the manifold with the verified Thiele machine receipts (`ThieleProc`), reuses the self-reference/meta-level machinery, and brings in the irreversibility lower bound (`thiele_run_mu_bounds_irreversibility`) plus a packaged faithful-implementation contract (`FaithfulImplementation`) and transport (`faithful_impl_irreversibility_lower_bound`) so π₄ projection cost links to concrete µ-ledger/entropy accounting on real hardware. |
| `thiele_manifold/PhysicsIsomorphism.v` | Optional — compiled | Defines a small discrete-physics interface, a generic embedding contract, and registers the reversible/dissipative/wave lattice case studies as evidence toward the physics-as-computation conjectures. |
| `thielemachine/coqproofs/PhysicsEmbedding.v` | Optional — compiled | Parameterises an encoding/decoding of the lattice gas into VM states, transports the physics invariants, and packages µ-constancy/irreversibility bounds for any faithful implementation running the compiled trace. |
| `thielemachine/coqproofs/DissipativeEmbedding.v` | Optional — compiled | Abstractly embeds the dissipative lattice trace, showing any faithful implementation incurs at least one µ unit per simulated step thanks to non-zero instruction costs. |
| `thielemachine/coqproofs/WaveEmbedding.v` | Optional — compiled | Mirrors the reversible wave model with VM-facing conservation, zero irreversible-count, and µ-constancy corollaries for faithful implementations once a simulation trace is supplied. |
| `spacetime_projection/SpacetimeProjection.v` | Optional — compiled | Makes the Thiele→spacetime projection explicit, shows many-to-one collapse with positive μ-cost, and captures quantum/consciousness effects as projection artefacts. |
| `test_vscoq/coqproofs/test_vscoq.v` | Optional — compiled | Minimal lemma used to validate editor integration; proves a simple arithmetic fact as a smoke test. |

### Sandboxes (excluded)
| File | Tier/Build status | Notes |
| --- | --- | --- |
| `sandboxes/AbstractPartitionCHSH.v`, `EncodingMini.v`, `GeneratedProof.v`, `ToyThieleMachine.v`, `VerifiedGraphSolver.v` | Not in audited builds | Developer playgrounds/sandboxes; not in `_CoqProject`; no admits/axioms tracked. |

### Miscellaneous
| File | Tier/Build status | Notes |
| --- | --- | --- |
| `coq/tmp_bell_head.v` | Not in audited builds | Bell-inequality sandbox; no admits/axioms flagged. |
| `coq/tmp_check_power.v`, `coq/tmp_verify_truth.v` | Not in audited builds | Arithmetic/truth-table experiments; not in `_CoqProject`. |
