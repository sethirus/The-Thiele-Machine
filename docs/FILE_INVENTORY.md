# Complete File Inventories

This document provides **complete inventories** of every file in the codebase. Each file is listed with its line count, purpose, and location.

## Python VM Files

**Location:** `/thielecpu/`
**Total:** 21 Python files, ~5,500 lines

### Core VM Files (7 files)

| File | Lines | Purpose |
|------|-------|---------|
| `vm.py` | 2,292 | Main VM execution loop, sandbox execution, symbolic solving, partition discovery |
| `state.py` | 291 | Machine state: partitions, regions, μ-accumulator, checkpointing |
| `isa.py` | 81 | Instruction set architecture: opcode definitions, encoding, decoding |
| `mu.py` | 85 | μ-bit calculation (μ-spec v2.0): question cost, information gain |
| `receipts.py` | 323 | Cryptographic receipt generation, verification, audit trails |
| `logic.py` | 151 | Logic engine: LASSERT/LJOIN implementation, certificate management |
| `discovery.py` | 1,179 | Efficient partition discovery using spectral clustering and MDL |

### Support Files (9 files)

| File | Lines | Purpose |
|------|-------|---------|
| `certcheck.py` | 237 | Certificate verification infrastructure, chain validation |
| `mdl.py` | 159 | Minimum Description Length calculations for partition evaluation |
| `cnf.py` | 113 | CNF formula handling and SAT solving integration |
| `primitives.py` | 299 | Placeholder system for symbolic variables, constraint solving |
| `assemble.py` | 53 | Assembly language parser for .thm files |
| `certs.py` | 63 | Certificate data structures and types |
| `memory.py` | 45 | Memory management and allocation |
| `logger.py` | 54 | Logging infrastructure and debugging utilities |
| `_types.py` | 47 | Type definitions and aliases |
| `__init__.py` | 42 | Package initialization and module exports |

### Specialized Primitives (5 files)

| File | Lines | Purpose |
|------|-------|---------|
| `factoring.py` | 114 | Integer factorization primitives (trial division, factor extraction) |
| `shor_oracle.py` | 291 | Period-finding oracle for Shor's algorithm demonstrations |
| `geometric_oracle.py` | 90 | Geometric computation primitives |
| `riemann_primitives.py` | 265 | Riemann hypothesis-related primitives and zeta function computations |
| `security_monitor.py` | 268 | Security monitoring, sandboxing, and safety enforcement |

---

## Verilog Hardware Files

**Total:** 24 Verilog files plus specialized modules

### Core CPU Modules (6 files)

The core Thiele CPU is implemented in 6 Verilog modules:

| File | Lines | Purpose |
|------|-------|---------|
| `thiele_cpu.v` | 783 | Main CPU: fetch/decode/execute pipeline, μ-accounting, opcode handling |
| `thiele_cpu_tb.v` | 235 | Testbench: validates all opcodes, μ-ledger accuracy, execution correctness |
| `lei.v` | 178 | Logic Engine Interface: LASSERT/LJOIN hardware support, Z3 integration |
| `mau.v` | 180 | Memory Access Unit: load/store operations, address translation |
| `mmu.v` | 247 | Memory Management Unit: virtual memory, protection, caching |
| `pee.v` | 215 | Python Execution Engine: sandboxed Python execution interface |

### Specialized Hardware Modules

**Synthesis Trap** (`thielecpu/hardware/synthesis_trap/`) — Graph solving hardware

| File | Lines | Purpose |
|------|-------|---------|
| `reasoning_core.v` | 106 | Combinational reasoning fabric for constraint propagation |
| `thiele_autonomous_solver.v` | 389 | Sequential controller for autonomous solving |
| `thiele_graph_solver.v` | 258 | Graph 3-coloring solver with partition logic |
| `thiele_graph_solver_tb.v` | 182 | Testbench for graph solver validation |
| `classical_solver.v` | 137 | Classical (blind) baseline for comparison |

**Resonator** (`thielecpu/hardware/resonator/`) — Period-finding hardware

| File | Lines | Purpose |
|------|-------|---------|
| `period_finder.v` | 370 | Thiele-based period finding with partition discovery |
| `classical_period_finder.v` | 125 | Classical period finder baseline |

**Forge** (`thielecpu/hardware/forge/`) — Primitive discovery hardware

| File | Lines | Purpose |
|------|-------|---------|
| `empyrean_forge.v` | 186 | Main forge controller for primitive discovery |
| `primitive_graph_node.v` | 55 | Graph node primitive for network analysis |
| `primitive_matrix_decomp.v` | 108 | Matrix decomposition primitive |
| `primitive_community_assign.v` | 139 | Community detection primitive |

**Discovery** (`thielecpu/hardware/partition_discovery/`) — Partition discovery architecture

| File | Lines | Purpose |
|------|-------|---------|
| `pdiscover_archsphere.v` | 437 | Architecture sphere for efficient partition discovery |

---

## Coq Proof Files

**Total:** 114 Coq files, ~54,600 lines of machine-verified proofs

### 1. Kernel — Core Subsumption (10 files)

**Location:** `coq/kernel/`
**Purpose:** Establishes TURING ⊂ THIELE containment

| File | Lines | Purpose | Key Theorems |
|------|-------|---------|--------------|
| `Kernel.v` | 66 | Shared primitives for TM and Thiele | `state` record, `instruction` type |
| `KernelTM.v` | 61 | Turing Machine step function | `step_tm`, `run_tm` |
| `KernelThiele.v` | 36 | Thiele Machine step function | `step_thiele`, `run_thiele` |
| `Subsumption.v` | 118 | **Main containment theorem** | `thiele_simulates_turing`, `turing_is_strictly_contained` |
| `SimulationProof.v` | 616 | Simulation lemmas and supporting proofs | `step_tm_thiele_agree`, `fetch_turing` |
| `VMState.v` | 262 | VM state formalization | `VMState` record, state invariants |
| `VMStep.v` | 127 | Step function semantics | `vm_step`, opcode semantics |
| `VMEncoding.v` | 657 | Instruction encoding correctness | `encode_injective`, `encode_decode_id` |
| `MuLedgerConservation.v` | 402 | **μ-ledger conservation** | `mu_conservation`, `mu_never_decreases` |
| `PDISCOVERIntegration.v` | 165 | Partition discovery integration | `discovery_profitable` |

### 2. ThieleMachine — Machine Semantics (40 files)

**Location:** `coq/thielemachine/coqproofs/`
**Purpose:** Complete formal specification of the Thiele Machine

| File | Lines | Purpose | Key Theorems |
|------|-------|---------|--------------|
| `ThieleMachine.v` | 457 | **Abstract machine signature** | `ThieleMachine` record, step semantics |
| `ThieleMachineConcrete.v` | 485 | Concrete executable model | `mu_cost`, `step_concrete` |
| `ThieleMachineModular.v` | 16 | Modular composition | Module independence proofs |
| `ThieleMachineSig.v` | 204 | Module type signatures | Signature definitions |
| `ThieleMachineUniv.v` | 15 | Universal machine | Universality properties |
| `ThieleMachineConcretePack.v` | 11 | Concrete packaging | Implementation packaging |
| `ThieleProc.v` | 243 | Process algebra formalization | Process composition |
| `Separation.v` | 185 | **Exponential separation** | `exponential_separation`, polynomial vs exponential |
| `Subsumption.v` | 64 | Containment (alternative proof) | TM ⊆ Thiele |
| `Confluence.v` | 36 | Church-Rosser property | `church_rosser` |
| `PartitionLogic.v` | 335 | **Partition algebra** | `partition_refines`, `psplit_preserves_independence` |
| `NUSD.v` | 27 | No Unpaid Sight Debt principle | Helper lemmas |
| `AmortizedAnalysis.v` | 161 | Cost amortization proofs | Amortized complexity bounds |
| `EfficientDiscovery.v` | 190 | **Polynomial discovery** | `discovery_polynomial_time` |
| `Oracle.v` | 558 | Oracle formalization | `T1_State`, `T1_Receipt`, oracle scaffolding |
| `HardwareBridge.v` | 151 | **RTL ↔ Coq alignment** | Opcode matching, μ-accumulator equivalence |
| `HardwareVMHarness.v` | 62 | Hardware testing harness | Test infrastructure |
| `EncodingBridge.v` | 28 | Encoding consistency | Cross-layer encoding |
| `Bisimulation.v` | 19 | Behavioral equivalence | Bisimulation relations |
| `BellInequality.v` | 2,487 | **CHSH verification** | `classical_bound`, Bell inequality witnesses |
| `BellCheck.v` | 151 | Bell inequality checker | Inequality verification |
| `LawCheck.v` | 156 | Physical law verification | Law checking algorithms |
| `PhysicsEmbedding.v` | 188 | Physics-computation isomorphism | Physical law formalization |
| `DissipativeEmbedding.v` | 159 | Dissipative systems embedding | Dissipation modeling |
| `WaveEmbedding.v` | 177 | Wave mechanics embedding | Wave equation formalization |
| `HyperThiele.v` | 51 | Hypercomputation limits | Hyper-Thiele definition |
| `HyperThiele_Halting.v` | 100 | Halting problem for hyper-Thiele | Halting decidability |
| `HyperThiele_Oracle.v` | 54 | Oracle limitations | Oracle boundary analysis |
| `Impossibility.v` | 102 | Impossibility results | What cannot be computed efficiently |
| `Simulation.v` | 29,668 | **Full simulation proof** | Complete simulation (66% of all Coq code!) |
| `SpecSound.v` | 204 | Specification soundness | Correctness of specifications |
| `StructuredInstances.v` | 113 | Structured problem instances | Instance construction |
| `Axioms.v` | 98 | Core axioms | Foundational assumptions |
| `ListHelpers.v` | 113 | List utility lemmas | Helper functions |
| `QHelpers.v` | 83 | Rational number helpers | Q arithmetic |
| `MuAlignmentExample.v` | 60 | μ-alignment example | Alignment demonstration |
| `PhaseThree.v` | 64 | Phase three verification | Phase 3 proofs |
| `UTMStaticCheck.v` | 28 | UTM static analysis | Static verification |
| `debug_no_rule.v` | 96 | Debugging utilities | Debug helpers |
| `Axioms.v` | 98 | Foundational axioms | Core assumptions |

**Note on Simulation.v:** This 29,668-line file contains the complete, detailed simulation proof showing how every possible Thiele Machine execution can be traced step-by-step. It represents 66% of all Coq code in the project and is the most comprehensive proof artifact. The bulk comes from explicitly enumerating **all instruction forms and tape/ledger cases** with minimal automation (to keep proof search deterministic), plus a catalogue of "no-rule" preservation lemmas that keep tape-length, μ-ledger, and CPU state aligned while stepping. In short: the file is long because it is **mechanically exhaustive**, not because the argument is hidden in a monolithic tactic.

### 3. Bridge Verification (19 files)

**Location:** `coq/thielemachine/verification/`
**Purpose:** Proves correctness of hardware-software bridge

#### Main Bridge Files (5 files)

| File | Lines | Purpose |
|------|-------|---------|
| `BridgeDefinitions.v` | 1,083 | Bridge type definitions and core structures |
| `BridgeProof.v` | 31 | Main bridge correctness theorem |
| `BridgeCheckpoints.v` | 13 | Checkpoint verification |
| `ThieleUniversalBridge.v` | 41 | Universal bridge construction |
| `ThieleUniversalBridge_Axiom_Tests.v` | 232 | Axiom testing (4 admits for test stubs) |

#### Modular Bridge Components (14 files)

**Location:** `coq/thielemachine/verification/modular/`

| File | Lines | Purpose |
|------|-------|---------|
| `Bridge_BasicLemmas.v` | 214 | Basic bridge lemmas |
| `Bridge_BridgeCore.v` | 164 | Core bridge logic |
| `Bridge_BridgeHeader.v` | 67 | Header and preamble definitions |
| `Bridge_Invariants.v` | 184 | Invariant preservation |
| `Bridge_LengthPreservation.v` | 34 | Tape length preservation |
| `Bridge_LoopExitMatch.v` | 214 | Loop exit condition matching |
| `Bridge_LoopIterationNoMatch.v` | 164 | Loop iteration (no match case) |
| `Bridge_MainTheorem.v` | 590 | **Main bridge theorem** |
| `Bridge_ProgramEncoding.v` | 164 | Program encoding correctness |
| `Bridge_RegisterLemmas.v` | 294 | Register manipulation lemmas |
| `Bridge_SetupState.v` | 197 | Initial state setup |
| `Bridge_StepLemmas.v` | 217 | Single-step execution lemmas |
| `Bridge_TransitionFetch.v` | 264 | Instruction fetch transitions |
| `Bridge_TransitionFindRuleNext.v` | 314 | Rule-finding transitions |

### 4. Universal Machine (7 files)

**Location:** `coq/thieleuniversal/coqproofs/`
**Purpose:** Universal Thiele Machine construction

| File | Lines | Purpose |
|------|-------|---------|
| `ThieleUniversal.v` | 117 | Universal Thiele Machine definition |
| `TM.v` | 133 | Turing Machine formalization |
| `CPU.v` | 184 | CPU semantics |
| `UTM_Program.v` | 456 | Universal program construction |
| `UTM_Rules.v` | 49 | Transition rules |
| `UTM_Encode.v` | 147 | Encoding proofs |
| `UTM_CoreLemmas.v` | 573 | Core supporting lemmas |

### 5. Modular Proof Components (8 files)

**Location:** `coq/modular_proofs/`
**Purpose:** Modular proof infrastructure for TM-Minsky-Thiele reductions

| File | Lines | Purpose |
|------|-------|---------|
| `CornerstoneThiele.v` | 365 | Cornerstone theorems |
| `Encoding.v` | 256 | Encoding infrastructure |
| `EncodingBounds.v` | 238 | Encoding size bounds |
| `Minsky.v` | 77 | Minsky machine formalization |
| `Simulation.v` | 41 | Simulation framework |
| `TM_Basics.v` | 168 | Turing Machine basics |
| `TM_to_Minsky.v` | 54 | TM to Minsky reduction |
| `Thiele_Basics.v` | 61 | Thiele Machine basics |

### 6. Physics Models (3 files)

**Location:** `coq/physics/`
**Purpose:** Physics-computation correspondence

| File | Lines | Purpose |
|------|-------|---------|
| `DiscreteModel.v` | 180 | Discrete physics model |
| `DissipativeModel.v` | 65 | Dissipative systems |
| `WaveModel.v` | 271 | Wave mechanics formalization |

### 7. Shor Primitives (3 files)

**Location:** `coq/shor_primitives/`
**Purpose:** Shor's algorithm primitives

| File | Lines | Purpose |
|------|-------|---------|
| `Euclidean.v` | 48 | Extended Euclidean algorithm |
| `Modular.v` | 84 | Modular arithmetic |
| `PeriodFinding.v` | 49 | Period-finding algorithm |

### 8. Thiele Manifold (4 files)

**Location:** `coq/thiele_manifold/`
**Purpose:** Geometric and physical manifold theory

| File | Lines | Purpose |
|------|-------|---------|
| `ThieleManifold.v` | 160 | Thiele manifold definition |
| `ThieleManifoldBridge.v` | 276 | Manifold-computation bridge |
| `PhysicalConstants.v` | 58 | Physical constants and units |
| `PhysicsIsomorphism.v` | 280 | **Physics ↔ Computation isomorphism** |

### 9. Spacetime Theories (2 files)

**Spacetime** (`coq/spacetime/`)

| File | Lines | Purpose |
|------|-------|---------|
| `Spacetime.v` | 140 | Spacetime formalization |

**Spacetime Projection** (`coq/spacetime_projection/`)

| File | Lines | Purpose |
|------|-------|---------|
| `SpacetimeProjection.v` | 130 | Projection onto spacetime manifold |

### 10. Self-Reference (1 file)

**Location:** `coq/self_reference/`

| File | Lines | Purpose |
|------|-------|---------|
| `SelfReference.v` | 80 | Self-reference and fixed points |

### 11. Sandboxes — Experimental Proofs (5 files)

**Location:** `coq/sandboxes/`
**Purpose:** Experimental and pedagogical proofs

| File | Lines | Purpose |
|------|-------|---------|
| `AbstractPartitionCHSH.v` | 408 | Abstract partition formalization with CHSH |
| `EncodingMini.v` | 247 | Minimal encoding example |
| `GeneratedProof.v` | 50 | Auto-generated proof demonstration |
| `ToyThieleMachine.v` | 130 | Toy implementation for pedagogy |
| `VerifiedGraphSolver.v` | 237 | Verified graph coloring solver |

### 12. P=NP Analysis (1 file)

**Location:** `coq/p_equals_np_thiele/`

| File | Lines | Purpose |
|------|-------|---------|
| `proof.v` | 65 | P=NP relationship in Thiele context |

### 13. Project Cerberus (1 file)

**Location:** `coq/project_cerberus/coqproofs/`

| File | Lines | Purpose |
|------|-------|---------|
| `Cerberus.v` | 229 | Cerberus multi-headed verification |

### 14. CatNet (1 file)

**Location:** `coq/catnet/coqproofs/`

| File | Lines | Purpose |
|------|-------|---------|
| `CatNet.v` | 99 | Category theory network formalization |

### 15. Isomorphism (1 file)

**Location:** `coq/isomorphism/coqproofs/`

| File | Lines | Purpose |
|------|-------|---------|
| `Universe.v` | 81 | Universal isomorphism construction |

### 16. Test Infrastructure (1 file)

**Location:** `coq/test_vscoq/coqproofs/`

| File | Lines | Purpose |
|------|-------|---------|
| `test_vscoq.v` | 2 | VSCoq IDE testing |

### Summary: Coq Files by Category

| Category | Files | Lines | Percentage |
|----------|-------|-------|------------|
| ThieleMachine Core | 48 | 40,896 | 75% |
| Kernel Subsumption | 10 | 2,510 | 5% |
| Bridge Verification | 18 | 4,447 | 8% |
| Universal Machine | 7 | 1,659 | 3% |
| Modular Proofs | 8 | 1,260 | 2% |
| Physics Models | 3 | 516 | 1% |
| Other (manifold, spacetime, etc.) | 21 | 3,485 | 6% |
| **Total** | **115** | **54,773** | **100%** |
