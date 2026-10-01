# kernel/foundation

The VM model itself, plus the Turing/classical fragment that the strictness
results compare against.

This is the bottom of the proof tree. Every other subdirectory ultimately
imports something here.

## Files

| File | Purpose |
|---|---|
| `VMState.v` | `VMState` record (mem, regs, pc, mu, certified, graph, csrs, witness, ...) |
| `VMStep.v` | `vm_apply : VMState → vm_instruction → VMState` plus `instruction_cost` table |
| `VMEncoding.v` | Canonical binary encoding `VMState ↔ list bool` (used by SimulationProof) |
| `MuCostModel.v` | Partition ops are mu-free; mu-zero traces reveal nothing (`mu_zero_no_reveal`) |
| `MuLedgerConservation.v` | `vm_apply_mu`: `vm_apply` preserves the cost ledger across the full instruction set |
| `SimulationProof.v` | `exec_trace_from`, `reachable`, fold-equivalence with `run_instrs` |
| `Definitions.v` | Shared utility predicates (region equiv, finite-region-equiv-class) |
| `Locality.v` | Module-region observation locality lemmas |
| `Persistence.v` | Long-term VM-state invariants under mixed traces |
| `StateSpaceCounting.v` | Cardinality bounds on observable equivalence classes |
| `Kernel.v` | Toy machine model used as the foundation-of-foundation comparator |
| `KernelTM.v` | Standard Turing-machine semantics over `Kernel.program` |
| `KernelThiele.v` | Costed toy step function (gives `H_ClaimTapeIsZero` an effect) |
| `Subsumption.v` | Every Turing program is a Thiele program; reverse fails |
| `ProperSubsumption.v` | Strict ISA inclusion witness |
| `PartitionSeparation.v` | Partition ops are semantic in Thiele, syntactic in TM |
| `DagRestriction.v` | Sub-Turing DAG variant: NoFI survives without backward jumps |
| `ClassicalBound.v` | Classical CHSH bound on `μ=0` traces |
| `ClassicalConservativity.v` | D3: classical-opcode traces preserve graph/cert/witness |
| `TuringClassicalEmbedding.v` | D1+D2: classical-program notion + embedding into the Thiele ISA |
| `TuringStrictness.v` | D4+D5: Thiele strictly extends classical semantics (witness construction) |
| `TuringCompletenessISA.v` | Simulates 2-counter Minsky machines through `vm_apply` (5 of the 51 opcodes: `load_imm`, `add`, `sub`, `jnez`, `jump`), bounded by the 64-bit word representation |
| `Substrate.v` | Abstract computational substrate as a Coq typeclass; the 51-opcode VM is one realization |
| `VMSubstrateInstance.v` | `VMState` as a `Substrate` instance, so the substrate-level `structural_shortcut_undecidable` applies to the concrete VM |
| `NatSubstrateInstance.v` | A concrete `Substrate` over `nat`-coded programs, with the recursion theorem discharged by construction |
| `VMInstructionEncoding.v` | Godel encoding from `list vm_instruction` to `nat` with a proven left inverse |
| `VMBoundedDecidability.v` | Decidability of the bounded VM shortcut predicate, which compares full outcomes after 1000 steps |
| `VMWitnessCounterMonotonicity.v` | Witness-counter buckets are monotone under `vm_step` |
| `VMWord64BoundednessObstruction.v` | The bounded VM's register and memory file is a finite-state system; no finite program injects arbitrarily many distinct inputs into it |
| `VMEncodedInputAccess.v` | No fixed VM program started from `vm_encode_concrete p` can report `p`'s final certification bit for every `p` through an output independent of the retained `vm_logic_acc`; every executable opcode commutes with replacing `vm_logic_acc` |
| `VMCounterBranch.v` | Internal counter-dependent control under the unchanged PC-indexed runner, with an executable trap trampoline |
| `VMTwoCounterAccess.v` | A candidate two-counter access layout under the unchanged ISA; its rejection theorem applies to this layout only |
| `VMAlternativeCounterAccess.v` | An alternative diagonal witness layout under the existing ISA; it does not establish independent zero tests or universal computation |
| `VMUnboundedCounterAccess.v` | One unbounded counter primitive in the existing abstract ISA (bucket difference `u - v`); not a universal interpreter |
| `VMUnboundedStep.v` | `vm_apply_u`, the unbounded sibling of `vm_apply` (unmasked arithmetic) |
| `VMUnboundedLedger.v` | Ledger and certification facts for `vm_apply_u`: each step adds the instruction cost to `vm_mu`, only `CERTIFY` switches `vm_certified` on |
| `VMUnboundedExec.v` | Unbounded relational execution for the VM, separate from the bounded `vm_run` |
| `VMUnboundedGuestEncoding.v` | Bridge between `get_slot`/`set_slot` on one packed `nat` and a guest's register file (`list nat`) |
| `VMUnboundedInterpreterSlots.v` | Bit-slicing specification layer (`get_slot`, `set_slot`) for the self-interpreter |
| `VMUnboundedInterpreterCode.v` | Host instruction sequences that compute `get_slot` and `set_slot` under `vm_apply_u`, with correctness proofs |
| `VMUnboundedInterpreterCompose.v` | Subroutine-embedding infrastructure: straight-line helper code proved once at pc 0 and reused at any offset |
| `VMUnboundedOpcodeAdd.v` | The ADD opcode block of the self-interpreter, proved against the guest's list-based register file |
| `VMUnboundedMinskyInterpreter.v` | A fixed, data-driven interpreter for a two-counter Minsky guest packed into one unbounded natural |
| `VMUnboundedMinskyEncoding.v` | Executable variable-width encoding for the fixed Minsky interpreter |
| `VMUnboundedMinskyInterpreterProof.v` | One guest step is simulated by a finite, strictly positive execution of the single fixed host program |
| `VMUnboundedMinskyCorrectness.v` | Multi-step and result correctness for the fixed unbounded interpreter |
| `VMUnboundedCM2Encoding.v` | Program encoding for the CM2 variant (jump on successful decrement, zero falls through; Dudenhefner, FSCD 2022, Definition 2) |
| `VMUnboundedCM2Interpreter.v` | The 60-instruction fixed host interpreter program for CM2 guests, with its boundary relation |
| `VMUnboundedCM2InterpreterProof.v` | Decoding and per-step lemmas for the CM2 interpreter (`cm2_decode_correct`) |
| `VMUnboundedCM2Correctness.v` | Run-level soundness and completeness of the CM2 interpreter boundary (`cm2_uniform_interpreter_run_simulation`) |
| `VMUnboundedCM2Bridge.v` | Exact bridge to the pinned upstream two-counter machine semantics (MM2) |
| `VMUnboundedCM2Applicability.v` | A nonterminating and a terminating CM2 instance that separate the CM2 control convention from the zero-branch one |
| `VMUnboundedCM2IndependentStorage.v` | Independently usable storage and control for the CM2 simulation under unchanged ISA semantics |
| `VMUnboundedCM2Specialization.v` | Effective specialization of MM2's first input, with exact two-direction terminal-result and host contracts |
| `VMUnboundedCM2Limitative.v` | Reduction theorem for actual unbounded host halting; the upstream synthetic `undecidable` notion is kept, not replaced by `~ decidable` |
| `VMUnboundedCM2OutputPredicate.v` | An output-value fact about actual host execution: reduction toward an explicitly named nontrivial extensional predicate (`zero_out_program`) |
| `MM2ComplementUndec.v` | The complement of pinned MM2 halting is undecidable in the upstream synthetic sense, by composing the library's reductions from `PCPb_compl_undec` |
| `VMSelfGuest.v` | The guest language of the uniform self-interpreter (an explicit fragment of the unbounded VM over guest registers 0..3) and its data encoding |
| `VMSelfProgram.v` | The fixed host program `U` of the uniform self-interpreter and its phase lemmas under `run_vm_u` |
| `VMSelfCorrect.v` | One guest step of the self-interpreter at an interpreter boundary |
| `VMSelfRun.v` | Whole-run correctness of the self-interpreter; `g_run` equals the VM's own `run_vm_u` on `g_program p` |
| `VMSelfUniversal.v` | The guest fragment is universal: `cm2_compile` translates every CM2 program into it |
| `VMSelfLimitative.v` | Applicability of the self-interpreter: pinned MM2 halting reduces to halting of the fixed host program `U` |
| `VMSelfRice.v` | Model of well-formed guest programs (`g_run`, `g_beh`, `g_equiv`) and Rice's theorem by reduction |
| `VMSelfRiceUndec.v` | Rice's theorem for the self-interpreted unbounded model, its dual orientation, deciders realized by guest programs, and two named unbounded predicates |
| `VMDynamicEvalTarget.v` | Decoder, fuel-bounded evaluator, and specialization constructor for the self-interpreted guest fragment (definitions) |
| `VMDynamicEval.v` | Verified numeric dispatch and semantic s-m-n for the self-interpreted guest fragment |
| `VMRecursionTarget.v` | Exact recursion-theorem and Rice targets for the self-interpreted guest; `vm_guest_recursion_theorem` is a `Prop` definition here |
| `VMRecursionAudit.v` | Execution and Rice outcomes adjacent to the recursion-theorem target |
| `VMMMAReduction.v` | Repeated output-preserving reduction of alternate Minsky machines to three counters |
| `MMAOutputEpilogue.v` | Redirects every exit of an alternate Minsky program through an epilogue that moves counter zero into a fresh final counter |
| `VMMMA3GuestCompiler.v` | Direct compiler from three-counter alternate Minsky machines to the four-register guest |
| `VMGuestEvalNat.v` | The guest evaluator over natural numbers only (halving, parity, addition, multiplication), proved equal to the existing definitions |
| `VMGuestEvalTuple.v` | The guest evaluator restated over nested pairs so that extraction to L applies, proved equal to the record form |
| `VMGuestEvalL.v` | The guest evaluator extracted to the lambda calculus L with correctness proofs, and its Minsky machine via `L_computable_to_MMA_computable` |
| `VMGuestMMAInit.v` | Cost-free guest prologue that turns the guest input into the start registers of a one-input `MMA_computable` program |
| `VMGuestExactEpilogue.v` | Exact output epilogue for the four-register guest: decodes one number into all four guest registers and charges the mu ledger by an exact data-dependent amount |
| `VMGuestMMAPipeline.v` | Composite guest program that evaluates a one-input alternate Minsky program with exact semantics |
| `VMGuestRecursion.v` | The guest's internal recursion theorem, closed: `vm_guest_recursion_theorem_closed` |
| `LRecursion.v` | Kleene's second recursion theorem and Rice's theorem for the lambda calculus L |
| `StructuralCore.v` | Record-carrying machines, adequacy, and core equivalence (weak form) |
| `StructuralCoreCover.v` | Computational covers and record observations: the strong form of the structural definitions, for machines that run the VM underneath |
| `StructuralUniqueness.v` | The uniqueness conjectures of `StructuralCore` and `StructuralCoreCover` are false: a machine that bills CPU time is adequate and not the same |
| `StructuralCoreSchedule.v` | Uniqueness up to the price schedule (definitions) |
| `StructuralScheduleUniqueness.v` | Uniqueness up to the price schedule, in both strengths (`cert_record_schedule_uniqueness_holds`) |
| `StructuralCoreAnyBase.v` | The record axis over any base: honest extension and latch factorization (definitions) |
| `StructuralRecordAxis.v` | The record axis over any base is a latch (`record_axis_is_latch_holds`) |
| `RecordAxisDiscrimination.v` | Which machines carry the record axis: every base does; a reversible base with unbounded memory does; a reversible machine with finite memory does not |
| `RAMRecordAxis.v` | Tied and untied list-memory RAMs on the record axis; the tied RAM is an honest extension whose Boolean record factors as a latch, the untied RAM is not |
| `CrossBaseGranularityCore.v` | Cross-base equivalence that permits instruction stuttering (definitions) |
| `CrossBaseGranularityTransCore.v` | Transitivity of the weak cross-base equivalence |
| `CrossBaseGranularity.v` | Generic and available-adapter outcomes for cross-base granularity |
| `CrossBaseGranularityL.v` | An executable L base for the cross-base comparison: L's weak call-by-value step as a total function, stuttering on terms that do not step |
| `CrossBaseGranularityRAM.v` | A unit-cost random-access machine base (Cook and Reckhow) for the cross-base comparison |
| `EventSwapCore.v` | The VM's main results restated for an arbitrary latchable reading in place of certification (definitions) |
| `EventSwapTheorem.v` | `swap_preserves_main_results` is refuted (`swap_preserves_main_results_refuted`); the five results hold for certification (`certification_main_results`) |
| `EventGeneralizationTargets.v` | Propositions for replacing the certification reading by an arbitrary latchable reading (definitions only) |
| `EventGeneralization.v` | Proofs and counterexamples for the propositions of `EventGeneralizationTargets.v` |
| `GrowingRecordCore.v` | Targets for monotone multi-valued records (threshold latches plus a price schedule); definitions and propositions only |
| `GrowingRecord.v` | Proved outcomes for the `GrowingRecordCore.v` targets, including `one_latch_refuted` |
| `PricedRevocationCore.v` | Targets for classifying records that are revocable at a price |
| `PricedRevocation.v` | Proved outcomes for the priced-revocation targets (`actual_revocation_excludes_permanence_holds`, `revocation_price_does_not_price_writes_refuted`) |
| `ProbabilisticRecordCore.v` | Targets for probabilistic record machines with finite weights |
| `ProbabilisticRecord.v` | Proved outcomes for the finite-weight probabilistic targets (`deterministic_latch_handles_branching_refuted`, `schedule_determines_probabilities_refuted`) |

## Load-bearing exports cited from the README

- `vm_mu_not_classically_determined`, `mu_ledger_necessity` (in [coq/NecessityOfMuLedger.v](../../NecessityOfMuLedger.v))
- `shadow_strictly_lossy` (in [witness/ShadowProjection.v](../witness/ShadowProjection.v))

## Imports

Coq standard library, other `Kernel` modules (within `foundation/` and from `nfi/`, `mu_calculus/`, `witness/`, `quantum/`, `curvature/`, `frontier/`, `reductions/`), and, for the files built on the Coq Library of Undecidability Proofs (for example `MM2ComplementUndec.v`, `VMGuestEvalL.v`), that library.
