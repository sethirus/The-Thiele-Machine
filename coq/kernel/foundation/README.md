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
| `MuCostModel.v` | `vm_apply_mu` + monotonicity baseline |
| `MuLedgerConservation.v` | `vm_apply` preserves the cost ledger across the full instruction set |
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
| `TuringCompletenessISA.v` | The Thiele ISA is Turing-complete on the classical fragment |

## Load-bearing exports cited from the README

- `vm_mu_not_classically_determined`, `mu_ledger_necessity` — via [coq/NecessityOfMuLedger.v](../../NecessityOfMuLedger.v)
- `shadow_strictly_lossy` — via [witness/ShadowProjection.v](../witness/ShadowProjection.v)

## Imports

Standard library only. No project-internal imports.
