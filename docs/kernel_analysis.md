# Project Omega: Definitive Analysis of the Thiele Kernel

## 1. Abstract
The kernel formalisation anchors the containment argument.  Two interpreters
share a common tape/head substrate and diverge only on the μ-charging
`H_ClaimTapeIsZero` instruction.  Coq establishes that classical programs evolve
identically under both machines and that the Thiele interpreter reaches states
unattainable by the classical one.  The Python VM bridge is currently undergoing
a redesign to include a faithful tape encoding; only μ-ledger alignment is
modelled today.

## 2. Shared State and Instruction Set (`Kernel.v`)
The `state` record tracks a boolean tape, head position, program counter, and μ
ledger.【F:coq/kernel/Kernel.v†L4-L9】  The shared instruction datatype offers halt,
write, move, and branch primitives plus the Thiele-only `H_ClaimTapeIsZero`
carrying an explicit μ-delta.【F:coq/kernel/Kernel.v†L15-L20】  The predicate
`turing_instruction` isolates the classical subset, enabling proofs about programs
that never invoke the claim.【F:coq/kernel/Kernel.v†L59-L66】

## 3. Classical Engine (`KernelTM.v`)
`step_tm` executes the classical opcodes by updating the tape and head while
leaving `mu_cost` untouched.  When it encounters `H_ClaimTapeIsZero`, it simply
advances the program counter, embodying the classical machine’s inability to pay
for the non-classical transition.【F:coq/kernel/KernelTM.v†L6-L30】  The iterator
`run_tm` extends this behaviour over finite fuel, preserving classical semantics
for any program made exclusively of `turing_instruction`s.【F:coq/kernel/KernelTM.v†L32-L55】

## 4. Thiele Engine (`KernelThiele.v`)
`step_thiele` mirrors the classical clauses but implements the claim: it replaces
the tape with zeros and increases `mu_cost` by the supplied delta before
advancing the control state.【F:coq/kernel/KernelThiele.v†L7-L26】  The recursion
`run_thiele` extends the semantics over fuel in lockstep with `run_tm`.

## 5. Subsumption Theorems (`Subsumption.v`)
The lemma `fetch_turing` shows that, for classical programs, fetching an
instruction always yields a classical opcode.  Combined with
`step_tm_thiele_agree`, it proves the simulation theorem
`thiele_simulates_turing`: running either interpreter on classical programs yields
the same state for any fuel.【F:coq/kernel/Subsumption.v†L23-L76】  The witness
program `p_impossible` contains a single claim; under the classical interpreter it
leaves the tape unchanged, while under the Thiele interpreter it reaches the
zeroed tape with μ-cost one, proving strict containment via
`turing_is_strictly_contained`.【F:coq/kernel/Subsumption.v†L78-L118】

## 6. Meaning of the μ-bit
Within the kernel, μ-cost tracks the non-classical resource consumed by the claim
instruction.  Classical steps never alter `mu_cost`; only
`H_ClaimTapeIsZero` increments the ledger.  This delineates classical work (fuel)
from paid reasoning (μ) inside the mechanised model.【F:coq/kernel/Kernel.v†L4-L66】【F:coq/kernel/KernelThiele.v†L23-L25】

## 7. Bridging the Python VM (`SimulationProof.v`)
The existing bridge modules provide a starting point: `VMState` mirrors the VM’s
partition bookkeeping and `VMStep` exposes opcode semantics with μ-deltas and
error flags.【F:coq/kernel/VMStep.v†L1-L102】【F:coq/kernel/VMState.v†L1-L204】
`vm_apply` deterministically replays each opcode while remaining compatible with
the relational `vm_step` semantics.【F:coq/kernel/SimulationProof.v†L34-L120】  A
canonical tape encoding and compilation routine are still outstanding; current
lemmas only align the μ-ledger and control counters.  Operation Unification
Milestone 2 tracks the work required to relate the full partition graph and CSR
state to the kernel tape.【F:docs/operation_unification_progress.md†L40-L120】

## 8. Audit Evidence
Compiling the kernel suite with `coqc -q -time -Q kernel Kernel` validates the
containment development without admits; the audit transcript in
`audit_logs/agent_coq_verification.log` records each timing step for independent
review.【F:audit_logs/agent_coq_verification.log†L1-L318】  The Python VM bridge and
its simulation theorem remain under construction; see the Operation Unification
log for the current status and outstanding tasks.【F:docs/operation_unification_progress.md†L1-L120】
