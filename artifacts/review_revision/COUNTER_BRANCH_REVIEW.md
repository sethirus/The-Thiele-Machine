# Counter branch source review (2026-09-12)

Scope: independent source reading within the SAME working environment/session, not separate-environment reproduction or a final release audit. Reviewed `coq/kernel/foundation/VMCounterBranch.v` against Gate B2 of the supplied completion contract, plus the definitions it actually executes in `SimulationProof.v`, `VMUnboundedCounterAccess.v`, `VMState.v`, and `VMUnboundedExec.v`. No source edits made. This review does not restart any original monograph item.

## Finding

No concrete correctness mismatch found in the claimed branch, update, or nonnegative drain contracts. These prove a reusable zero/equality test and a fixed internally controlled repetition example under the existing abstract PC-indexed runner. They do NOT discharge the B2 requirement of sufficient independently usable storage/control for a chosen universal simulation, B3 uniform self-interpretation, or B4 effective recurrence.

## Execution and both guard outcomes

`counter_branch_correct` quantifies over all u,v:nat and all states satisfying the exact `counter_witness u v` layout. It requires the guard at the current PC, a success jump at PC+1, and a failure jump at the existing LASSERT_TRAP_PC=3840. In two `run_vm` steps it reaches the selected target with the full `counter_branch_result` state.

The source `SimulationProof.vm_apply` CHSH guard (557–590) advances PC on success and preserves errors, or writes PC3840, vm_err=true and csr_err=1 on failure. BOTH paths charge one at delta0. `run_vm` (729) fetches by PC and does not stop on vm_err. Consequently the failing path can execute the trap trampoline and later guards even while err remains true. This is specific to the abstract execution model: actual hardware's `Assert !err` differs, and the macro does not claim hardware realization.

Full-state result is accurate: graph, registers, memory, witness, tensor, logic accumulator, mstatus and certification are retained. Success preserves the whole CSR and existing vm_err. Failure updates only CSR error via `csr_set_err`, preserving other CSR fields, and sets vm_err. Mu increments exactly once; no implicit error clearing is present.

The branch fetch premises are concrete rather than opaque interpreter-correctness assumptions. Some arbitrary PC/target choices could make simultaneous fetch hypotheses inconsistent; the statement does not promise those layouts. `counter_drain_fetch` gives an explicit nontrivial satisfying layout and the example states supply its state premises.

## Fixed program and progress

`counter_drain_program` is one fixed list of length3841, independent of u,v. The PC0 guard reaches either PC1 (jump3841) or PC3840 (jump2). The unequal path executes the differing CHSH trial at2 and jump0 at3. No host routine chooses the next VM action. `counter_rounds` is a proof-level expression for the resulting state, not a runtime callback. Supplying a fuel bound calculated from initial data is a proof/observation device; it does not choose branch outcomes during execution.

`counter_drain_iteration` universally establishes one four-step unequal round. `counter_drain_exit` gives the two-step equal exit. `counter_drain_correct` proves a full-state result at fuel `4*(u-v)+2` for all v<=u; `counter_drain_halts` additionally proves end-of-program halting at PC3841, using the actual program length. Halting means PC outside the list, not an `instr_halt` event or fuel exhaustion.

The bound is a sufficient finite execution bound, not a theorem of minimal instruction count. It includes d=u-v unequal rounds and one final equality round. From `counter_rounds_fields`, witness becomes counter_witness u u; mu increases d+1; if d>0 vm_err is true and csr_err1; at d=0 initial error/CSR are preserved. The frame lemma and full result preserve all other fields.

The v<=u restriction is explicit and appropriate to a decrement-to-zero loop; it does not establish drain termination for a negative represented signed difference. The generic equality branch and increment/decrement remain unrestricted over u,v. No claim that negative inputs halt was found.

## Update contracts added during review

`counter_update_result`, `counter_increment_correct`, and `counter_decrement_correct` now cover the actual one-step `run_vm` behavior, not merely `record_trial`. They require a typed witness layout and the relevant CHSH_TRIAL instruction at the current PC. Each advances PC by1, changes only the designated witness component, charges zero at delta0, and retains even a pre-existing error/CSR state. The witness invariants are preserved for every u,v. Source proofs unfold the actual runner/application and do not invoke external decoding. Root subsequently reported successful compilation and full make. I inspected the final `artifacts/review_revision/counter_branch_report.txt`: it includes both exact update theorem types and their `Closed under the global context` assumption reports. The earlier separate review probe did not include these additions.

## Executable examples and nonvacuity

Three `vm_compute` examples cover unequal repeated guards after the first failure, an equal input already carrying vm_err=true with nontrivial registers/memory/certification, and the final equal witness after two unequal rounds. `counter_example_state` has graph/CSR from init_state, registers[42], memory[13], mu7, logic accumulator99, certification true. Arbitrary represented witness input at initialization is permitted by the target. It is not a proof that all such states are reachable from a particular restricted reset/input-loading program, which B2 does not silently assume here.

`counter_branch_repeats_after_error` samples fuel2,4,6,8,10 and reaches PCs2,0,2,0,3841 with the expected persistent error and charges. This is a concrete repetition regression rather than a claim drawn only from the guard's Boolean mathematics.

## Remaining composition/universality dependencies

- The representation reserves the other CHSH buckets and exposes one difference u-v. It has not established enough independently addressable counters/storage for a universal model, nor simulation of that model's exact instruction set.
- The failure vector is one global fixed address. The generic branch lemma allows arbitrary no targets only for a program containing the corresponding jump at that vector; a multi-site program cannot instantiate different static no-target jumps there simultaneously. Drain reuses a single site and is sound. A larger interpreter needs an explicit dispatch/return convention or another proved control layout.
- The full witness/error/CSR effects must be retained when composing with other macros; the error latch is not restored. Future specifications needing clean errors need an actual mechanism, not deletion of the observed bit.
- Programs extend through address3840; finite128-word hardware cannot execute this program. The source header makes the abstract scope explicit.
- No guest configuration relation, fixed universal program, effective specializer, recurrence instance, or preservation of a simulated structural ledger is provided by these lemmas.

## Evidence

`/tmp/thiele-resume/CounterBranchReviewProbe.v` imported the built module and checked branch, drain, and halting types, expanded the fixed program, and printed assumptions for eight existing results (branch, drain, halting, fields, frame, three examples). `/tmp/thiele-resume/CounterBranchReviewProbe.log` records command and exit0. Every printed assumption report was `Closed under the global context`. This was an import/type/assumption check, not a new complete source rebuild or compiled-library audit.

Final reviewed source hash, including both one-step update theorems: d7ff33086b28d23fbb5602f89b16558e5899e54381e0e54a131a933801ae8582. Root reports the full source build passed; final compiled-library audit and source/artifact provenance remain recorded by the root checkpoint. Read-only source inspection used sed/grep/cat; an exploratory grep for MuInitiality.v under foundation failed because that file is under mu_calculus, then the correct path was located. No failed validation command was represented as success.
d7ff33086b28d23fbb5602f89b16558e5899e54381e0e54a131a933801ae8582  coq/kernel/foundation/VMCounterBranch.v
