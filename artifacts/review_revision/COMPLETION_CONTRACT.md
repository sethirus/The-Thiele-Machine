Thiele Machine — completion contract for the current revision

Basis: the review-revision status and interpreter investigation summary supplied by Devon in this conversation. This is a proposed work instruction, not an independent verification report. The current repository, proof terms, generated RTL, and validation logs were not examined or rerun in preparing it.

Reported base: 69b968906eeb88622f6480cd65a011a7d021b890
Reported branch: work/v3.2.2-review-fixes
Original review-source SHA-256: c59642623b2074b172a641bee0848a4f32eabdbf54c859438427028371fa36ab

Objective and boundaries

Complete the existing revision and the explicitly requested extensions: an internally executed unbounded self-interpreter with an applicable theorem, and a physical RTL refinement contract. Preserve the abstract substrate/scaffolding distinction. Certification remains a worked instance, not the definition of the whole contribution.

Do not obtain a green completion label by silently weakening a conclusion, strengthening its premises, changing the machine, discarding an observation relevant to the intended claim, deleting failing tests, or replacing a requested implementation with a host-language evaluator. A justified specification change is allowed only when recorded explicitly as a target change rather than presented as completion of the old target.

Keep the original 30 review entries and their closure evidence. Do not reopen a closed entry without a concrete counterexample, a changed dependency, or evidence that its recorded resolution does not answer the original objection. A valid new finding must still be recorded; a frozen target is not permission to ignore an actual error.

Preserve all inherited staged changes, unstaged changes, and relevant untracked files. Do not reset, discard, overwrite, push, or publish them without authorization. Prepare a recoverable, immutable local source snapshot before additional changes. A complete base-plus-patch/archive representation is acceptable; it must include new files, not just tracked diffs.

Gate A — recoverable source and fixed theorem targets

Create a single completion ledger using the existing tracker rather than a competing checklist. Each remaining obligation needs:

the exact claim and the mathematical/execution model it concerns;

the input domain, observable result, and resource/environment assumptions;

the actual implementation and proof symbols;

the proof's full type, expanded load-bearing definitions, and axiom dependencies;

evidence that the intended instance satisfies its premises;

a validation command, raw output location, and checked source/artifact hashes;

a status that distinguishes implemented/tested, proved conditional, proved for the intended instance, and open.

The 27-result crosswalk and the 30-item review tracker count different objects. Provide their mapping; do not require their numbers to agree or treat either count alone as evidence of completeness.

Write the intended interpreter correctness, recurrence/representability, and retirement-refinement statements before the implementation is enlarged. Proposed theorem names are labels for work, not claims that those theorems already exist.

Pass condition: a fresh directory can reconstruct the checked source exactly, and each target has an explicit statement and evidence requirement.

Gate B — internal interpreter on the existing abstract ISA

B1. Retain both new findings

Keep the reported VMEncodedInputAccess theorem as an obstruction to the particular vm_logic_acc input route. Do not mistake it for impossibility of every encoding. Do not keep presenting a Coq-level decoder of that field as an instruction a running VM program can execute.

Keep the reported VMUnboundedCounterAccess increment, decrement, and equality results. They are evidence for the counter route, not yet a universality or interpreter theorem.

Likewise retain VMBoundedDecidability.v. A later unbounded theorem must not undo, rename, or obscure decidability of the actual bounded predicate.

B2. First milestone: composable data-dependent execution

Before attempting a complete interpreter, construct an actual VM instruction program that uses the counter representation and repeatedly branches on a counter-dependent condition under the intended PC-indexed runner.

In particular, inspect the base CHSH guard's normal and failing paths. Establish what happens to the PC, the error latch, and subsequent execution. A proof that the guard's mathematical Boolean detects equality is not yet a proof that the VM can use both answers repeatedly.

Require explicit contracts for the counter macros: representation invariant, scratch state, preserved fields, entry/exit control locations, and finite completion of each macro on its allowed inputs. Test both outcomes and repetition, but prove the contracts universally over the represented counter values.

Show that the selected representation supplies enough independently usable storage and control for the universal model being simulated. It may use counters or another encoded arrangement; do not assume that one usable counter automatically supplies all required storage, or that standard counter-machine universality transfers to a different instruction set without a simulation.

Input encoding at initialization and proof-level input/output decoding are legitimate. During execution, however, no external Coq/Python routine may inspect the guest program and choose its next action in place of the VM program. A host-side decoder may interpret a produced output representation; it may not execute the guest program to manufacture the alleged output.

Pass condition: composable, reusable, internally controlled primitives sufficient for the chosen simulation, with working examples and proofs under the unchanged execution semantics.

Failure disposition: report the smallest precise obstruction. Failure of this construction is not automatically nonuniversality of the whole ISA. Other readable encodings or a new reference model remain architectural options. Do not silently adopt either while describing the result as a theorem about the unchanged VM.

B3. Uniform self-interpreter

Construct one fixed finite VM program U. The guest program p and its input x must be supplied as encoded data; they must not select a different host program or an external sequence of decoded VM instructions at runtime.

State a representation relation between guest configurations and host configurations at interpreter boundaries. Prove that every guest step is implemented by a finite host execution with the appropriate progress guarantee. Prevent infinite host bookkeeping from masquerading as successful simulation of an advancing guest.

Prove both correctness directions for the chosen result observation: guest termination with result y leads to interpreter termination with the represented result, and an interpreter result corresponds to an actual guest result. State how halting, traps, malformed code, and divergence are distinguished. Do not call running out of fuel divergence.

Keep host scratch state and interpreter overhead separate from the simulated guest state. If the theorem preserves structural observations or a guest ledger, represent and prove those facts explicitly. The host's own accumulated charge need not equal the simulated guest's charge; do not assume that equality.

Pass condition: a fixed VM program and an applicable correctness theorem over the full stated guest/input domain, not just a Coq evaluator, a compiler producing a separate host program per guest, a few examples, or a theorem assuming interpreter correctness.

B4. Applicable unbounded recurrence and limitative theorem

Define the unbounded program semantics and the precise behavioral equivalence used in the recurrence theorem. Specify whether that equivalence observes only returned answers or additional structural state. Do not discard information needed by the predicate whose undecidability is claimed.

Supply the effective program-transformer and specialization machinery required by the selected fixed-point argument, or use a different proved construction with its prerequisites discharged. Interpreter existence must not be treated as automatically discharging an arbitrary recursion-theorem record field.

Define representability through the actual execution model and connect the target program predicate to that same model. Supply the nontrivial witnesses and extensionality argument the target theorem needs. Preserve the distinction between bounded outcome equality and unbounded halting/reachability.

Pass condition: the concrete intended instance satisfies the exact recurrence and representability premises, and the claimed limitative result applies to its explicitly named unbounded predicate. A remaining assumed instance means this gate remains open.

Gate C — physical FSM and RTL refinement

C1. Fix the finite implementation contract

Identify the actual synthesizable FSM/module, the emitted RTL, and their source hashes. State the supported opcode set, initial/reset state, admissible input encodings, arithmetic widths, table limits, observations, and environment assumptions.

Resolve the current capacity policy explicitly. The supplied status says admission uses raw intermediate size even after normalization. Keeping that conservative policy is legitimate when it is the stated contract. Claiming admission whenever the normalized result fits requires a different implementation/proof. Specify intermediate workspace requirements as well as final storage limits.

Resolve labels and regions without hiding their meaning. If labels are part of the promised observable semantics, represent the supported labels or prove an abstraction that preserves their relevant uses. A placeholder empty label is not correspondence for arbitrary observed labels. State the supported region-membership and tensor-endpoint representation, including its finite domain.

Specify behavior outside the exact-correspondence domain: resource exhaustion, unsupported operands, and invalid inputs need defined outcomes. Do not obtain a theorem by merely assuming that all inconvenient executions never occur.

C2. Prove actual retirement correspondence

Define a relation between abstract states and hardware states at instruction boundaries, plus the stronger intermediate invariants needed within a multi-cycle instruction.

Establish reset/init, invariant preservation across actual FSM transitions, correctness when an instruction retires, and progress to retirement or the specified failure under the documented environment/scheduling conditions. A statement only about completed instructions is insufficient to rule out a machine that never finishes one.

Cover success and failure behavior, PC and error state, accounting updates, allocation, identities, descriptor zero, capacity boundaries, regions, labels, and endpoints wherever they belong to the promised contract.

For normalization, prove correspondence to the exact last-occurrence list rule, including order wherever observable. Matching only the set of pairs is insufficient if subsequent operations inspect list order or multiplicity. Prove that finite allocation/copying/joining realizes that normalized result under the stated admission rules.

A theorem about the intermediate Gallina kami_step is reusable evidence, but it does not replace the proof about the actual FSM rules. Retain the existing 127 runtime regressions and expand them only to cover concrete missing contract cases.

Pass condition: a checked refinement/retirement result for the actual implementation domain, with progress and resource/failure behavior covered. Regression success alone does not close this gate.

C3. Identify every downstream assurance boundary

For extraction, the printer, the Bluespec compiler, generated Verilog, synthesis, and place-and-route, state whether correspondence is formally proved, independently translation-validated, tested, or trusted. Bind the classification to the exact artifacts.

Do not call the entire chain proved when an edge remains a trust assumption. Conversely, naming a remaining compiler/hardware assumption does not invalidate an already proved abstract theorem.

New LUT, timing, routing, or bitstream claims require artifacts regenerated from this revision. Historical numbers may remain labeled as historical. Physical operating assumptions and measurements belong to those implementation claims, not to existence or uniqueness of the abstract substrate.

Pass condition: the claim about the delivered layer matches the evidence covering that layer. Do not erase a requested implementation target merely by labeling it outside scope.

Gate D — whole-substrate uniqueness, kept separate

The supplied status explicitly keeps uniqueness as a scoped proposal. Interpreter completion and physical refinement do not close that proposal.

If the intended final claim is that there is only one possible substrate, retain a separate target stating the admissibility requirements and a representation-independent equivalence or characterization of the structural core/laws. Prove that the stated alternatives cannot differ in the promised substrate content, without defining adequacy to assume the conclusion.

Existing applicable results may discharge this target. Otherwise it remains open. Correctly labeling it a proposal closes a documentation inconsistency, not the mathematical uniqueness claim.

Pass condition for a proved uniqueness claim: the actual uniqueness/characterization theorem under independently specified requirements. No new implementation is a substitute.

Gate E — final assurance review and reproducible release candidate

Reconstruct the immutable candidate in a clean environment and rebuild its proof dependencies, extraction products, RTL, tests, and monograph. Run the compiled-library checker appropriate to the pinned Coq/Rocq version with the intended dependencies checked; record options and do not use bypass flags to obtain a pass.

Inspect final theorem types, expanded definitions, and assumptions as well as global-axiom reports. Check that concrete preconditions are satisfiable and cover the promised inputs; exhibit nontrivial instances and prove general initialization/preservation where required.

Treat source hashes as provenance evidence, not correctness evidence. Keep raw logs and exit codes. Ensure a failed command cannot be converted into a success by a summary script. Do not count a successful PDF build or a test count as a theorem-applicability check.

Contract amendment requested by Devon on 2026-09-14: a fresh independent reviewer and reproduction on a separate machine/environment are optional follow-up work, not delivery gates. Local theorem-contract review and source-only reconstruction/checking remain mandatory. Do not report the optional checks as performed unless they actually occur.

Do not publish without Devon's explicit release instruction. Preparing the candidate and its evidence does not require pushing it.

Pass condition: every required release claim is supported on one immutable revision, no unresolved counterexample remains within that claim's scope, and every residual assumption is enumerated. A requested but unfinished mathematical/implementation extension must stay marked unfinished.

Immediate next action

Preserve the snapshot. State the counter macro contract. Then implement and prove the reusable VM-controlled equality branch under the existing runner, including what happens after a failed guard. This is the next dependency to resolve before committing to the full interpreter architecture.

In parallel where practical, turn the existing normalization FSM into a retirement proof under the fixed capacity and representation contract. Do not restart the monograph review.

Reporting rule

At each checkpoint report the exact target addressed, files/proof symbols changed, commands actually run, evidence produced, and the next unresolved dependency. Do not use “perfect,” “fully verified,” “unconditional,” or “complete” without naming the object and scope to which the term applies.

The completion statement should identify the immutable revision and say which obligations are discharged under which assumptions. It must not promise that no future reviewer can discover an error.

Technical references behind the recommendations

These references support general verification/computability distinctions; they do not validate the Thiele branch.

Andrej Dudenhefner, Certified Decision Procedures for Two-Counter Machines, FSCD 2022, DOI 10.4230/LIPIcs.FSCD.2022.16. The exact counter instruction set matters to transferred universality/decidability claims.

Rocq Prover 9.1.1 Reference Manual, Libraries and plugins. The compiled-library checker avoids loading development plugins and can reduce the trusted code involved in rechecking.

The supplied v3.2.1 monograph, §§3.7, 10.6, 14, 19. These are historical definitions/context, not evidence that the revised source still has every same implementation detail.