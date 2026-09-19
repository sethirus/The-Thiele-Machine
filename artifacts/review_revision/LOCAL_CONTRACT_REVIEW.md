# Final local source and theorem-contract review, 2026-09-17

This is the implementation session's local review, the Gate E deliverable named in
`COMPLETION_CONTRACT.md`. It is not an independent review and not separate-machine
reproduction. Devon made both optional on 2026-09-14; neither was skipped by
oversight. `STATUS.md` is the completion authority for gate closure; this document
is the audit pass over what that ledger already recorded, checked here against the
current source and the fresh reproduction below rather than taken on trust.

## Completion state

Nine of ten delivery gates are closed: A, B1, B2a, B2b, B2c, B3, B4, C1/C2, C3.
Gate E is in progress; this review and the reproduction it cites are two of its
four pieces. Pinning an immutable local candidate is the remaining piece, proposed
separately rather than executed as part of this review. Gate D and the N1-N3
research items stay deferred per `RESEARCH_BACKLOG.md`; nothing here revisits them.

## Delivery gates, checked

**A** and **B1**: unchanged since prior sessions. Bounded decidability, the
logic-accumulator encoding obstruction, and the abstract counter-access results
hold for their stated domains, no universality conclusion attached.

**B2a/B2b/B2c**: the two-step branch, the counter-drain program, and the
independent-storage pair result all hold for their stated abstract VM domain, not
the 128-word RTL instruction memory. That resource gap is explicit in
`COUNTER_BRANCH_REVIEW.md` and is not treated as closed by the abstract runner.

**B3**: closed under the alternative-construction clause, not the original full
request. The checked object is `VMSelfProgram.U`, a 122-instruction host
interpreting a twelve-opcode guest fragment (HALT, LOAD_IMM, XFER, ADD, SUB, MUL,
AND, OR, SHL, SHR, JUMP, JNEZ) over four unbounded guest registers, with the guest
ledger held in host R11 separately from host `vm_mu`. `self_interpreter_correct`
gives two-direction soundness and completeness; `self_interpreter_divergence`
covers non-termination without treating fuel exhaustion as divergence;
`self_interpreter_malformed` covers bad encodings. The fragment has no structural
instructions, so guest structural fields are ambient, not separately proved. This
is not full-VM self-interpretation; `SELF_INTERPRETER_REVIEW.md` states the gap.

**B4**: closed under the alternative-construction clause: Rice's theorem by
reduction from the complement of MM2 halting over the B3 guest model
(`self_rice`, `self_rice_dual`), with `total_run_obstruction` keeping the
conditional VM-substrate diagonal conditional rather than claiming an internal
recursion theorem. `RICE_REVIEW.md` states this is not the originally requested
general fixed-point/representability instance.

**C1/C2**: closed 2026-09-16. The outside-domain outcome relation's last open
piece, `DispatchLets.dd_rich_fault`, is proved false for all 55 of
`RetireMaster.admitted`'s constructors (`RichFaultMaster.v`, `RichFaultWords.v`,
`RichFaultRetireMaster.v`), closing it alongside the already-checked reachable-
invariant preservation, trace composition, and scheduler-progress obligations.
Combined, every sub-obligation `C1_IMPLEMENTATION_CONTRACT.md` names for C1/C2 is
now checked with zero `Admitted`/`admit` in the closure's dependency set. This
does not extend past what `C1_IMPLEMENTATION_CONTRACT.md` itself scopes: legacy
MORPH/COMPOSE/MORPH_TENSOR/MORPH_GET/MORPH_ASSERT operand encodings are lossy by
design (use the extended forms for the full operand contract); register/heap/
stack addresses are truncated to seven bits before the locality check, so a raw
address like 128 can alias cell zero, and nonaliasing is an admission requirement,
not a hardware guarantee; the reset trap vector (3840) sits outside the 128-word
instruction memory, so a Bianchi trap is a specified outside-domain outcome, not a
claim that a handler there executes; there is no host data-memory load or
CSR-status/heap-base setter, and no internal instruction-loading lock. None of
this is new in this session; it is restated here because a final review is where
a reader should be able to find it without reconstructing it from `STATUS.md`'s
handoff history.

**C3**: closed 2026-09-16 on the current CPU source. Extraction and BSC 2024.07
regeneration reproduce `thielecpu/hardware/rtl/thiele_cpu_kami.v` byte-identical
to the freshly generated `mkModule1_synth.v`. `REALIZATION_ASSURANCE.md`'s three-
way split (proved source wiring, tested byte replay and provenance, trusted
semantic preservation of extraction/BSC/lowering) is unchanged. No synthesis,
timing, place-and-route, or bitstream measurement is claimed; none was attempted.

## Assumption census

Checked twice, independently, on two separately built trees with the same
result: a standalone `coqchk -o` pass over the tree as incrementally built, and
the whole-library `coqchk` step inside the fresh reproduction below. Both report
the same six axioms and nothing else:

- `Coq.Logic.FunctionalExtensionality.functional_extensionality_dep`
- `Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq`
- `Kami.Lib.CommonTactics.cheat` -- a vendor axiom reachable in the wider
  dependency closure; no result cited in this review depends on it, checked by
  per-theorem `Print Assumptions` throughout this project's session history.
- `Coq.Logic.Classical_Prop.classic`, `Coq.Reals.ClassicalDedekindReals.sig_not_dec`,
  `sig_forall_dec` -- ordinary excluded-middle and real-number axioms, traced to
  `kernel/curvature/EinsteinEquations4D.v`, `kernel/thermodynamic/FiniteInformation.v`,
  and `kernel/frontier/F3_PartitionTopologyCrossLink.v`. Unsurprising for
  real-analysis physics proofs. New to this project's written record only because
  no earlier assumption census had checked enough of the tree at once to surface
  them; every narrower C1/C2 closure check genuinely excluded the physics side, it
  did not hide these axioms.

No type-in-type, no unsafe (co)fixpoints, no assumed inductive positivity, in
either run.

## Fresh reproduction evidence

`artifacts/reproduction/20260916T204401Z/`: a fresh, source-only, same-machine
rebuild, 1,260 snapshotted source files, tool binaries hashed and pinned for the
run's duration. `reproduction.json`: `"status": "passed"`, `"exit_code": 0`,
`"source_mismatches_after_build": []`. All 17 recorded commands (`bbv-build`,
`kami-build`, `project-makefile`, `coq-build` over all 421 project files, 12
probes, the whole-library `coqchk`) exit 0. `result.txt` reads `passed`. No
host-compiled artifact was copied in, no `coqchk` bypass flag was used, no
network command ran; `reproduction.json` records all three as false/none
directly, not just by the runner script's design intent.

This run needed three recoveries, each because of the environment or the
reproduction harness, not the mathematics, and each is why the run's own log
history is longer than a clean pass would be:

1. `scripts/reproduce_coq.py`'s `coqchk` step had checked a hand-maintained list
   of 18 modules, unchanged since before most of this week's C1/C2 work and
   never covering the kernel/physics tree. Fixed by deriving the module list from
   `coq/_CoqProject`'s own file list at run time (421 modules), so this cannot
   drift stale again.
2. The build process was killed twice by causes outside the sandbox (a Claude
   Code session restart, then a second interruption whose exact cause is not
   fully pinned down). Both were recovered from cheaply because `make`'s
   incremental cache and the reproduction script's own `--resume` mode carried
   forward everything already built; one truncated `.vo` file from the second
   kill was found and deleted before the retry.
3. `c2_dispatch/FetchFactoring.v`, a literal AST transcript of the CPU's `step`
   rule from 2026-09-14, failed: its own header already called it a snapshot
   "before later CPU changes," and the rule has since changed twice by design
   (removal of the `high_value_locked` fault-gate term, addition of the
   `coupling_desc_label_table` write for the COMPOSE label decision). Removed
   from `DEFAULT_PROBES` with the reasoning recorded in the script; the file
   itself is untouched, kept as the historical record it already was.

None of these three affected the mathematics this review reports on. All three
are recorded in full in `STATUS.md`'s 2026-09-17 handoffs, not just here.

## What this review is not

Not independent: written by the same session that did the work it reviews. Not
separate-machine: one codespace, one toolchain snapshot. Both are optional under
Devon's 2026-09-14 amendment, not silently dropped requirements. Not a claim that
passing compilation, a theorem's existence, or a passing test count establishes
theorem applicability on its own; each gate's paragraph above names the actual
checked object and its stated domain, not just that something compiled.

## What remains for Gate E

Pinning an immutable local candidate revision. Proposed separately, since it
touches git state and this project's standing rule is no commit, tag, or
publication without Devon's explicit instruction. Once pinned, Gate E closes and
`STATUS.md`'s completion line moves from 9/10 to 10/10 gates, with Gate D and the
N1-N3 research items remaining deferred research, not delivery.
