# Review revision status

Base commit: `69b968906eeb88622f6480cd65a011a7d021b890`.
Branch: `work/v3.2.2-review-fixes`.
Review input: the 30-item v3.2.1 checklist, with uploaded-source SHA-256 `c59642623b2074b172a641bee0848a4f32eabdbf54c859438427028371fa36ab`.

## Completion

**90%: 9 of 10 delivery gates closed.** Closed: A, B1, B2a, B2b, B2c, B3, B4, C1/C2, C3. Open: E. Gates have equal weight; partial results do not close a gate. Deferred research is excluded.

B3 and B4 closed on 2026-09-14. C3 closed on 2026-09-16: the extraction pipeline was rerun from the current `ThieleCPUCore.v` after the VM-alignment and label/tensor edits, the provenance manifest and text transform audit were regenerated against the new hashes, and the artifact-specific audit (manifest check, transform replay, 18 pipeline tests) passes with every check at exit 0. **C1/C2 closed on 2026-09-16 (later session):** `dd_rich_fault`'s outside-domain relation -- the last open piece of C1/C2's outside-domain outcome relation, per this ledger's own closure rule stated in the handoff below ("`dd_rich_fault` being open means C1/C2 is not yet closed") -- is now proved for all 55 of `RetireMaster.admitted`'s constructors, with the reachable-invariant, trace-composition and scheduler-progress obligations already checked in earlier sessions and zero `Admitted`/`admit` anywhere in the closure's dependency set. See the current handoff below for the exact theorems and evidence. E remains open. This ledger is the completion authority; individual proof results and passing tests do not close broader gates.

## Current handoff: 2026-09-17 (fresh reproduction passed in full; Gate E's first two pieces done, two remain)

`artifacts/reproduction/20260916T204401Z/` passed completely after the recoveries in the handoffs below: `bbv-build`, `kami-build`, `project-makefile`, `coq-build` (all 421 project files, from a clean source snapshot), all 12 current probes, and the whole-library `coqchk` -- 17 of 17 recorded commands at exit 0, `result.txt` says `passed`, `source_mismatches_after_build` is empty (nothing touched the snapshot mid-build). This is a genuinely fresh, source-only, same-machine reconstruction: 1,260 snapshotted source files, a captured tool-hash record, no host-compiled artifacts copied in, no `coqchk` bypass flags, no network commands (`reproduction.json`'s own recorded fields for all four).

`coqchk`'s `CONTEXT SUMMARY` matches the standalone whole-library pass from the handoff below exactly: `functional_extensionality_dep`, `Eq_rect_eq.eq_rect_eq`, `Kami.Lib.CommonTactics.cheat` (the three already-documented axioms) plus `Classical_Prop.classic`, `ClassicalDedekindReals.sig_not_dec`, `sig_forall_dec` (the physics/kernel classical-analysis axioms this session's broader scope first surfaced). No type-in-type, no unsafe fixpoints, no assumed positivity. This is now checked twice, independently, on two different builds of the same source, with the same result -- as strong a confirmation as a same-machine check can give.

**This satisfies Gate E's first two pieces: a fresh full reproduction, and a dependency-enabled `coqchk` over the whole library.** Two remain: the final local source/theorem-contract review, replacing this file's own `LOCAL_CONTRACT_REVIEW.md`, and pinning an immutable local candidate revision. Gate E is not yet closed; do not read this section as closing it.

Along the way this run found and fixed three real things, each recorded in its own handoff below rather than summarized away here: `scripts/reproduce_coq.py`'s `coqchk` step had silently only ever checked 18 hand-picked modules, never the whole library it claimed to (fixed by deriving the module list from `coq/_CoqProject` itself); background builds on this machine do not survive either a Claude Code process restart or whatever else killed the second attempt at 00:55:42 (mitigated, not solved, by `setsid`/`nohup`/`disown` plus cheap incremental resume); and `c2_dispatch/FetchFactoring.v` was a permanently stale historical probe that could never pass again after 2026-09-14's later CPU edits (removed from `DEFAULT_PROBES`, kept in the tree, flagged for Devon rather than deleted unilaterally).

**Next agent: start here.** Write the final local source/theorem-contract review citing this reproduction's directory, hashes, and the two-axiom-set finding above as evidence -- not `LOCAL_CONTRACT_REVIEW.md`'s 2026-09-14 text, which predates B3/B4/C1/C2/C3 closing and is now almost entirely stale. Then pin an immutable local candidate revision. Neither step commits, tags, or publishes anything without Devon's explicit instruction, per this ledger's standing rule.

## Earlier handoff: 2026-09-17 even later (a stale probe caught by the fresh reproduction itself, exactly what Gate E's process is for)

After the `coq-build` retry (all 421 files, exit 0) and ten passing probes, `probe-10` failed: `artifacts/review_revision/c2_dispatch/FetchFactoring.v:1343`, `reflexivity` on `nth_error (getRules thieleCore) 0 = Some {| attrName := "step"; attrType := dispatch_before_fetch_factoring |}` no longer unifies.

**Diagnosed, not patched over.** `FetchFactoring.v`'s own header already says what it is: "exact AST preservation of the fetch factoring, before later CPU changes" -- a literal ~1300-line transcription of the `step` rule's exact Kami AST as it stood on 2026-09-14, checked by `reflexivity` against the live rule. Diffed the transcript against the current `kami_hw/ThieleCPUCore.v:1336-1344` directly rather than guessing: the current rule's `mc_phase` fault-gate list no longer includes `#high_value_locked` (present in the frozen transcript), and current source has a write the transcript does not, `Write "coupling_desc_label_table" <- IF #mc_enters_fsm ...`. Both match this ledger's own record of deliberate, already-audited edits made after 2026-09-14 (the COMPOSE label/MORPH_TENSOR CPU change in particular explains the new table write). The rule changed on purpose, more than once, exactly as this file predicted it eventually would. This is a stale historical check catching up with reality, not a regression in the CPU or a bug in the probe.

**Fix: stopped asserting this file as live evidence, kept it as the record it already was.** Removed `c2_dispatch/FetchFactoring.v` from `scripts/reproduce_coq.py`'s `DEFAULT_PROBES`, with a comment explaining why so this is not rediscovered as a mystery later. Did not touch the file itself or the CPU source; neither is wrong for what it is. Verified: `pytest tests/test_native_reproduction.py` still 5/5, and `DEFAULT_PROBES` now has 12 entries. Patched the in-progress run's own `reproduction.json` to match (removed its `probe-10` command entry and the file from its `probes` list) so this resume continues at `probe-11` rather than needing an entirely fresh source snapshot and rebuild over a finding that has nothing to do with `coq-build`'s correctness.

**This is worth surfacing to Devon directly, not just filing away:** it means the reproduction pipeline had been silently carrying a check that could never pass again after 2026-09-14, and nothing had run it end to end since to notice. Whether `FetchFactoring.v` is worth keeping at all (versus deleting, since nothing currently re-derives or re-checks its claim against the current rule) is a judgment call about the record, not the mathematics, and is left open rather than decided unilaterally.

## Earlier handoff: 2026-09-17 later (a corrupted `.vo` from the abrupt kill, not a proof defect; removed and resumed)

The third attempt failed fast (33s, exit 2) with `coq-build` itself returning a real, non-guard error: `kami_hw/CouplingComposeRun.vo: premature end of file. Try to rebuild it.` This is `coqc` having been SIGKILLed mid-write of that one file during the second run's abrupt death, leaving a truncated `.vo` on disk that `make`'s timestamp-based dependency tracking had no way to detect as invalid -- it looked up to date, so nothing tried to rebuild it, until something else (`CouplingComposeRetire.v`) tried to load it as a dependency and choked on the truncated marshaled data. Confirmed, not guessed: both `CouplingComposeRun.vo` and its `.glob` were timestamped exactly at the second run's last heartbeat, and a size scan (`find ... -name '*.vo' -size -500c`) found no other undersized file, so this looks like the only casualty from either interruption. Fixed the only way a truncated `.vo` can be fixed: deleted it and its `.glob`, which drops the `.vo` count from 393 to 392 and forces `make` to recompile that one file on the next run rather than trusting a stale timestamp against corrupt content.

Separately, the root cause of that second death is now less certain than the handoff below assumed. That handoff attributed it to the container restart it found evidence for (`docker-init` freshly started). But the guard log's last write was at 00:55:42 and the container's `docker-init` start time was 03:09:38 -- over two hours later. The build was already dead for two hours before the container-restart evidence appeared, so something else killed the detached, init-reparented process at 00:55:42, and the later container restart is a second, separate event this handoff cannot explain from available evidence (no `MEMORY`/`SYSTEM`/`TIME` guard trailer line was written for either death, meaning both were external SIGKILLs the guard script itself never got to react to, not a threshold it recognized and handled). Whatever is reaping detached background processes in this environment, `setsid`/`nohup`/`disown` is necessary but has not been sufficient on its own. **The mitigation that matters in practice is the cheap-resume property, not preventing the kill**: each interruption has cost at most the one file being written at the moment of death, recoverable by finding and deleting it, because `make`'s incremental cache carries everything else forward untouched.

**If `coq-build` fails with "premature end of file" or similar corruption again:** this is the pattern to expect, not a new class of problem. Find the named `.vo` (and its `.glob`), delete both, and resume; do not assume the source or the proofs are wrong. If a build dies without producing any error at all (silent process disappearance, no trailer line in the guard log), check the `.vo` file that `coq-build.log`'s last `COQC` line names as the one most recently started -- that is the one most likely to be mid-write.

## Earlier handoff: 2026-09-17 (a second interruption was the container itself restarting, not just the CLI process; resumed again, 392/421 already compiled)

The detachment fix in the handoff below (`setsid`/`nohup`/`disown`, reparented to init) protects against the Claude Code CLI process restarting. It does not and cannot protect against the container itself restarting: `docker-init` (PID 1) showed a fresh start time, meaning the whole container, not just the CLI, came down and came back. No process inside a container survives that regardless of how it was detached; this is outside anything fixable from inside the sandbox. Found by checking `ps -eo pid,lstart,cmd | sort` for PID 1's start time against the current time, after the guard log had gone quiet for over two hours with no trailing `rc=` line (i.e. killed, not exited).

**What actually survived: everything on disk.** `/workspaces` is a persistent volume; only the process tree was lost, not the filesystem. `find .../source/coq -name '*.vo' | wc -l` showed 392 of 421 project files already compiled before this interruption, so `coq-build`'s incremental `make` had gotten nearly all the way through despite two separate interruptions before finishing. Resumed the same way as the handoff below (`reproduce_guarded.sh` auto-detects the existing `reproduction.json` and adds `--resume`), same output directory, same guard thresholds. Only the remaining ~29 files, the 13 probes, and the final whole-library `coqchk` are left.

**If this happens again:** do not assume lost work. Check `find artifacts/reproduction/20260916T204401Z/source/coq -name '*.vo' | wc -l` against 421 before concluding anything needs to be redone, then just re-run `reproduce_guarded.sh` on the same directory. `make`'s own incremental dependency tracking is what makes this cheap; nothing about the guard script needs to know how far in a single `coq-build` invocation got.

## Earlier handoff: 2026-09-17 (fresh reproduction interrupted by a session restart, not a proof or build defect; resumed detached)

The standalone whole-library `coqchk` pass from the handoff below finished clean while this session was still active: exit 0, 1990s, peak RSS 1041MB, no type-in-type, no unsafe fixpoints, no assumed positivity. Its `CONTEXT SUMMARY` is wider than any closure checked before it, because it is the first check to cover the physics/kernel side of the tree in the same pass as the hardware side. Beyond the two axioms and the unused vendor one every C1/C2 closure already reported, it also lists `Coq.Logic.Classical_Prop.classic`, `Coq.Reals.ClassicalDedekindReals.sig_not_dec` and `sig_forall_dec` -- ordinary excluded-middle and real-number axioms, traced to `kernel/curvature/EinsteinEquations4D.v`, `kernel/thermodynamic/FiniteInformation.v` and `kernel/frontier/F3_PartitionTopologyCrossLink.v`, reached through `MasterSummary.v`/`ThieleMachineComplete.v`. Ordinary for real-analysis physics proofs, but new to the record: no prior assumption census had covered enough of the tree at once to surface them. This belongs in the final contract review below as a dated finding, not folded silently into the existing two-axiom framing.

That result is evidence about the tree as it stood, not yet a fresh reproduction. The fresh `reproduce_coq.py` run this calls for next was launched the same session, in the background, guarded by an external watchdog (`/home/codespace/.cache/thiele-guard/reproduce_guarded.sh`) for the same reason `mk.sh` exists: the script itself does not cap memory or per-stage time. It reached `bbv-build`, `kami-build` and `project-makefile` (all exit 0) and about 24 minutes into `coq-build` before this session's own Claude Code process was replaced (a restart external to anything in this conversation, not a `git status` change or a proof failure -- confirmed by checking process ancestry after the fact). The background job had been started as a plain backgrounded shell command, which is tied to the launching process's lifecycle; when that process went away, so did the build, mid-file, with no error in any log.

**Not a defect to fix, a detachment gap to close.** Relaunched with `setsid nohup ... </dev/null >log 2>&1 & disown`, confirmed by `ps` to be reparented to init (PPID 1) in its own session, independent of both this shell and the Claude Code process. `reproduce_guarded.sh` now also auto-detects an existing `reproduction.json` in its output directory and adds `--resume`, so restarting it replays nothing already at exit 0 -- `bbv-build`, `kami-build` and `project-makefile` were not redone. Running as of this handoff: output directory `artifacts/reproduction/20260916T204401Z`, guard log `/home/codespace/.cache/thiele-guard/logs/reproduce_guarded.log`, same 1800MB/process and 1200MB-system-available guard thresholds as every other build in this project, 28800s (8h) outer cap as a hang safety net rather than an expected duration.

**If a future session finds this still running or interrupted again:** check `ps aux | grep reproduce_guarded` for a live, init-reparented process before assuming it died; check `artifacts/reproduction/20260916T204401Z/reproduction.json`'s `status`/`exit_code`/per-command `exit_code` fields for exactly where it stopped; and re-run the same `reproduce_guarded.sh <dir> 28800` command (not a fresh directory) to resume, since the source snapshot and manifest hash are already pinned and the script refuses to resume against changed source.

## Earlier handoff: 2026-09-16 night (Gate E started; reproduction script's coqchk scope corrected to the whole library; a standalone whole-library coqchk pass is running)

C1/C2 closed in the handoff below. This session picks up Gate E, the one remaining delivery gate, using its own four-piece scope from `COMPLETION_CONTRACT.md`: a fresh full source reproduction, a dependency-enabled `coqchk` over the whole library, the final local contract review, and an immutable local candidate.

**A scope gap found in `scripts/reproduce_coq.py` before trusting its coqchk step.** `DEFAULT_LIBRARIES` was a hand-maintained tuple of 18 module names. It predated most of this week's C1/C2 work and every kernel/physics module: it had never included `KamiHW.RetireMaster`, `KamiHW.RichFaultRetireMaster`, or anything under `Kernel.*` beyond three CM2/self-interpreter files. A reproduction run against that list would report a pass while never touching most of what the ledger calls closed. This matches the prior handoff's own finding that the `RichFaultRetireMaster` closure check "does not cover modules outside that one file's dependency graph, e.g. the kernel VM/physics developments" -- the same gap, found again from the other direction.

Fixed by replacing the frozen tuple with `discover_project_libraries`, a function that parses `coq/_CoqProject`'s own file list (421 entries) and its `-R`/`-Q` roots into fully qualified module names at run time. A fresh reproduction now hands `coqchk` all 421 modules -- literally the whole project library `_CoqProject` declares, not a curated subset -- so this cannot silently drift out of date again as files are added. `--resume` is unaffected: it replays whatever library list a prior run already captured in its `reproduction.json`. Checked: `python3 -m pytest tests/test_native_reproduction.py`, 5 passed; a `--prepare-only` dry run shows the generated `coqchk` command carrying all 421 modules, including this session's `KamiHW.RichFaultWords`, `RichFaultMaster`, `RichFaultRetireMaster`, `OutsideDomainMaster`, and `RetireProgress`.

**Standalone whole-library coqchk launched, result not yet known.** Before committing to the multi-hour clean rebuild that a fresh `reproduce_coq.py` run requires, I launched a guarded `coqchk -o` pass over the tree as it stands right now (already fully built, `make -C coq -n all` schedules nothing) against all 421 modules from the fix above. This is a faster signal on whether the whole library actually checks clean; it is not itself a fresh reproduction and does not by itself satisfy Gate E's first clause. Guard: `/home/codespace/.cache/thiele-guard/coqchk_whole.sh`, run in the background, log at `/home/codespace/.cache/thiele-guard/logs/coqchk_whole.log`, killed if any single process exceeds 1800MB RSS, system `MemAvailable` drops below 1200MB, or wall time exceeds 10800s. This machine has 2 CPUs and 8GB RAM with three other idle Claude sessions on the same repo holding memory, so headroom is tighter than earlier sessions had; the 2026-09-14 OOM incident (a `-j2` build killed the VS Code server) is why this runs alone rather than concurrently with anything else heavy.

**Deliberately not started yet: the fresh `reproduce_coq.py` run itself.** Running it at the same time as the standalone coqchk pass above risks the same OOM failure mode on this machine. It starts once the standalone pass finishes (pass, fail, or guard-killed) and reports what it found.

**Next agent: start here.**
1. Check `/home/codespace/.cache/thiele-guard/logs/coqchk_whole.log` and the guard's exit line for the standalone pass above. If it failed on a real inconsistency (not a guard kill), that is a proof defect to fix before anything else in Gate E is meaningful. If it was guard-killed on memory or time, raise the ceiling or split the module list and retry; do not treat a guard kill as a pass or a failure of the mathematics.
2. Once that result is known, run `python3 scripts/reproduce_coq.py --jobs 1` to a full pass from a fresh source snapshot, guarded the same way (`mk.sh`'s per-coqc RSS ceiling and system-available floor, applied externally since the script itself does not watch memory). This rebuilds bbv, Kami, the whole project, all 13 probes, and finally the corrected whole-library coqchk in one run. Expect it to take substantially longer than any single check so far in this project; if a guard kill interrupts it, `--resume --output <same dir>` continues from the last completed command rather than restarting, since it verifies the captured source hasn't changed first.
3. Only after that reproduction passes, write the final local source/theorem-contract review, replacing this file's own `LOCAL_CONTRACT_REVIEW.md`, citing the reproduction's directory, hashes, and exit codes as evidence, not the older 2026-09-14 interim review or a running stage.
4. Pin an immutable local candidate revision. No commit, tag, or publication without Devon's explicit instruction, per this ledger's standing rule.

## Current handoff: 2026-09-16 later (C1/C2 closed: `dd_rich_fault`'s outside-domain relation proved for all 55 admitted constructors)

Continuing directly from the handoff below, which scoped `dd_rich_fault` as the one remaining piece of C1/C2's outside-domain outcome relation and left it unstarted ("a fresh session should start by reading `dd_rich_fault`'s six disjuncts in `DispatchLets.v:125-126` against which opcodes/formats the `admitted` constructors in `RetireMaster.v` actually use"). That reading is what closed it, faster than the handoff expected: the six disjuncts turned out to be almost entirely closed constants once the word encoding is fixed, not a per-opcode case analysis.

**What the reading found.** `DispatchLets.dd_rich_fault` is `dd_isa_version_invalid || dd_format_invalid || dd_inline_malformed || dd_generic_desc_range_fault || dd_rich_table_overflow || dd_cert_desc_invalid`. Every one of `RetireMaster.admitted`'s 55 constructors fetches one of exactly two word shapes: `StepEval.legacy_word op a b c` (46 constructors: format `FMT_LEGACY`, flags 0, isa 2, all baked into the word's fixed top-96-bit lane) or `StepFieldsMorph.rich_word fmt op a b c e` (9 constructors: the six morph/compose "_ext" opcodes at `fmt = 3` = `FMT_MORPH_INLINE`, MORPH_ASSERT's extended form at `fmt = 5` = `FMT_CERT_INLINE`; flags fixed to 4, isa 2). Neither shape ever instantiates `FMT_DESC`, so `dd_generic_desc_range_fault` and `dd_cert_desc_invalid` (both gated on `format_id == FMT_DESC`) are false for every admitted instruction by format alone -- no admission premise needed at all, for any opcode. `dd_isa_version_invalid` is false because isa is always 2 in both word shapes. `dd_format_invalid` is false because `dd_format_allowed_for_opcode`'s `FMT_LEGACY` branch is unconditionally true, and the rich encodings' fixed format matches exactly the opcode classes (`dd_is_morph_opcode`, `dd_is_cert_opcode`) they are used with. `dd_inline_malformed` is false because the legacy word's flags are 0 (satisfying the reserved-flag check vacuously) and the rich word's fixed flags value 4 decodes to descriptor kind 0 (zero) and inline length 4 (neither zero nor over 8), exactly satisfying `dd_inline_payload_fault`'s own well-formedness test. The **only** disjunct that reads live hardware state is `dd_rich_table_overflow`, and only for the three morph-allocating opcodes (MORPH, COMPOSE, MORPH_ID) -- and exactly those constructors (`adm_morph_id`, `adm_morph_id_ext`, `adm_morph_ext`, `adm_morph_ext_fault`, `adm_compose_ext`, `adm_compose_ext_fault`) already carry the `hw_morph_next_id`/`hw_coupling_desc_next_id` room-bound premises the guard needs (confirmed by mechanically extracting every constructor's premise list from `RetireMaster.v` and checking which ones mention the room bounds -- the room bound is present in exactly the six constructors that need it and absent from all 49 that do not, matching the mathematics with no gaps). So closing this obligation needed **zero new admission premises**: every fact used was already either a closed constant or a premise the constructor already carried.

**What is checked and in the tree.** Three new files, all registered, all `Qed`, zero `Admitted`/`admit`.

- `kami_hw/RichFaultWords.v`: the word-encoding bridge. `StepFieldsMorph.rich_word fmt op a b c e` (the fixed-flags morph/cert-inline encoding) is proved equal to `RichWordDecode.rich_word` (the general six-encoding word `OutsideDomainMaster.v` already uses) instantiated at `isa = 2`, `flags = 4`, `reserved = 0`, `format_id = fmt`, for `fmt ∈ {3, 5}` -- a closed computation (`rich_word_tail_eq`, `vm_compute`) since both format literals are concrete. `rich_op_correct`, `rich_isa_correct`, `rich_format_correct`, `rich_flags_correct` transfer `RichWordDecode.v`'s `rw_*_correct` decode lemmas through the bridge.
- `kami_hw/RichFaultMaster.v`: `dd_rich_fault_unfold` (the flat six-leaf disjunction, mirroring `OutsideDomainMaster.v`'s `_unfold` lemmas), one falsity lemma per leaf (format-gated leaves proved via a `format_id <> FMT_DESC` premise with no opcode reasoning; `dd_rich_table_overflow_false` opcode/format-generic over already-decoded values, taking the room bound only as a conditional hypothesis keyed to the three morph-allocating opcodes), and three top-level theorems: `dd_rich_fault_false_legacy` (universal over every legacy-word opcode), `dd_rich_fault_false_morph_inline` (universal over the seven morph-class opcodes at `fmt = 3`), `dd_rich_fault_false_cert_inline` (MORPH_ASSERT at `fmt = 5`, no premise at all). Each is fully general over its word shape's operand bits and (for the rich case) opcode within its class -- not just the specific instances `RetireMaster.v` happens to use, so this is stronger than a 55-way case enumeration.
- `kami_hw/RichFaultRetireMaster.v` (generated): one corollary per `RetireMaster.admitted` constructor, `dd_rich_fault b (<constructor's own fetched word>) = false`, each proved by a one-line `apply` of the appropriate theorem above. Built the way the codebase's other generator scripts are: a Python pass reads each constructor's `forall`-header and `step_fetched` word call verbatim out of `RetireMaster.v`'s own `admitted` inductive (not retyped by hand, to avoid transposing a bit-variable among the ~24-56 per constructor), cross-checks which room-bound premises each constructor actually carries, and emits the matching lemma; every one of the 55 was still verified by the guarded `coqc`, not assumed correct from the generator (two bugs were caught this way during generation, see below).

**Checked:** guarded `coqc` on all three files, exit 0, 2-3s each. `Print Assumptions` on the three top-level `RichFaultMaster` theorems and a representative sample of `RichFaultRetireMaster` corollaries (`_add`, `_morph_id`, `_morph_ext`, `_compose_ext`, `_compose_ext_fault`, `_morph_assert_ext`, `_pdiscover`, `_chsh_lassert`, `_lassert_sat`) shows only the two already-documented inherited axioms (`functional_extensionality_dep`, `Eq_rect_eq.eq_rect_eq`) -- no new axioms, no `cheat`. Full guarded `make -C coq -k all`: exit 0; `make -C coq -n all`: schedules nothing further. A dependency-enabled `coqchk -o` run over `KamiHW.RichFaultRetireMaster` (its full transitive closure -- effectively the whole library, since `RetireMaster.v` and everything it depends on is upstream of it) ran to completion at the end of this session: exit 0, 1710s, no bypass flags. Its context summary: axioms `functional_extensionality_dep`, `Kami.Lib.CommonTactics.cheat` (library-wide vendor axiom; the per-theorem `Print Assumptions` runs above confirm none of this session's new results depend on it) and `Eq_rect_eq.eq_rect_eq` -- the same three the library context has always listed, no new ones; no type-in-type, no unsafe (co)fixpoints, no assumed positivity.

**Two generator bugs found and fixed while building this, recorded so the pattern is not rediscovered.** (1) A naive `args.split()` was used both to call the word constructor (correct) and as the corollary's own `forall`/`intros` binder list (wrong): `adm_pdiscover`'s fetched word is `pdiscover_word a0..a7 false false false false false false false false c0..c7` (the middle eight bits are hardwired to the literal `false`, not left as bound variables), so the naive binder list tried to name `false` as a variable and Coq rejected it ("Cannot infer the type of `false`"). Fixed by deriving the binder list from the constructor's own `forall` header (filtering literal `true`/`false` tokens out of the word-call argument list), not from the word-call arguments directly. (2) The generator's class-membership proof for the last disjunct of a 7-way `\/` chain (`op = OP_MORPH \/ ... \/ op = OP_MORPH_GET`) emitted `right; right; right; right; right; right.` with no closing `reflexivity`, since the off-by-one logic assumed the last case needed no `left` (true) but forgot it still needs to close the equality goal it lands on ("Wrong bullet" / focus error). Fixed by always appending `reflexivity` regardless of position.

**Proof trap recorded for future `dd_*` reduction work in this file family.** Kami's named `dd_*` accessors (`dd_is_morph_opcode`, `dd_morph_alloc_opcode`, and the like) are referenced from other `dd_*` definitions as opaque `Var` values (the generator embeds `Var type (SyntaxKind Bool) (dd_foo b w)`, i.e. an already-evaluated Coq function application), not by re-inlining their underlying Kami expression tree. Two consequences, both hit and fixed in this session: (a) rewriting a decode fact (e.g. `dd_flags b w = natToWord 16 4`) only reaches the places that read it if every intermediate `dd_*` accessor between the goal's surface and the read site is also in the `unfold` list -- `dd_inline_malformed_false_morph_inline`'s first attempt omitted `dd_desc_kind`/`dd_inline_len` from the unfold list, leaving `dd_flags bd (rich_word ...)` buried one level deeper than the rewrite could see, and the subsequent `vm_compute` tried to reduce through the *symbolic* `combine e (...)` word structure directly (the exact trap `RichWordDecode.v`'s own header comment warns about) instead of hitting the now-concrete flags value, ballooning to a 2.2 GB guard kill. (b) When the *same* Kami subexpression (e.g. `dd_opcode b w == OP_MORPH`) appears twice in a definition -- once directly, once via an opaque `dd_morph_alloc_opcode b w` reference -- a single `destruct (weq (dd_opcode b w) OP_MORPH)` only resolves *both* occurrences if `dd_morph_alloc_opcode` is unfolded *before* the destruct (so both copies are the literal same post-`cbn` term); unfolding it separately inside one branch after the fact creates a second, independently-destructed copy and leaves the other stuck. A `Ltac name := cbn [...] .` also cannot take an `in H` clause the way the built-in `cbn`/`cbv` can; write the reduction out at the hypothesis site directly instead.

**What this closes, and what it does not.** Per this ledger's own rule stated in the handoff below, `dd_rich_fault` was the last open piece of C1/C2's outside-domain outcome relation: the opcode-membership half (`OutsideDomain.v`) and the ten guard-class opcodes' bound-premise half across every encoding (`OutsideDomainMaster.v`) were already closed; `hwb_bianchi` is a direct premise on every admitted constructor, not derived; `dd_morph_runtime_fault` is admitted by design per `StepFaults.v`'s own scoping. With `dd_rich_fault` now closed, the outside-domain relation is complete for every guard the contract requires C2 to prove ("Fault predicates are the actual dispatch LET expressions. C2 must split on them and prove each result; there is no assumed fault-correctness axiom," `C1_IMPLEMENTATION_CONTRACT.md:170-171`). Combined with the reachable-invariant preservation (`TableInvariantsPreserved.v`, all 55 constructors), the reachable-state and trace-composition theorem (`TableInvariantsReachable.v`) and scheduler progress to retirement (`RetireProgress.v`) already checked in earlier sessions, every sub-obligation this ledger has tracked for C1/C2 is now checked, with a clean `grep` for `Admitted`/`admit` across the whole closure returning nothing. **This ledger therefore records C1/C2 as closed.** This does **not** close Gate E: fresh source-only reproduction, a full dependency-enabled `coqchk` pass over the *entire* library (not just this closure), the final local source/theorem-contract review (replacing the interim `LOCAL_CONTRACT_REVIEW.md`), and pinning an immutable local candidate are all still open and unattempted this session.

**Next agent: start here.** Gate E is now the only open delivery gate. Its four pieces, per `COMPLETION_CONTRACT.md`: (1) run `python3 scripts/reproduce_coq.py` to a full pass from a fresh source snapshot (the last recorded full pass, `20260913T192742.493929Z`, predates this entire C1/C2 closure and the C3 regeneration, so it needs rerunning, not just citing); (2) a full dependency-enabled `coqchk` over the whole library (the run completed this session, scoped to `KamiHW.RichFaultRetireMaster`'s transitive closure -- exit 0, 1710s, same three already-documented library axioms, no bypass -- is a useful data point and covers essentially all of `kami_hw/` and `Kernel`, but is not this deliverable on its own: it does not include modules entirely outside that dependency graph, e.g. some of the standalone physics/spacetime developments, so the full-library invocation from `reproduce_coq.py` still needs its own run); (3) write the final local source/theorem-contract review, replacing `LOCAL_CONTRACT_REVIEW.md`; (4) pin an immutable local candidate revision. Separate-machine reproduction and an independent reviewer remain optional under Devon's 2026-09-14 amendment. No commit, tag or publication without Devon's explicit instruction.

## Earlier handoff: 2026-09-16 late (guard-class outside-domain master theorem closed; `rich_fault` identified as a separate, still-open obligation -- scope correction to the handoff below)

The handoff immediately below closed the ten guard-class opcodes' own bound-premise-as-decoded-guard-falsity lemmas over every ISA-v2 encoding, and flagged assembling them into the actual master statement as the next step. That assembly is now done: `kami_hw/OutsideDomainMaster.v` (new, registered) proves, for each of the ten guard-class opcodes, `dd_locality_violation || dd_ptable_overflow_violation || dd_nfi_violation = false` given that opcode's own admission bound -- the exact conclusion `OutsideDomain.not_guard_of_opcode` reaches for off-guard-class opcodes by computation, reached here through the bound instead. Built as: two `_unfold` lemmas exposing `dd_locality_violation`/`dd_ptable_overflow_violation` as their flat four-way/three-way disjunctions (already how `DispatchLets.v` defines them, so the unfold is one `dd_cbn`), eight generic "sibling nullification" lemmas (`dd_<leaf>_false_of_neq`, one per disjunction leaf: load, store, call, ret, pnew, psplit, pmerge, nfi) showing a leaf is false whenever the decoded opcode does not match its own gating constant -- fully encoding-independent, since they never look past `dd_opcode` -- and ten combination theorems, each rewriting its own leaf via the already-proved `Rich*_false_rich` bound lemma and the other seven leaves via sibling nullification (opcode mismatch discharged by `discriminate` off the known `rw_op_correct` fact). Checked with the guarded `coqc`: exit 0, 2s, first attempt, no new traps. `Print Assumptions` on all ten master theorems: only the two standard inherited axioms. `make -n all`: schedules nothing further.

Stated over `rich_word` throughout, this single file already covers all six ISA-v2 encodings (legacy included as `fid = FMT_LEGACY`), so the four `Legacy*Guard.v` files are now subsumed for this purpose (kept in the tree since nothing requires deleting them, but the master theorem does not use them). This closes the guard-class half of C1's outside-domain relation completely: `OutsideDomain.not_guard_of_opcode` (off-guard-class opcodes, by computation) plus `OutsideDomainMaster`'s ten theorems (guard-class opcodes, by admission bound) together cover every opcode against the three guards `dd_guard_opcode` names (locality, partition-overflow, NFI).

**Scope correction, found while integrating this.** The night handoff's phrase "the rich-format guard, which needs the same lane identity for the other five encodings" conflated two different things that happen to share the word "rich": (1) restating the ten guard-class opcodes' own bounds over the rich *encodings* -- what `RichWordDecode.v` and this handoff's work actually closed -- and (2) `DispatchLets.dd_rich_fault`, a fifth, separate guard (distinct from the three `guard_opcodes` covers) checking ISA-version validity, format validity per opcode, inline-payload malformation, descriptor-range faults across the morph/coupling/meta tables, rich-table overflow, and cert-descriptor validity. `OutsideDomain.v`'s own docstring already flagged `dd_rich_fault` as "not covered here... needs a per-encoding argument," separately from the guard-class work, and `C1_IMPLEMENTATION_CONTRACT.md:177` confirms it is its own contractual outside-domain outcome, not closed by anything in this handoff or the one below. `hwb_bianchi` (the fourth premise for `dd_trap`) is not part of this obligation at all -- every `admitted` constructor already carries `hwb_bianchi b = false` as a direct hypothesis, not something derived. `dd_morph_runtime_fault` remains admitted by design per `StepFaults.v`'s own scoping, unaffected.

**What remains for C1/C2, precisely.** `dd_rich_fault`'s own outside-domain relation: for each opcode/format combination the admitted constructors use, restate the admission conditions (well-formed format, valid descriptors, table capacity) as `dd_rich_fault`'s decoded falsity. This is substantially larger than the guard-class work just closed -- it touches every opcode's format-validity interaction, not ten opcodes with one shared shape, and needs the morph/coupling/meta descriptor table premises (`hwb_table_invariants`, already proved reachable) threaded through per opcode rather than a single opcode-mismatch argument. Not scoped in detail yet; a fresh session should start by reading `dd_rich_fault`'s six disjuncts in `DispatchLets.v:125-126` against which opcodes/formats the `admitted` constructors in `RetireMaster.v` actually use, to see how much of it is vacuous per opcode (e.g. `dd_generic_desc_range_fault` only fires under `FMT_DESC`) before assuming all six disjuncts need separate arguments for all opcodes. Only after that closes does Gate E (fresh reproduction, dependency-enabled `coqchk`, final local contract review, immutable candidate) become attemptable -- STATUS.md's own rule is Gate E starts only after C1/C2 itself closes, and `dd_rich_fault` being open means C1/C2 is not yet closed.

## Earlier handoff: 2026-09-16 later (rich-format guard lemmas closed for all ten guard-class opcodes; legacy-vs-rich lane identity found to be a single generalization, not five per-encoding files)

Continuing from the night handoff below, which left two things open: (1) the rich-format lane decode identity for the five non-legacy encodings, and (2) the master theorem assembly. Item (1) is now closed, and closed more cheaply than planned: `kami_hw/RichWordDecode.v` (found already in the tree at the start of this handoff, registered but not yet recorded here -- built by an untracked prior session) shows the six ISA-v2 encodings do not actually lay out `dd_opcode`/`dd_op_a`/`dd_op_b`/`dd_cost_v`/`dd_isa_version`/`dd_format_id`/`dd_flags`/`dd_ext0` differently: every one is a fixed `ConstExtract` at a fixed absolute bit offset in `DispatchLets.v`, independent of what `format_id` decodes to -- only the *interpretation* of those bits depends on the format. So instead of five separate `<encoding>_word`/`<encoding>_nat` constructors and five lane-arithmetic files (the night handoff's plan), one general `rich_word` constructor with the header fields (`isa`, `fid`, `flags`, `reserved`, `ext0`) left as arbitrary parameters covers all six encodings at once, including legacy as the special case `fid = FMT_LEGACY, flags = ext0 = 0`. `rw_op_correct`/`rw_a_correct`/`rw_b_correct`/`rw_c_correct`/`rw_isa_correct`/`rw_format_correct`/`rw_flags_correct`/`rw_ext0_correct` mirror `LegacyWordDecode.v`'s `dd_*_correct` lemmas exactly.

This handoff used that to close the guard-class side of the same gap: all ten guard-class opcodes' bound-premise-as-decoded-guard-falsity lemmas, now proved over `rich_word` (hence over every encoding) rather than `legacy_word` alone. `kami_hw/RichLoadGuard.v` (hand-written first, as the demonstration LOAD played for the legacy files) confirmed the technique carries over with **zero new traps**: the guard's own address getter and mux structure stay fully opaque to the word's encoding throughout the proof (never unfolded against it), so the only encoding fact any guard lemma actually needs is the opcode decode -- `RichWordDecode.rw_op_correct` in place of `LegacyWordDecode.dd_op_correct` -- and for PDISCOVER, `rw_b_correct`/`rw_c_correct` in place of `dd_b_correct`/`dd_c_correct`. Every other tactic line is byte-identical to its legacy counterpart. Guarded `coqc`: exit 0, 15s (includes `Kami.Kami` reload).

The other nine then generated via a Python script (`/tmp/.../scratchpad/gen_rich_guards.py` this session, not checked in) from the same per-opcode parameter tables the night handoff's legacy generator used, split into the same three files by shape: `kami_hw/RichLocalityGuard.v` (STORE, CALL, RET, HEAP_LOAD, HEAP_STORE), `kami_hw/RichPartitionGuard.v` (PNEW, PSPLIT, PMERGE), `kami_hw/RichNfiGuard.v` (PDISCOVER). All three registered in `_CoqProject` and checked individually with the guarded `coqc`: exit 0, 1-2s each. `Print Assumptions` on all ten `*_false_rich` lemmas: only `functional_extensionality_dep` and `Eq_rect_eq.eq_rect_eq`, the same two axioms every other C1/C2 result carries -- no new axioms, zero `Admitted`/`admit` across all four new files. `make -C coq -n all`: schedules nothing further, confirming everything is current and nothing downstream broke.

**What this does not close.** All ten guard-class opcodes now have their bound premise restated as their decoded guard's falsity over *every* ISA-v2 encoding (legacy via the night handoff's four files, all six via this handoff's four `Rich*.v` files). Still open, per `OutsideDomain.v`'s closing note:

1. Assembling all ten opcodes' lemmas (twenty lemmas total: ten legacy-specific plus ten format-general) into `OutsideDomain.v`'s actual master statement (`not_guard_of_opcode` plus the ten `op_off_*`-style premise lemmas, generalized the way that file's own closing note describes) -- not yet done; the lemmas exist as standalone facts, not yet wired into one theorem. Since the ten `Rich*_false_rich` lemmas already generalize their legacy counterparts (rich_word's fid can be instantiated to FMT_LEGACY to recover the legacy statement), the legacy-specific lemmas may turn out to be redundant once the master theorem is stated directly over `rich_word` -- worth checking before assembly, since it could mean deleting four files rather than keeping all eight.
2. Everything downstream of that: C1/C2 gate closure still needs Gate E in full (fresh reproduction, dependency-enabled `coqchk`, final local contract review, immutable candidate) after C1/C2 itself closes.

**Next agent: start here.** Item 1 is now the only thing standing between the guard-class half of the outside-domain relation and being fully closed across every encoding. Read `OutsideDomain.v`'s closing note (the comment block after `op_member_guard_of_in`) for the exact shape the master statement needs, then check whether stating it directly over `rich_word` (parameterized by the header fields) subsumes the four legacy-specific files before wiring both in.

## Earlier handoff: 2026-09-16 night (all ten guard-class opcodes' bound-premise-as-decoded-guard-falsity lemmas closed, legacy encoding only)

Continuing directly from the evening handoff below: the nine guard-class opcodes it left open (STORE, HEAP_LOAD, HEAP_STORE, CALL, RET, PNEW, PSPLIT, PMERGE, PDISCOVER) are now done, joining LOAD. All nine follow `LegacyLoadGuard.v`'s proved technique with no new tricks; they split into three shapes and landed as three new files.

**`kami_hw/LegacyLocalityGuard.v`** (new, registered): STORE, CALL, RET, HEAP_LOAD, HEAP_STORE. Same shape as `LegacyLoadGuard.v`'s LOAD proof -- decode the opcode via `LegacyWordDecode.dd_op_correct`, resolve the `dd_is_*_op`/mux `weq` terms (CALL and RET have no mux, so only one `destruct`; the two heap variants take the heap branch of the same mux the non-heap proof left unhandled), close with the `check_bounds`/`wlt_dec` reasoning `StepRefineCommon.region_ok_of_lt` already names. The bound premise is stated over the opaque address getter (`dd_mem_addr_a`, `dd_sp_addr`, `dd_sp_dec_addr`, `dd_heap_addr`, `dd_heap_addr_a`) exactly as LOAD's was over `dd_mem_addr` -- these read a register value, not a word-decoded field, so no further decoding of operand bytes is needed, only the opcode.

**`kami_hw/LegacyPartitionGuard.v`** (new, registered): PNEW, PSPLIT, PMERGE. Simpler than the locality guards: `dd_pnew_overflow`/`dd_psplit_overflow`/`dd_pmerge_overflow` read no operand byte at all, only `hw_pt_next_id` and the opcode, so only the opcode needs decoding. The capacity arithmetic mirrors `StepRefineCommon.pt_room_one_of_lt`/`pt_room_two_of_le` exactly, since `dd_ptable_room_one`/`dd_ptable_room_two` are the same comparison at the Kami-expression level those state directly in Gallina. One real trap, found by reproducing a failure: `dd_cbn`'s `cbn` list (copied from `LegacyLoadGuard.v`) did not include `evalBinBit`, so the Kami `+` in `dd_ptable_room_two` stayed as an unreduced `evalBinBit (Add _) x y` application instead of `wplus x y`, and `rewrite wordToNat_wplus_7` could not find its pattern. Fix: add `evalBinBit` to `dd_cbn`'s unfold list. This only matters when a guard's own top-level expression contains arithmetic (as `dd_ptable_room_two` does); the locality guards never needed it because their address getters are opaque.

**`kami_hw/LegacyNfiGuard.v`** (new, registered): PDISCOVER. Unlike the other nine, `dd_nfi_violation` compares two word-decoded operand bytes directly (`dd_cost_v` against `dd_op_b`, both zero-extended), not a register-read address, so this needed `LegacyWordDecode.dd_b_correct`/`dd_c_correct` plus `StepRefineCommon.wordToNat_zext8_ext` rather than the `check_bounds` route. Second trap, also found by reproducing a failure: `rewrite wordToNat_zext8_ext ... in Hlt` failed because `Hlt`'s type after `destruct (wlt_dec _ _)` is the abstract `wlt` proposition, not yet a `wordToNat _ < wordToNat _` inequality, so the `wordToNat (evalZeroExtendTrunc ...)` pattern was not syntactically present. Fix: `apply wlt_lt in Hlt` first to expose the `wordToNat` form, then rewrite. (`LegacyPartitionGuard.v`'s and `LegacyLoadGuard.v`'s proofs never hit this because they convert a nat hypothesis to `wlt` for the *goal*, the reverse direction, where `apply lt_wlt` already produces the right shape before any rewrite is needed.)

All three files generated via a Python script (`/tmp/.../scratchpad/gen_guards.py` this session, not checked in) from a per-opcode parameter table, since the nine lemmas are structurally identical modulo names -- writing each by hand would have meant retyping the same nine-line tactic script with high risk of a silent name transposition. Every lemma was still verified by the guarded `coqc`, not assumed correct from the generator; the two traps above were both caught this way; the generator does not close the underlying mathematics, only assembles it. Checked: guarded `coqc` on each file individually, exit 0 (LegacyLocalityGuard.v: ~1s including Kami.Kami reload; LegacyPartitionGuard.v: ~1s; LegacyNfiGuard.v: ~1s). `Print Assumptions` on all nine lemmas: only `functional_extensionality_dep` and `Eq_rect_eq.eq_rect_eq`, the same two axioms every other C1/C2 result carries -- no new axioms, zero `Admitted`/`admit` across all three files. `make -C coq -n all` after registering in `_CoqProject`: schedules nothing further, confirming the `.vo`s are current and nothing downstream broke.

**What this does not close.** All ten guard-class opcodes' bound premises are now available as decoded-guard falsity for the *legacy* encoding only. Still open, per `OutsideDomain.v`'s closing note:

1. The rich-format guard needs the same lane identity for the other five encodings (`BRANCH_EXT`, `TENSOR_EXT`, `MORPH_INLINE`, `DESC`, `CERT_INLINE`) -- `LegacyWordDecode.v` only covers legacy words. Each encoding packs its fields differently and needs its own `<encoding>_nat`/`<encoding>_low_flat` pair; the `wordToNat_combine`/`mod_add_pow2`/`div_small_add` toolkit is encoding-agnostic and reuses directly, only the byte layout changes.
2. Assembling all ten opcodes' lemmas (now: LOAD in `LegacyLoadGuard.v`, the other nine across the three new files) into `OutsideDomain.v`'s actual master statement (`not_guard_of_opcode` plus the ten `op_off_*`-style premise lemmas, generalized the way that file's own closing note describes) -- not yet done; the ten lemmas exist as standalone facts, not yet wired into one theorem.
3. Everything downstream of that: C1/C2 gate closure still needs Gate E in full (fresh reproduction, dependency-enabled `coqchk`, final local contract review, immutable candidate) after C1/C2 itself closes.

**Next agent: start here.** Item 1 above is the natural next increment and is now the only thing standing between the ten legacy-word guard lemmas and a complete legacy-word outside-domain relation. Start with whichever of the five rich-format encodings is simplest to decode (check `BoundaryDecoded.v`/`DispatchLets.v` for how each `*_EXT`/`DESC`/`CERT_INLINE` word lays out its fields), build its `<encoding>_word_nat` lane identity mirroring `legacy_word_nat`, then its own `dd_opcode`/operand-field `_correct` lemmas mirroring `dd_op_correct`/`dd_a_correct`/`dd_b_correct`/`dd_c_correct`, checking each with the guarded `coqc` before moving to the next encoding. Only after all six encodings (legacy plus the five rich formats) have their decode identities does item 2 (the master theorem assembly) become well-typed to attempt.

## Earlier handoff: 2026-09-16 evening (legacy-word decode identity landed; C1/C2 outside-domain obstruction cracked for one opcode)

Devon asked a fresh agent to pick up the outside-domain obstruction the prior handoff (below) recorded as blocked. That obstruction is now partially cleared: the missing "word-lane identity over split/combine" is built, checked in, and demonstrated end to end on one opcode. C1/C2 as a whole is **not** closed by this; nine guard-class opcodes and the six per-encoding rich-format guards remain, plus the master theorem the outside-domain relation feeds.

### What was blocking: verified, then fixed

The prior handoff's own diagnosis was right: reducing a decoded field (`dd_isa_version`, `dd_opcode`, ...) on a concrete instruction word with symbolic operands needs a `split`/`combine` identity that did not exist in the tree, and every earlier attempt (including a same-day predecessor session's `LaneArith.v`, left unregistered) stalled on it. Two real causes, confirmed by reproducing the failure directly:

1. **The technique was wrong.** Manipulating `split`/`combine` terms symbolically forces dependent-size `eq_rect` casts at every re-association, which is exactly where prior attempts got stuck (stack overflows, unification timeouts). The fix: never touch `split`/`combine` directly. Go through `wordToNat` instead (`wordToNat_combine`, `wordToNat_split1`, `wordToNat_split2`, which are plain `mod`/`div` identities on naturals), solve the goal in `nat`, then close with `wordToNat_eqw` (two words of the same size are equal iff their `wordToNat` values are). This sidesteps the cast problem entirely — there is never a `split`/`combine` term to re-associate.
2. **A second, separate trap, found by reproducing the crash.** `ring`, `nia`, and `exact`'s conversion check must never be asked to relate two forms of a term that still contains an unevaluated `pow2 n` for large `n` (89, 96, 121 here) — the kernel represents `nat` in unary, so normalizing `pow2 89` this way means building a ~10^26-successor term, which is the stack overflow the prior handoff attributed only to decimal literals like `4294967296`. It is broader than that: any large, unevaluated `pow2` exponent triggers it. The fix is mechanical and now written down as a comment in the new file: stay on plain `rewrite` with named facts near such terms, and only let `ring`/`nia` touch `pow2 8`/`16`/`24`/`32` (safe — bounded by concrete products of 256).

### What is now checked and in the tree

**`kami_hw/LegacyWordDecode.v`** (new, registered, ~330 lines, zero `Admitted`/`admit`). For `legacy_word op a b c` (the canonical ISA-v2 legacy encoding, symbolic operand bytes), every field the guard obligations need is proved to decode back exactly:

- `dd_opcode`, `dd_op_a`, `dd_op_b`, `dd_cost_v` decode to `op`, `a`, `b`, `c`.
- `dd_isa_version = 2`, `dd_format_id = FMT_LEGACY`, `dd_flags = 0`.

Guarded `coqc`: exit 0. `Print Assumptions` on all seven: only `functional_extensionality_dep` and `Eq_rect_eq.eq_rect_eq`, the same two axioms every other C1/C2 result already carries — no new axioms, no `cheat`. Full guarded `make -C coq all` after registering: exit 0, only this file rebuilt, `make -n all` schedules nothing afterward.

**`kami_hw/LegacyLoadGuard.v`** (new, registered). One end-to-end demonstration that the identity above is actually usable for the outside-domain obligation, not just an isolated arithmetic fact: `dd_load_locality_bad_false` shows that for an arbitrary `legacy_word OP_LOAD a b c`, the decoded guard `dd_load_locality_bad` is false whenever the decoded memory address is within the active partition's region — the same premise `StepRefineCommon.region_ok_of_lt` already names for `StepRefine.step_load_refines`'s bit-variable route, but reached here through the actual decoded opcode and operand fields on a concrete word, which is the form the outside-domain relation needs. Guarded build: exit 0, 3s. Assumptions: the same two axioms only.

### What this does not close

This is the premise-half pattern for **one** of the ten guard-class opcodes (LOAD), on **one** of the six instruction-word encodings (legacy). Still open, all using the same now-proven technique:

1. The other nine guard-class opcodes' own bound premises restated as their decoded guard's falsity: STORE, HEAP_LOAD, HEAP_STORE, CALL, RET, PNEW, PSPLIT, PMERGE, PDISCOVER. HEAP_LOAD/HEAP_STORE need one more step (the `dd_opcode == OP_HEAP_LOAD` branch of the mux, unhandled by `dd_load_locality_bad_false`, which only closed the non-heap branch). PNEW/PSPLIT/PMERGE need the same treatment against `dd_ptable_overflow_violation`'s arithmetic rather than `check_bounds`. PDISCOVER needs it against `dd_nfi_violation`.
2. The rich-format guard, which needs the same lane identity for the other five encodings (`BRANCH_EXT`, `TENSOR_EXT`, `MORPH_INLINE`, `DESC`, `CERT_INLINE`) — `LegacyWordDecode.v` only covers legacy words. Each encoding packs its fields differently and will need its own version of `legacy_word_nat`/`legacy_low32_flat`, though the same `wordToNat`-only technique applies directly.
3. Once all ten opcodes and six encodings are covered, assembling them into `OutsideDomain.v`'s actual master statement (`not_guard_of_opcode` plus the ten `op_off_*`-style premise lemmas, generalized the way the file's own closing note describes).
4. Everything downstream of that: C1/C2 gate closure still needs Gate E in full (fresh reproduction, dependency-enabled `coqchk`, final local contract review, immutable candidate) after C1/C2 itself closes.

### Next agent: start here

1. Repeat `LegacyLoadGuard.v`'s pattern for STORE, CALL, RET against `dd_store_locality_bad`/`dd_call_locality_bad`/`dd_ret_locality_bad` — same `check_bounds`/`region_ok_of_lt` shape, different `dd_*_in_bounds` predicate and different operand byte (`dd_op_a`/`dd_dst_val`/`dd_sp_addr`/`dd_sp_dec_addr` instead of `dd_op_b`/`dd_src_val`). `HEAP_LOAD`/`HEAP_STORE` need the OP_HEAP_LOAD/OP_HEAP_STORE branch of the same mux `dd_load_locality_bad_false` left unhandled — same proof, opposite `destruct` branch, using `dd_heap_addr`/`hw_csr_heap_base` instead of `dd_mem_addr`.
2. PNEW/PSPLIT/PMERGE against `dd_ptable_overflow_violation` (`dd_pnew_overflow`/etc. in `DispatchLets.v`) and PDISCOVER against `dd_nfi_violation` (`dd_is_declared_bound_op`) are arithmetic comparisons, not `check_bounds`, so they will not need `region_ok_of_lt`'s lemma but do need the same opcode/operand decode identity.
3. The rich-format guard's five non-legacy encodings each need their own `<encoding>_nat`/`<encoding>_low_flat` pair mirroring `LegacyWordDecode.v`'s `legacy_word_nat`/`legacy_low32_flat`; the `wordToNat_combine`/`mod_add_pow2`/`div_small_add` toolkit in that file is encoding-agnostic and can be reused directly, only the byte layout changes.
4. Watch for the two traps recorded above in any new file: use `@` on every `bbv`/Kami word lemma applied with explicit arguments (`Set Implicit Arguments` is in effect throughout `Kami.Lib.Word`, so bare `forall sz w` binders are silently implicit — omitting `@` makes the first explicit argument bind to the wrong parameter with a confusing "expected word ?sz" error), and never let `ring`/`nia`/`exact` see an unevaluated large-exponent `pow2` term.

## Earlier handoff: 2026-09-16 (C3 closed on the current CPU source; C1/C2 preservation, reachable invariants, trace composition and scheduler progress complete)

### C3: regenerated and passed on the current source

The extraction pipeline (`scripts/kami_extract.sh`, BSC 2024.07) was rerun
from the current `ThieleCPUCore.v` after the VM-alignment and label/tensor
changes. It produced `build/kami_hw/thiele_hw.bsv`, `thiele_hw_clean.bsv`,
`mkModule1.v` and `mkModule1_synth.v`, and the tracked RTL
`thielecpu/hardware/rtl/thiele_cpu_kami.v` is byte-identical to
`mkModule1_synth.v` (`cmp` clean). The provenance manifest and the text
transform audit were regenerated against the new hashes, and the C3 audit
(`artifacts/review_revision/c3_audit/validate.py`) passes all three checks:
pipeline 0, transforms 0, tests 0. Evidence:
`artifacts/review_revision/c3_audit/validation.json`,
`regeneration-2026-09-16.log`, `artifacts/rtl_pipeline_manifest.json`,
`artifacts/rtl_text_transform_audit.json`. No synthesis, timing, LUT or
bitstream claim is made; the classification scope in the audit report is
unchanged. With this run the C3 gate closes.

### C1/C2: what closed this session

Four obligations of the C1/C2 contract are now checked. I record them in
the order the contract states them, so the remaining gap is unambiguous.

**Reachable-invariant preservation, all 55 constructors.**
`TableInvariantsPreserved.v` covers all 55 of `RetireMaster.admitted`'s
constructors and proves
`hwb_table_invariants_preserved : forall b i d, hwb_table_invariants b ->
admitted b i -> Retire b i d -> hwb_table_invariants d`. The two cases added
here are `preserved_compose_ext` (COMPOSE at its extended encoding: the step
firing allocates the morph slot `s` and the coupling descriptor `cd`
provisionally, then `compose_fsm_final` commits `cd`'s base/count/valid
fields and the pair table through `CouplingComposeRetire.compose_fsm_run`,
pinned by `RetireRunsOps.compose_ext_runs`; the helpers are
`compose_label_represented` and `compose_mc_zero`) and
`preserved_compose_ext_fault` (the fault branch, closed by the new
`mux3_frame`). Checked with the guarded `coqc`: exit 0, 9 s. Full file: zero
`Admitted`, zero `admit`, 64 `Qed`. `Print Assumptions` on the master
theorem shows only `functional_extensionality_dep` and
`Eq_rect_eq.eq_rect_eq`.

**Reachable-state invariants from reset.** `TableInvariantsReachable.v` defines
`AdmittedRun b is d`, a chain of admitted instructions each retiring from the
boundary the previous one reached, and proves `hwb_table_invariants_run` (the
invariants carry along a chain by induction, using
`hwb_table_invariants_preserved` as the step) and
`hwb_table_invariants_reachable` (there is a reset boundary `b0` with
`hwb_regs b0 = dispatch_reset_state` such that every admitted chain from `b0`
ends in a state carrying the invariants).

**Trace composition.** The same file proves `admitted_run_multistep` (a chain is
one actual `Multistep` of `thieleCore`, by chaining each step's
`retire_multistep` through `normalization_multistep_trans`),
`admitted_run_snapshot` (the chain's final boundary observes the kernel's own
run of the same instruction list, via the new `kami_run_list` fixpoint and each
step's `Retire` snapshot equation), and `fsm_retirement_refinement` (there is a
reset boundary such that every admitted chain from it ends in a state carrying
the table invariants, observing the kernel's run of the same instructions, and
reached by one actual Kami execution). Checked: guarded `coqc`, exit 0, 1 s;
`Print Assumptions` shows only the two inherited axioms.

**Scheduler progress to retirement.** `RetireProgress.v` states progress against
the concrete scheduler rather than an abstract relation. `retire_runs` shows
that an admitted instruction lets the rule runner reach its retirement boundary
in a bounded number of firings. `admitted_progress` and
`admitted_instruction_progress` compose that with `admitted_retires`: from a
boundary where an instruction is admitted, the runner reaches a boundary
observing the kernel's step for that instruction, and the whole firing sequence
is one actual Kami execution. `admitted_run_progress` extends it along a whole
admitted chain, and `admitted_run_progress_invariants` adds that the end state
still carries the table invariants. Checked: guarded `coqc`, exit 0, 1 s; full
guarded `make -C coq -k all`, exit 0; `Print Assumptions` on the progress
theorems shows only the two inherited axioms.

### C1/C2: the outside-domain outcome relation

The outside-domain relation connects `StepFaults`'s guards to C1's admission
conditions. Half of it is checked, half is not.

**Checked: the opcode-membership half.** `OutsideDomain.v`.
`StepFaults.dd_guard_opcode` says the locality, partition-overflow and NFI
guards fire only on an opcode in `guard_opcodes` (six memory opcodes, three
partition opcodes, PDISCOVER). `not_guard_of_opcode` turns that into an
evaluator: an opcode outside `guard_opcodes` takes the disjunction to `false`,
for an arbitrary boundary and fetched word, with no decode reasoning. The
`op_off_*` facts name each such opcode and discharge the membership test by
computation, `guard_opcodes_exact` fixes the class, and
`locality_opcodes_sub_guard` and `partition_opcodes_sub_guard` place the
sub-classes. Checked: guarded `coqc`, exit 0, 2 s.

**Not checked: the premise half.** Two pieces remain.

1. The ten guard-class opcodes (LOAD, HEAP_LOAD, STORE, HEAP_STORE, CALL, RET,
   PNEW, PSPLIT, PMERGE, PDISCOVER) each carry the bound premise that makes
   their own guard false. Stating that premise as the decoded guard's falsity
   is not yet done.
2. The rich-format guard inspects operand and format fields, so it needs one
   lemma per encoding (legacy, BRANCH_EXT, TENSOR_EXT, MORPH_INLINE, DESC,
   CERT_INLINE).

Both pieces share one blocker, and I record it plainly so the next handoff does
not rediscover it. The decoded guards (`dd_locality_violation`,
`dd_rich_fault`, and the rest) are `evalExpr` reflections of the rule's LETs.
The admission premises are stated over the hardware accessors
(`hw_regs`, `hw_ptTable`) through `hw_region_ok` and `region_ok_of_lt`. To
connect them you must reduce a decoded field on a concrete instruction word,
for example show `dd_isa_version bd (legacy_word op a b c) = 2` with symbolic
`op a b c`. That reduction needs a word-lane identity over `split`/`combine`
that does not yet exist in the tree.

I built most of that identity in scratch probes and verified each piece, then
removed the probes rather than integrate a partial result. What is proved and
usable: the top 96-bit lane value (`wordToNat (NToWord 96 (N.shiftl 2 88)) =
pow2 89`), the four-lane combine expansion (`repeat rewrite
wordToNat_combine`), and the 128-bit lane arithmetic (a `mod`/`div` identity
over the four symbolic 8-bit operands plus the constant high lane), which
proves the opcode, version, format and flags lanes. Three arithmetic details
cost real time and should be carried forward: `ring` and `nia` fail on the
literal `4294967296` because it parses as `Nat.of_num_uint`, so the constants
must be written as products of 256; `Nat.mod_add` and `Nat.div_add` need the
multiplier on the right, so commute first; and `rewrite wordToNat_combine`
only fires once the word sizes are literal, which needs `unfold WordSz,
InstrUpperSz, InstrSz, FormatIdSz` because the extraction records the split
size as `WordSz + InstrUpperSz` rather than `128`.

What is left to land: after the sizes are unfolded and every `split`/`combine`
rewrite succeeds, the goal is the lane arithmetic in `Nat.pow` form while the
arithmetic lemma is stated with numeric products, and `exact`/`change` between
the two forms overflows the stack. The fix is to state the arithmetic lemma in
exactly the goal's `pow2` shape and convert only the divisors inside it. Once
that one lemma is stated to match, the lane lemmas follow mechanically, and
the guard-class and rich-format halves reduce to opcode-class and
format-class case analysis over them. Concrete instances (all-concrete
operands) reduce fine by computation, so the mathematics is not in doubt. The
morph-runtime guard is admitted by design for the morph constructors, so it
needs no falsity lemma.

## Earlier handoff: 2026-09-15 night (reachable-invariant preservation: 47 of 55 constructors done)

**This session's increment: `TableInvariantsPreserved.v` (new file,
registered), the preservation half of C1/C2's reachable-state-invariants
obligation, for 47 of `RetireMaster.admitted`'s 55 constructors.**
`hwb_table_invariants_frame`: a reusable combinator taking the twelve field
equalities the nine invariant clauses actually read (four morph-table
fields, six coupling desc/pair-table fields, two label-table fields) and
transferring `hwb_table_invariants` from `b` to `d` verbatim (plus a small
`hw_coupling_ref_ok_frame` helper for the one clause that calls a function
of two of those fields). 45 constructors retire in a single `step_next`
firing (`Busy_runs _ _ 0` via `busy_done`, forced by uniqueness against
`hw_idle (step_next b)` from `step_idle` plus each opcode's own three
phase-zero lemmas): their own `StepFields`/`StepFieldsMorph`/
`LassertStepFields` frame lemmas for the four morph fields and two label
fields, plus `StepEval`'s six opcode-independent lemmas for the rest, close
the twelve facts directly. The other two (CHSH_LASSERT, LASSERT_SAT) run a
multi-cycle FSM after `step_next` (`chsh_iter 23`, respectively
`lscan_iter n (lhdr_next (step_next b))`); `ChshRun`'s and
`LassertWord`/`LassertRetire`'s own `iter_keeps_X`/`lscan_iter_keeps_X`/
`lhdr_keeps_X` frame catalogues chain onto the same per-opcode `step_next`
equations to reach the same twelve facts, with the run itself pinned down
via `chsh_lassert_runs`/`lassert_sat_runs` (both already in
`RetireRunsOps.v`) against the same uniqueness argument. All 47 lemmas
(named `preserved_<opcode>`) are `Qed`, zero admits. Built with a
mechanical extraction pass, not hand-transcription: a script read each
constructor's forall-header, `step_fetched`/`hwb_bianchi` premises and
concluding instruction directly out of `RetireMaster.v`'s own `admitted`
inductive (verbatim, to avoid retyping up to 56 bit-variables per
constructor by hand) and cross-checked that all 45*9 opcode-specific lemma
names it would cite actually exist before emitting anything. Checked:
guarded `coqc` on the file alone, exit 0, 2s; `Print Assumptions` on the
frame combinator and five representative `preserved_*` lemmas (one plain
arithmetic op, one morph-non-table op, one bit-omitting LASSERT encoding,
and both FSM cases) shows only the two already-documented inherited axioms;
full guarded `make -C coq -k all` rebuild after registering, exit 0.

**Still not done: the other 8 constructors** (`adm_morph_id`,
`adm_morph_id_ext`, `adm_morph_delete`, `adm_morph_delete_ext`,
`adm_morph_ext`, `adm_morph_ext_fault`, `adm_compose_ext`,
`adm_compose_ext_fault`) actually write the morph or coupling tables, so
`hwb_table_invariants_frame` does not apply to them; they need the
allocation/deletion algebra `TableInvariants.v`'s closing note already
scoped (an explicit if-mux at the write index from `StepFieldsMorph.v` for
ID/DELETE legacy+ext; `CouplingFsmRun.morph_fsm_run`'s and
`CouplingComposeRetire`'s field equations at the *old* allocation pointer
for the two FSM-completion cases; `CouplingFaults.v`'s frame lemmas for the
two fault branches). Only once those 8 are built can
`hwb_table_invariants_preserved : forall b i d, hwb_table_invariants b ->
admitted b i -> Retire b i d -> hwb_table_invariants d` actually be stated
(Coq requires every constructor closed to state a theorem by `destruct` on
`admitted`; a partial case split is not expressible without `Admitted`,
which this branch's discipline forbids) -- until then the 47 `preserved_*`
lemmas exist as standalone, individually complete facts, not yet assembled
into that master statement. After it can be stated, the reachable-state
theorem itself is a straightforward induction over `admitted`+`Retire`
chains carrying `hwb_table_invariants_reset` (already done) as the base
case and `hwb_table_invariants_preserved` as the step -- and that same
induction skeleton is also where the `fsm_retirement_refinement` trace
composition obligation belongs, since both need "chain `Retire` steps,
carrying an invariant."

## Earlier handoff: 2026-09-15 late session (single-instruction retirement closed for all 47 opcodes; reachable-invariant base case added)

The section below ("Earlier handoff: 2026-09-15 morning") is now stale where
it says fault outcomes and the master theorem are unstarted -- that work
happened later the same day and is fully checked; read the Live-progress
table's rows from "Step rule as Gallina" (`DispatchLets.v`) through "Master
single-instruction theorem" (`RetireMaster.v`) for what actually shipped
before treating that section's "Next agent: start here" as current. This
handoff corrects that and adds the next real increment.

**What is now true, checked, on disk.** `RetireMaster.Retire b i d` (live
boundary `b`, an instruction `i`, the busy FSM firings from `step_next b`,
the idle boundary `d`, `hwb_snapshot d = kami_step (hwb_snapshot b) i`) has
one `admitted`-inductive constructor per opcode -- all 47 -- each carrying
its retirement theorem's premises verbatim, and `admitted_retires : admitted
b i -> exists d, Retire b i d`. This is the C1/C2 single-instruction master
theorem the contract calls for, not a partial result. `StepFaults.v`
separately covers the five trap guards (Bianchi, locality, partition
overflow, NFI, rich) and `morph_runtime_fault` at the snapshot level, for an
arbitrary boundary and fetched word with no opcode fixed. Guarded full
rebuild is clean (`make -C coq -n all` schedules nothing); dependency-enabled
`coqchk`/assumption census have been run per-file along the way (see the
Live-progress rows) and show only the already-documented inherited axioms
(`functional_extensionality_dep`, `Eq_rect_eq.eq_rect_eq`, plus the
library-wide vendor `Kami.Lib.CommonTactics.cheat`, unused by any of these
results).

**Still open for C1/C2, precisely** (`RetireMaster.v`'s own closing note):
reachable-state invariants from reset for the table premises several
retirement theorems already carry as hypotheses; the outside-domain outcome
relation connecting `StepFaults`'s guards to C1's admission conditions; and
trace composition (`fsm_retirement_refinement`) chaining `Retire` across a
run under the concrete scheduler.

**This session's increment: `TableInvariants.v` (new file, registered),
the base case of the first item above.** `hwb_table_invariants` bundles the
nine table predicates already named across `StepRefineMorph.v` (
`hwb_morph_valid_below_next`, `hwb_morph_coupling_refs_ok`,
`hwb_coupling_desc_zero_invalid`), `StepFaults.v`
(`hwb_coupling_desc_valid_below_next`) and `CouplingComposeKami.v`
(`hwb_desc_pairs_below_next`, `hwb_pairs_valid_below_next`,
`hwb_desc_zero_empty`, `hwb_identity_desc_zero`, `hwb_labels_represented`) --
these are exactly the premises `retire_compose_ext` and its neighbors already
require to fire, i.e. exactly what a reachable-state induction needs to
supply at every step. `hwb_table_invariants_reset`: there is a boundary
`b` with `hwb_regs b = dispatch_reset_state` (via `cpu_reset_run_has_boundary
0`) at which all nine hold, because `morph_valid_table`,
`coupling_desc_valid_table` and `coupling_pair_valid_table` reset to
all-false and `coupling_pair_next_id` resets to 0 (`DispatchReset.v`), so
every implication is vacuous and the one non-vacuous clause
(`hwb_desc_zero_empty`) is a direct reset-value check. Checked: guarded
build (4 s), `Print Assumptions` reports only `functional_extensionality_dep`
and `Eq_rect_eq.eq_rect_eq` (the same already-documented set), full guarded
`make -C coq -k all` rebuild after registering it is exit 0.

**Next agent: start here for the preservation half (induction step, not yet
built).** `RetireMaster.admitted` has 55 constructors, one per retirement
theorem, covering all 47 opcodes (a few opcodes have more than one
constructor for a legacy/extended encoding or a success/fault branch). 47
of the 55 leave every field `hwb_table_invariants`
mentions unchanged, provably without a case split on opcode for six of the
nine fields and via a per-opcode named lemma for the rest:
- `StepEval.step_keeps_coupling_desc_base_table`, `_count_table`,
  `_valid_table`, `_next_id`, `step_keeps_coupling_pair_valid_table` and
  `_next_id` already hold **unconditionally** for `step_next b` regardless
  of opcode (only the multi-cycle `mc_commit`/loop rules ever write these,
  and none of the 35 easy constructors reach them).
- The morph-table fields (`hw_morph_valid_table`, `_next_id`,
  `_coupling_desc_table`, `_identity_table`) are unchanged for each of the
  38 single-cycle non-morph opcodes by that exact opcode's own named lemma
  in `StepFields.v` (e.g. `step_add_morph_valid_table`, one such lemma per
  opcode per field -- 38 x 4, already generated and Qed'd, just needs
  citing), and for LASSERT/CHSH_LASSERT by those FSMs' own frame catalogues
  (`ChshFsm.v`'s ~111 frame equations, `LassertWord.v`'s equivalents).

The remaining 8 constructors (`adm_morph_id`, `adm_morph_id_ext`,
`adm_morph_delete`, `adm_morph_delete_ext`, `adm_morph_ext`,
`adm_morph_ext_fault`, `adm_compose_ext`, `adm_compose_ext_fault`) touch
these tables and need real (but already mostly available) algebra:
- ID/DELETE (legacy and ext) write exactly the morph-table fields inside
  `step_next` at index `hw_morph_next_id b` (alloc) or the deleted index
  (clear); `StepFieldsMorph.v` already states the resulting value as an
  explicit `if`-mux (e.g. `hw_morph_valid_table (step_next b) = if
  hw_morph_room b then if hw_module_present b ... then (fun w => if weq w
  (split1 4 1 (hw_morph_next_id b)) then true else hw_morph_valid_table b w)
  else ... else ...`) -- combined with the room premise (`< 16`, already
  required by these opcodes' own `admitted` constructors) this is a direct
  "the new/cleared index satisfies the bound; every other index inherits
  the IH" argument, no new Kami evaluation needed.
- `adm_morph_ext`/`adm_compose_ext` additionally run to
  `morph_fsm_final count (step_next b)` / `compose_fsm_final (step_next b)`.
  `CouplingFsmRun.morph_fsm_run` (and `CouplingComposeRetire`'s analogous
  statement) already gives every field equation needed: pair table entries
  below the *old* `coupling_pair_next_id` are untouched
  (`forall k, k < P -> table_pair ... = table_pair (old) ...`), the new
  segment is exactly the loaded/deduplicated pairs, `coupling_pair_next_id`
  becomes the new write pointer, and `coupling_desc_base/count/valid_table`
  and `coupling_desc_next_id` are updated at exactly the *old*
  `coupling_desc_next_id` via `put_vector`, then incremented by 1. Since
  `coupling_desc_next_id` only ever increases by exactly 1 at this one write
  site and starts at 1 (`DispatchReset.v`), it is never 0, which is exactly
  what `hwb_coupling_desc_zero_invalid` needs to survive the new allocation
  -- consider adding a tenth invariant, `1 <= wordToNat
  (hw_coupling_desc_next_id b)`, to make that step self-contained rather
  than re-deriving it from the reset value and the single write site each
  time.
- `adm_morph_ext_fault`/`adm_compose_ext_fault` are frame: `CouplingFaults.v`
  already states "tables unchanged" for both.

Suggested next file: `TableInvariantsPreserved.v`, one lemma
`hwb_table_invariants_preserved : forall b i d, hwb_table_invariants b ->
admitted b i -> Retire b i d -> hwb_table_invariants d`, built by `destruct`
on `admitted` (43 cases), the 35 easy ones closed by a short repeated
frame-rewrite pattern and the 8 hard ones by the algebra above. Once that
exists, `hwb_table_invariants_reset` (base case, done) plus an induction on
run length over `admitted`+`Retire` chains gives the actual reachable-state
theorem C1/C2 asks for -- the natural point to also start the trace
composition (`fsm_retirement_refinement`) obligation, since both need the
same "chain `Retire` steps, carrying invariants" induction.

## Earlier handoff: 2026-09-15 morning (resuming after container restart)

The devcontainer restarted between the last session's edits (04:20-04:45 UTC)
and this session (started 06:54 UTC); all host processes show start times of
06:48-06:49, and no stale `coqc`/`coqtop`/orphan Claude process survived the
restart, so nothing needed to be killed. No source was lost: the last edits
are on disk with their usual `~/.cache/thiele-guard/*.pre_*.v` backups.

**What the interrupted session had done** (rows up to "MORPH retirement
(extended encoding)" below, then further unlogged work): revised the COMPOSE
label representation from the earlier ";"-count to an atom-count-plus-mask
encoding, because a morphism with no valid descriptor (MORPH_ID, identity,
legacy self-MORPH) needs an "empty" atom the count alone could not carry.
`ThieleCPUCore.v` and `ImplementationContract.v` were edited accordingly
(backups `~/.cache/thiele-guard/*.pre_label_atoms.v`); `atom_label n mask`
and `atom_label_compose` (concatenation identity) were proved and checked by
three standalone probes (`AtomLabel.v`, `CRDbg.v`, `ComposeRun.v`, all
compiled clean at 04:41-04:45). Full decision and admission-premise text is
in [C2_DIVERGENCE_LEDGER.md](C2_DIVERGENCE_LEDGER.md) under "CPU changes for
COMPOSE labels and MORPH_TENSOR". A guarded `make -k all` was then started to
propagate the change through the tree but was cut off mid-`RuleNext.vo` by
the container restart, not by a proof defect or the guard's own limits.

**This session:** confirmed the restart explanation above, ran `make -C coq
-n all` and found 33 files stale downstream of the CPU/contract change (the
same set the interrupted run was working through: `RuleNext.v` through
`CouplingMorphRetire.v`), and relaunched the guarded rebuild. It found and
fixed two defects, both pre-existing gaps from the interrupted session, not
regressions from anything on `main`:

1. **`CouplingFsmRun.v` proof bug.** `morph_fsm_keeps_coupling_desc_label_table`
   (line 400) rewrote with `mccommit_keeps_coupling_desc_label_len_table`,
   `nouter_iter_keeps_coupling_desc_label_len_table` and
   `mcnstart_keeps_coupling_desc_label_len_table` mixed into its chain: three
   frame lemmas about the *length* table copy-pasted into the proof of the
   *label* table's frame lemma, where they don't apply. Removed the three
   extra rewrites so the proof matches every other `morph_fsm_keeps_*` lemma
   in the file (four rewrites, one per FSM stage, then the header lemma).
   Compiles in 4s standalone.
2. **`BoundaryRun.v` never registered.** This file (the "HWB-level runner
   mirroring `run_cpu_rules`" that the "Not yet done" list below still
   listed as open) was already written in the interrupted session -- correct
   in substance -- but was never added to `coq/_CoqProject`, so `make` never
   compiled it and no prior session had actually checked it. Once added, it
   failed for three independent reasons, all fixed: (a) `[]`/`::` pattern
   matches on lists don't parse under `Kami.Kami`/`Kami.Semantics` in this
   codebase (a Kami notation shadows the empty-list bracket even after
   `Open Scope list_scope`) -- the established idiom here is `nil`/`cons r
   rest`, used instead; (b) a redundant `rewrite <- Hnext` in
   `run_boundary_rules_correct` failed because Coq's `inversion ... as
   [[Hname Hnext]]` had already substituted that equation into the goal on
   its own (verified by printing the goal before and after `inversion`) --
   removed the now-redundant rewrite; (c) `<=`/`<` on `fuel : nat` in the two
   firing-bound theorems parsed as the word-comparison notation instead of
   nat's, inferring `fuel : word ?sz` -- added the `%nat` scope annotation,
   the same idiom already used in `CoreExecution.v`. `BoundaryRun.v` now
   compiles clean (13s) with `select_boundary_rule_correct`,
   `select_boundary_unique`, `run_boundary_rules_correct`,
   `run_boundary_rules_actual`, `run_boundary_rules_firing_bound` and
   `run_boundary_rules_short_trace_disabled`, mirroring `run_cpu_rules`
   exactly (same firing sequence, same trace, same 12-rule priority order).

After both fixes, `~/.cache/thiele-guard/mk.sh ... -C coq -k all` exits 0 and
`make -C coq -n all` schedules nothing: the whole tree is consistent again.
`c2_step/Contracts.v` gained an `atom_label_compose` check, and
`c2_step/validate.py` (dry-run, contracts, dependency-enabled `coqchk` over
all 33 C2 step/FSM/coupling modules plus `BoundaryRun`) passed in full:
dry-run 2.3s, contracts 294.3s/886MB, `coqchk` 1593.9s/477MB, all exit 0.
`coqchk`'s context summary lists only the already-documented
`functional_extensionality_dep`, `Eq_rect_eq.eq_rect_eq` and the vendor
`Kami.Lib.CommonTactics.cheat` (library-wide, not used by any of these
results); no type-in-type, unsafe fixpoints or assumed positivity.
`atom_label_compose` itself is closed under the global context with no
axioms at all. `c2_step/validation.json` records `"status": "passed"`.

### Next agent: start here

1. **Fault outcomes at snapshot level -- scoping finding, not yet proved.**
   This item does *not* need 47 opcode-specific proofs. In
   `ThieleCPUCore.v`'s step rule, `new_pc` (line 870), `new_regs` (899),
   `new_mem` (935), `new_certified` (1028) and (with a different, four-way
   list omitting `rich_fault`) `new_halted`/`new_err` (960/963) all gate on
   an outer `IF (bianchi_violation || locality_violation ||
   ptable_overflow_violation || nfi_violation || rich_fault) then <frozen
   value> else <opcode-specific dispatch>` -- the freeze/trap branch never
   inspects the opcode. `new_error_code` (972) is a fixed priority chain
   over the same five flags (Bianchi first). So the real obligation is
   5-6 generic theorems parametric in an arbitrary decoded instruction and
   an arbitrary truth value of each flag, not one theorem per opcode.
   `hwb_bianchi` (`BoundaryDecoded.v:10`) is already a free-standing
   boundary-only predicate (`wlt_dec (hw_mu b) (hwb_tensor_total b)`,
   independent of the fetched word) and is the easiest of the five to
   start with; `locality_violation` (405), `ptable_overflow_violation`
   (416), `nfi_violation` (763) and `rich_fault` (300) are computed inside
   `dispatch_decoded`'s LET chain and *do* depend on the fetched
   instruction's fields (which opcode, which operands), so stating their
   generic theorem needs the raw decoded boolean as a hypothesis (the way
   `StepFields.v` already carries named guard predicates), not a
   standalone Gallina function the way `hwb_bianchi` is. `StepEval.v`'s
   ~67 `step_keeps_*` frame lemmas (registers the step rule never touches
   at all) already cover a large fraction of the 138-field snapshot
   unconditionally and can be reused directly. None of this is proved yet
   -- no Gallina lemma anywhere states what happens when any of these five
   flags is true; `step_<op>_refines` in `StepRefine.v` only covers the
   Bianchi-free success path. Expect this to need its own generator
   script, similar in size to `generate_step_refine.py`.
2. After that: the decode/admission master theorem across all 47 opcodes,
   reachable-state invariants from reset, and trace composition
   (`fsm_retirement_refinement`). The HWB runner and rule enabledness items
   are now both done and checked (`BoundaryRun.v`, `RuleEnabled.v`), and the
   label-atom change is now fully audited (assumption census/`coqchk`
   passed, see above).
3. RTL regeneration, runtime-test updates and the C3 re-audit stay last,
   once the hardware stops changing.

## Earlier handoff: 2026-09-14 evening (C2 VM alignment and single-cycle refinement)

Devon asked to stop and update this ledger. Nothing is running. `make -C coq -n all` schedules no compilation. No commits, tags or publication.

### What this session did

1. **Divergence survey and decision.** The CPU disagreed with `vm_apply`/`kami_step` on VM-visible state where no admission premise applies. Devon chose to change the CPU to match the VM. Full ledger: [C2_DIVERGENCE_LEDGER.md](C2_DIVERGENCE_LEDGER.md).
2. **CPU edits** in `coq/kami_hw/ThieleCPUCore.v` (backup `~/.cache/thiele-guard/ThieleCPUCore.pre_vm_alignment.v`): logic-gate lock, per-step `mstatus` rewrite and LASSERT `logic_acc` toggle removed; HALT advances pc; PDISCOVER writes no register; CHSH_TRIAL x=1 surcharge and zero-tensor gate removed; morph runtime faults advance pc; kind-0 LASSERT charges header x 8 + cost + 1.
3. **`kami_step` / observation alignment** in `Abstraction.v` (backup `~/.cache/thiele-guard/Abstraction.pre_vm_alignment.v`) and `ImplementationContract.v`: EMIT adds its payload bits to `info_gain`; REVEAL leaves `info_gain` unchanged; LASSERT/CHSH_LASSERT failures record ERR_LOGIC; morph failures record the CPU fault code (`kami_advance_err_code`, codes behind Qed-closed witnesses); the boundary observation carries the empty LASSERT shadow. `GraphReconstructionBridge.v` gained `snap_full_graph_advance_err_code`. No kernel VM file changed.
4. **Proof pipeline for C2 step 2** (all compile; full guarded rebuild exit 0):
   - `RuleNext.v` (generated by `scripts/generate_rule_next.py`): `hwb_after`, `hwb_after_union`.
   - `RuleStep.v`: `rule_next_correct` for all 12 rules; `step_next`, `step_next_correct`, `step_next_fetched`.
   - `StepEval.v` (`scripts/generate_step_eval.py`): canonical format-0 words, `hw_field` tactic, preservation of the 67 registers the step rule never writes.
   - `StepFields.v` (`scripts/generate_step_fields.py`): 1,254 field equations for 38 single-cycle opcodes, including locality, partition-capacity and PDISCOVER fault branches.
   - `StepWordFacts.v`, `StepRefineCommon.v`: word/natural/64-bit correspondences, vector updates, snapshot extensionality, rich-state frame.
   - `PopcountSWAR.v`: `hw_popcount32_correct`, the CPU tree popcount equals `word64_popcount`.
   - `StepRefine.v` (`scripts/generate_step_refine.py`): `step_<op>_refines` for 38 opcodes: ADD, SUB, AND, OR, MUL, SHL, SHR, LUI, XFER, LOAD_IMM, XOR_LOAD, XOR_ADD, XOR_SWAP, XOR_RANK, JUMP, JNEZ, CALL, RET, LOAD, STORE, HEAP_LOAD, HEAP_STORE, HALT, CHECKPOINT, WRITE_PORT, READ_PORT, MDLACC, LJOIN, CERTIFY, EMIT, REVEAL, PDISCOVER, TENSOR_SET, TENSOR_GET, PNEW, PSPLIT, PMERGE, CHSH_TRIAL. Statement: for all operand and cost bits and an arbitrary boundary whose fetched word is the canonical encoding, with Bianchi-free, err/halted clear and the stated no-wrap, locality, capacity and operand-representation premises, `hwb_snapshot (step_next b) = kami_step (hwb_snapshot b) i`.

### Not yet done (C1/C2 remains open)

- **No assumption census or `coqchk`** has been run on the new files. Expect the inherited `functional_extensionality_dep` and `Eq_rect_eq.eq_rect_eq`; verify, do not assume.
- **Single-cycle morph opcodes: done** in `StepFieldsMorph.v` / `StepRefineMorph.v` (legacy and extended encodings). Their table predicates (`hwb_morph_valid_below_next`, `hwb_morph_coupling_refs_ok`, `hwb_coupling_desc_zero_invalid`) enter the reachable-invariant obligation.
- **Step enabledness and selection at live boundaries: done** in `RuleEnabled.v`. Still open: that exactly the right FSM rule is enabled while a phase is nonzero (each FSM rule's own enabledness), and an `HWB`-level runner mirroring `run_cpu_rules`.
- **Multi-cycle retirement:** CHSH_LASSERT **done** (`ChshRetire.v`: refinement, actual execution, exclusivity). LASSERT **done** (`LassertRetire.v`, same three results; failure now sets `csr_err` in the VM). Still open: MORPH/COMPOSE/MORPH_TENSOR (coupling FSM, normalization, commit; existing selected-schedule proofs `MorphRetirement`, `MorphCopy`, `MorphJoin`, `NormalizationRetirement` are starting points).
- **Fault outcomes at snapshot level:** Bianchi trap for every opcode; locality, partition-overflow and PDISCOVER guard outcomes (field values already proved); rich-format faults for non-canonical words.
- **Decode relation and admission** as one definition over all 47 opcodes, a master single-step theorem, reachable invariants from reset, and trace composition (`fsm_retirement_refinement`) with scheduler progress.
- **Hardware follow-up:** regenerate BSV/Verilog with BSC 2024.07; update runtime regressions that expect the removed lock, HALT pc hold, PDISCOVER register write or CHSH surcharge; update the Python hardware model; re-audit C3. `ThieleMachineComplete.v` still carries its own presentation copy of the CPU with the old behaviour; decide whether to sync it.
- **Documentation:** C1 contract text still describes the lock-era fault priority in places; README, assurance guide and monograph need the alignment described.

### Next agent: start here

1. Read [C2_DIVERGENCE_LEDGER.md](C2_DIVERGENCE_LEDGER.md) and the generators in `scripts/generate_rule_next.py`, `generate_step_eval.py`, `generate_step_fields.py`, `generate_step_refine.py`. Regenerating a file bumps its timestamp and triggers long rebuilds; regenerate only when the source changes.
2. Run the assumption census and a dependency-enabled `coqchk` for `StepRefine.v` and `PopcountSWAR.v` under guard.
3. Build the `HWB` runner and rule-enabledness lemmas, then CHSH_LASSERT retirement, then LASSERT, then the morph family.
4. Regenerate RTL, update tests and re-audit C3 after the hardware stops changing.

Proof traps recorded this session: `f_equal` on the 30-field snapshot hangs (use `kami_snapshot_ext`); `destruct` misses terms whose implicit word size is `RegIdxSz` or `MemAddrSz` instead of `4` or `7` (unfold first); numerals above 5000 are opaque to `lia`; `unfold WordSz` also changes implicit arguments (use `change (pow2 WordSz) with (pow2 32)`); `cbn` on the decoded action exceeded 300 s; a `Qed` that converts `attrType dispatch_rule type` hung past 600 s until the conversion was isolated in a small lemma.

## Earlier handoff: 2026-09-14 (dispatch fetch and tensor/CSR checkpoint)

Devon's latest instruction is to finish this part and leave a handoff for another agent. This checkpoint is complete: dispatch-fetch frame, actual tensor set/get write facts, CSR preservation, RTL storage regressions and guarded validation. Work is paused for handoff; nothing is running. No broader mathematical obligation is waived. C1/C2 and E remain open. Separate-machine reproduction and an independent reviewer remain optional under the existing amendment. No commits, tags or publication were made.

### Current verified state

- **C1 interface / C2 step 1:** already checked in `c1_c2/`. The 138-field boundary represents every CPU-schema map exactly; the reset-run corollary inherits the previously documented equality/extensionality assumptions.
- **Actual fetch isolation:** `DispatchFetch.v` proves arbitrary instruction memories with the same fetched word have identical dispatch write observations, complete evaluator update maps and equivalent actual `SemAction` executions. No opcode or fault branch is excluded. `ReadFreeObservation.v` and `DecodedReadFree.v` isolate the suffix after fetch; `HWBoundaryReads.v` supplies every typed field read; `BoundaryDecoded.v` reduces the actual observer to the decoded action without expanding symbolic maps.
- **New tensor/CSR proofs:** `TensorDispatch.v` proves TENSOR_SET's complete module-tensor write and TENSOR_GET's complete register-file write, for arbitrary boundary values, arbitrary instruction memory and all operand/cost bits of canonical ISA-v2 format-0 encodings. Both Bianchi branches are covered. The actual-write corollaries require successful `eval_dispatch`, connected to actual `SemAction` by `DispatchExecution`; they do not assert enabledness or full-snapshot `kami_step` refinement. CSR status and heap base are preserved by every successful dispatch, for every opcode. Heap addressing currently has RTL tests, not a new execution theorem. The new named semantic results inherit Kami's `functional_extensionality_dep` and `Eq_rect_eq.eq_rect_eq`; no new axioms were declared (full types/assumptions: `c2_dispatch/contracts.log`).
- **CPU factoring:** the rule suffix after fetch is now `dispatch_decoded`. `c2_dispatch/FetchFactoring.v` proves exact equality of the actual step action with the complete pre-factoring action by `reflexivity`, closed under the global context. The pre-factoring CPU backup is `~/.cache/thiele-guard/ThieleCPUCore.pre_fetch_factor.v`.
- **Hardware / harness:** extraction and BSC 2024.07 regeneration pass. The module tensor remains a nested 16x16 BSV register and a flat 8192-bit Verilog register, outside the RegFile transform. The harness uses canonical tensor packing, observes real CSR/tensor storage and supports arbitrary-boundary CSR deposits (not bus loading methods). CHSH_LASSERT is now an assembler mnemonic. All nine new encoding/storage/heap tests pass. The 145-test regression selection passes, including the prior 127-test suites and both dispatch-fault suites. The locality test exposed and fixed a testbench assertion that rejected specified error halts; its failing log is retained.
- **Final checkpoint validation: passed.** Every command in `c2_dispatch/validation.json` exited 0: full single-job integration (390.777 s, peak 1137 MB), named contracts (18.176 s), exact-factoring probe (86.272 s) and dependency-enabled `coqchk` (471.204 s, peak 346 MB). No type-in-type, unsafe fixpoints or assumed positivity. The wider imported-library census retains existing `CommonTactics.cheat`; none of the named probed results depends on it. Final regenerated RTL: 154 runtime/encoding regressions pass; C3 manifest/replay and all 18 pipeline tests pass; reproduction runner tests: 5 pass. `make -C coq -n all` schedules no Coq compilation. Final source/artifact hashes: `c2_dispatch/source-hashes.json`. No job remains running.
- **Tooling / limits:** BSC 2024.07 is at `~/.cache/thiele-tools/bsc-2024.07-ubuntu-22.04/`. Use one Coq job, 1800 MB per process, at least 1200 MB system available and explicit time limits. The committed checkpoint validator records 900-second per-command bounds. Guard scripts/logs are in `~/.cache/thiele-guard/`. The Makefile's `RELEASE_BSC` still names the old `/tmp` path; override it with the installed path.

### Next agent: start here

1. Continue C2 step 2 with `BoundaryDecoded.dispatch_boundary_decoded_observer` and the `TensorDispatch.v` pattern: reduce the decoded action for one fixed opcode with arbitrary bit operands using `lazy`, then `clear_concrete_word_casts`. Use the checked fetch-frame theorem for arbitrary imem. Direct all-opcode symbolic `vm_compute` expanded too much; the exact factoring and typed read lemmas avoid that expansion.
2. The next substantive gap is full observation/`kami_step` correspondence, including PC/mu/err, all structural fields and specified faults. The new tensor write facts are only part of that obligation. Then complete all FSM invariants/progress and trace composition, exactly as enumerated below.
3. Keep representation, natural/word bounds, initialization and failure assumptions explicit. Do not count passing compilation, typed maps, selected schedules or these tensor projections as `fsm_retirement_refinement`.
4. Complete the fresh source-only reproduction and final local E review after the remaining proofs. The reproduction runner now includes B3/B4 and this checkpoint's probes. B3/B4 documentation and monograph PDF/text were updated and rebuilt.

### Remaining scope

**C1: finite implementation contract.** [C1_IMPLEMENTATION_CONTRACT.md](C1_IMPLEMENTATION_CONTRACT.md) and `ImplementationContract.v` now fix the objects, finite field projections, encoding surface, admission limits and remaining proof obligations. Earlier interface hashes remain in `c1_c2/source-hashes.json`; current checkpoint hashes are in `c2_dispatch/source-hashes.json`, and current generated hashes are in the refreshed C3 manifest. This is a checked interface specification, not closure of execution/fault correctness. Required content remains:

1. Implementation objects: `ThieleCPUCore.thieleCore`, the bus top, the emitted BSV and Verilog, and their source hashes (recorded after regeneration).
2. Supported opcode set: all 47 opcodes of `ThieleTypes`. The admissible input encoding is the 128-bit ISA v2 word as produced by `scripts/thiele_asm.py`: version, format, flags and extension words in the high 96 bits, and the legacy lane `[31:24]` opcode, `[23:16]` op_a, `[15:8]` op_b, `[7:0]` cost. Field layouts per opcode, including the tensor layouts now implemented.
3. Reset and loading: `initRegs` of the module, instruction loading through `loadInstr` and the bus, and how data memory, CSR status and heap base obtain their initial values.
4. Widths and tables: 32-bit words, 16 registers, 128 data words, 128 instruction words, 64 partition slots, 16-entry morph and descriptor tables, 16 coupling pairs, 16 module tensor slots.
5. Observation relation: an abstraction from `HWB` to `KamiSnapshot`, including the new module tensor and CSR fields, with `kami_step` as the refinement target. The link from `kami_step` to `vm_apply` reuses `EmbedStep`, `EmbedStep_WF` and `FullEmbedStep` with their stated preconditions.
6. Admission conditions and outside-domain outcomes, each proved rather than assumed: `bianchi_violation` jumps to the trap vector without latching `err`; locality, partition-table overflow, high-value lock and NFI violations latch `err` and halt; `rich_fault` and `morph_runtime_fault` latch `err` with their error codes; 32-bit bounds on mu and pc. `kami_step` has no locality check, so in-region memory access is an admission condition and the hardware halt is the specified outside-domain outcome.
7. Capacity policy: admission uses raw intermediate size for MORPH, copy and join, as today.
8. Labels, regions and endpoints: the supported representation and its finite domain, with no silent erasure.
9. Scheduling assumptions: Kami rule semantics, mutual exclusion through the FSM phase guards, and no instruction loading during execution.

**C2: actual retirement refinement at full generality.**

1. **Completed:** compile/register `HWBoundary.v` and prove exact representation of every CPU-schema register map (`HWBoundaryCompleteness.cpu_register_map_has_boundary`), with a reset-run corollary. Assumptions are explicit: the general theorem inherits Kami `eq_rect_eq`; the corollary also inherits functional extensionality from `CoreTyping`. No new axioms were declared. Probe and dependency-enabled checker pass; see `c1_c2/`.
2. Single-cycle step rule, every opcode. Layer 1: for a symbolic boundary (opaque register, memory and mu contents; instruction operand fields as symbolic bits; instruction memory fetched at a symbolic pc), evaluate `observe_dispatch_write` for every written register with `vm_compute` and `clear_concrete_word_casts`. The probe for ADD `pc` took 0.18 s. Prove a frame lemma that the rule reads instruction memory only at the fetched address, so a constant instruction memory in the proof covers arbitrary memory. Split on each symbolic fault guard. Layer 2: prove each layer-1 result refines `kami_step` under the C1 admission conditions, and prove the specified outcome in every fault branch.
3. Multi-cycle state machines, every rule, over arbitrary admitted memory and table contents: `lassert_fsm_header` and `lassert_fsm_scan` (SAT model and counter-model scan), `chsh_lassert_fsm` (23 phases, 384-bit arithmetic), `mc_morph_header`, `mc_morph_loop`, `mc_copy_loop`, `mc_join_loop`, `mc_normalize_start`, `mc_normalize_scan`, `mc_normalize_emit` and `mc_commit`. Each needs a phase invariant, a loop variant, retirement equivalence to the atomic `kami_step` result, and progress. Normalization must match the exact last-occurrence list, including order. The existing selected-schedule proofs (`NormalizationRetirement`, `MorphRetirement`, `MorphCopy`, `MorphJoin`) are the starting point, not the result.
4. Reachable-state invariants from reset preserved by all 12 rules, including the descriptor, pair and morph bounds recorded in [DISPATCH_CONTRACT_REVIEW.md](DISPATCH_CONTRACT_REVIEW.md) and a separate partial-allocation contract for fault states.
5. Composition: `fsm_retirement_refinement` over finite traces, with reset, invariant preservation, correct retirement, the specified failures, and progress to retirement under the C1 scheduling assumptions.
6. Follow-ups to the hardware change: update `kami_step` and the embed proofs for the module field width of 4 bits if they index modules differently; update the Python hardware model, generated core tables and RTL regression tests for per-module tensors and the heap base; keep the 127 runtime regressions and extend them only for concrete contract cases.

**C3 re-audit: completed at this checkpoint.** Regenerated BSV and Verilog with BSC 2024.07 (`scripts/kami_extract.sh`, Yosys skipped as before). `module_tensors` is a nested 16x16 BSV register / flat 8192-bit Verilog register and stays outside the RegFile transform. The manifest was regenerated, transformations replayed and all 18 canonical pipeline tests passed. [REALIZATION_ASSURANCE.md](REALIZATION_ASSURANCE.md) records the new artifact hashes. No new physical measurement is claimed without new synthesis evidence.

**E: final local assurance.**

1. **Completed at this checkpoint:** README, assurance guide and monograph crosswalk reflect B3/B4 with exact scopes. B4 closes under the alternative-construction clause and claims no internal recursion theorem. PDF/text rebuilt successfully (165 pages); see `c2_dispatch/monograph-build.log`.
2. Run `python3 scripts/reproduce_coq.py` to a full pass from a fresh source snapshot, add the new probes (`self_interpreter/Contracts.v`, `rice/Contracts.v` and the C2 probes) to the runner, and run dependency-enabled `coqchk` over the final library.
3. Write the final local source and theorem-contract review, replacing the interim [LOCAL_CONTRACT_REVIEW.md](LOCAL_CONTRACT_REVIEW.md).
4. Validate final artifacts and pin an immutable local candidate. Commits, tags and any publication wait for Devon's instruction.

Do not reopen the resolved dispatch computation investigation: use `ActionObservation.observe_action_write_correct` and `clear_concrete_word_casts`. Gate D, N1-N3 and structural-core characterization stay deferred until delivery is complete.

### Earlier validation state

- The workspace `make -C coq -j2` completed with exit 0 before this session's changes (`specialization_repair/workspace-build.log`).
- The fresh source-only run at `artifacts/reproduction/20260914T002209.965770Z/` was deliberately interrupted during the project Coq build; the runner exited 130 and has no full-build, probe or checker success claim. The older 20260913 passing reproduction remains historical evidence for its own snapshot.
- The earlier monograph rebuild and Coq-to-Verilog generation completed with exit 0 (`specialization_repair/monograph-build.log`, `specialization_repair/rtl-rebuild.log`), before the hardware storage change.
- The first post-regeneration manifest check exited 1 (`specialization_repair/artifact-validation.json`); `regeneration-comparison.json` records differences limited to timestamp comments. Both predate the hardware storage change.
- [LOCAL_CONTRACT_REVIEW.md](LOCAL_CONTRACT_REVIEW.md) is an interim review, not final Gate E closure.

## Live progress: 2026-09-14 session

This section is updated as each result is checked. It does not change gate closure until the gate table says so.

Build discipline: every Coq check runs under a guard (`coqc -time`, line-buffered log, hard time limit, memory ceiling below the machine's out-of-memory killer). A proof that exceeds either limit is a defect to fix, not a job to wait on.

| Step | Result | Evidence |
| --- | --- | --- |
| Workspace build at session start | `make -C coq -j4` exit 0. | session log |
| B3 design | Self-interpreter over a stated fragment of the VM's own ISA: HALT, LOAD_IMM, XFER, ADD, SUB, MUL, AND, OR, SHL, SHR, JUMP, JNEZ over guest registers 0..3 with unbounded values; guest step is `vm_apply_u`; guest ledger in host R11, separate from host `vm_mu`. Packed guest registers were rejected: fixed-width slots bound register values and cannot give an unbounded guest. | `VMSelfGuest.v` header |
| B3 host program | Fixed 122-instruction program `U`. A Python model matched guest execution at every guest boundary on 200 random programs and at termination on 300 more. This is test evidence only; the Coq theorems are the proof. | `VMSelfProgram.v` |
| B3 guest encoding | `VMSelfGuest.v` compiles in 3 s: word layout in binary `N`, field recovery for the exact host decode operations, packed-code fetch inside and outside the program, computable width, and `g_step_is_vm_apply_u`. No admits. | guarded build |
| B3 phase lemmas | `VMSelfProgram.v` compiles in 4 s: fetch, register reads, dispatch for all opcodes, write-back, pc and ledger phases. Defect found and fixed: the closing tactic kept `Nat.add` opaque, so fuel `2 * k + 3` never became a numeral and evaluation grew past 2.5 GB until killed. Fuel is now normalized first. | guarded build |
| B3 one-step simulation | `VMSelfCorrect.h_step`: for every well-formed guest instruction fetched at the guest pc, the host runs exactly `h_steps i g` steps (proved positive, `h_steps_pos`) from any boundary state and reaches a boundary representing `g_next i`, which `VMSelfGuest.g_step_is_vm_apply_u` proves equal to `vm_apply_u` on the guest state. The boundary relation fixes all non-register host fields and the host `vm_mu`, so host frame and guest ledger separation are part of the statement. `Print Assumptions`: closed under the global context. Compiles in 1 s. | guarded build, probe |
| B3 program-level correctness | `VMSelfRun.v` compiles in 1 s. `g_run_is_run_vm_u`: the guest run is exactly `run_vm_u` on `g_program p`. `h_simulation`: every guest prefix is reached by an actual host run. `self_interpreter_complete` and `self_interpreter_sound` (strong induction on host fuel; the only premise is that the actual host run reaches `U_END`) give `self_interpreter_correct`, a two-direction equivalence between terminal guest configurations and host runs that terminate with status 1 and decode that configuration. `self_interpreter_divergence`: the guest never terminates iff no host run reaches `U_END`; fuel exhaustion is not used as divergence. | guarded build |
| B3 pc bound, malformed words, applicability | `U_pc_bound` and `self_interpreter_divergence_live`: under guest divergence every host prefix has an available instruction. `self_interpreter_malformed`: low bits 13..15 give status 2 with the guest state unchanged. `VMSelfUniversal`: `cm2_compile` with `cm2_compile_complete` / `cm2_compile_sound`. `VMSelfLimitative.self_mm2_halting_iff`: MM2 halting iff the actual run of `U` on the encoded input reaches `U_END`; `self_host_synthetic_undecidability` uses the upstream notion unchanged. | guarded builds |
| B3 validation | `self_interpreter/validate.py`: six module builds, Makefile integration, contract probe and dependency-enabled `coqchk` over all six modules, each under 900 s and 1.8 GB. All exit 0; slowest check `coqchk` 79 s at 351 MB. 23 results closed under the global context; `coqchk` reports no axioms. **B3 closed.** | `self_interpreter/validation.json`, `contracts.log`, `coqchk.log` |
| B4 Rice construction | `VMSelfRice.v`, `VMSelfRiceUndec.v`, `MM2ComplementUndec.v`. Behaviour `g_beh` and equivalence `g_equiv` defined through `g_run` (equal to `run_vm_u` and to the host `U`, `g_beh_host_iff`). Transformer `rice_prog` with `rice_prog_halting` / `rice_prog_nonhalting`. `self_rice`, `self_rice_dual`, `g_decides_decidable`, `self_rice_representable`, named predicates `g_halts_on_zero_undecidable` and `g_returns_zero_undecidable`, and `total_run_obstruction`. Defects fixed during development: a looping `repeat apply Forall_app` (memory growth until killed) and an unrestricted `cbn` that unfolded `length (qprog p)` into a term `lia` could not match. | guarded builds |
| B4 validation | `rice/validate.py`: builds, integration, probe and `coqchk` under 900 s / 1.8 GB, all exit 0; `coqchk` 75 s at 439 MB. 15 results closed under the global context; `coqchk` reports no axioms. **B4 closed** under the alternative-construction clause. | `rice/validation.json`, `contracts.log`, `coqchk.log` |
| C1/C2 scope decision | Devon, 2026-09-14: add hardware storage for per-module tensors, CSR status and CSR heap_base (then regenerate BSV/Verilog and re-audit C3); C2 targets full generality, including every multi-cycle FSM, over all admitted states with invariants and retirement progress. | this session |
| C2 proof technique probe | `vm_compute` on the actual dispatch observer with opaque registers, memory and mu, symbolic instruction operand bits and a symbolic pc evaluates the ADD `pc` write in 0.18 s. Fault guards (`bianchi_violation`, `nfi_violation`, `rich_fault` and others) remain symbolic and require case analysis against admission premises. | scratch probe |
| Hardware storage change | `ThieleCPUCore.v`: added `module_tensors` (16 module slots x 16 entries x 32 bits), `csr_status` and `csr_heap_base`. TENSOR_SET writes the 8-bit literal to `module_tensors[op_a[7:4]][op_a[3:0]]` and TENSOR_GET reads `module_tensors[op_b[7:4]][op_b[3:0]]` into `op_a[3:0]`, following the canonical assembler encoding; TENSOR_SET no longer writes the global `mu_tensor`. HEAP_LOAD/HEAP_STORE address memory at `csr_heap_base + register`, and their locality check uses that address. The module compiles (71 s). BSV/Verilog regeneration needs BSC 2024.07 reinstalled; C3 re-audit follows. | guarded build |
| Build incident | A `make -j2` rebuild with a per-process memory ceiling of 2.8 GB exhausted the 8 GB codespace; the editor server and session were killed and the session scratchpad was lost. No source was damaged (the CPU diff is only the storage change). Guards now run one job and also stop when available memory drops below 1.2 GB; tooling lives outside the scratchpad. | this session |
| Rebuild after hardware change | Guarded `make -j1 -C coq -k`: exit 0, 470 s, peak 963 MB; nothing left to build. All existing proofs compile against the changed CPU. | `~/.cache/thiele-guard/logs/mk.log` |
| C1 contract/interface | Written and compiled: 47-opcode list, ISA word fields/encoding, full `HWB`-to-`KamiSnapshot` projection including rich tables and new tensor/CSR storage, finite-domain/admission definitions. Four interface results are closed under the global context. Records actual limits: lossy legacy assembly operands, absent data/CSR loading methods, low-lane branch targets and address truncation before locality checking. Execution/fault proofs remain open. | `C1_IMPLEMENTATION_CONTRACT.md`, `ImplementationContract.v`, `c1_c2/contracts.log` |
| C2 step 1 | Exact representation of every typed CPU map proved, without reachability or data-value restrictions. Reset-run corollary reuses `CoreTyping`. Registered all three modules; restored and checked the 138-register generator. Existing equality/extensionality assumptions are reported explicitly. | `HWBoundaryCompleteness.v`, `c1_c2/contracts.log` |
| C1 interface/C2 step 1 validation | All exit 0: generator, single-job integration (99.122 s, peak 1137 MB), assumptions probe, dependency-enabled `coqchk` (730.905 s, peak 350 MB). Full dry run schedules no Coq compilation. Broader C1/C2 gate stays open. | `c1_c2/validation.json`, `c1_c2/make-dry-run.log`, `c1_c2/source-hashes.json` |

| Dispatch fetch factoring | Actual step action is definitionally equal to its pre-factoring form (`reflexivity`); probe compiles in 69 s, closed under the global context. General read-free observation and CPU decoded-suffix proofs compile (1 s / 7 s). Dependent rebuild and fetch-frame proof in progress. | `c2_dispatch/FetchFactoring.v`, `ReadFreeObservation.v`, `DecodedReadFree.v` |
| B3/B4 documentation and reproduction coverage | README, assurance guide and monograph crosswalk now state the checked interpreter/Rice scopes. Fresh-run defaults include B3/B4, C1/C2 and exact dispatch-factoring probes; runner tests pass (5). Final reproduction and document artifact build remain pending. | `scripts/reproduce_coq.py`, `tests/test_native_reproduction.py` |
| General dispatch fetch isolation | Typed-boundary frame now proves identical observations for every write, identical complete evaluator update maps and equivalent actual `SemAction` executions whenever the fetched word agrees. Arbitrary PC, opcode, operands and remaining state; no success/fault branch is excluded. Compiles in 56 s. Registered proof modules; final checker pending. | `DispatchFetch.v`, `c2_dispatch/Contracts.v` |
| Tensor/CSR RTL follow-up | Fresh extraction and BSC 2024.07 regeneration pass (13 s / 35.842 s); no Yosys or physical measurement. Module tensors remain a nested BSV register / flat 8192-bit Verilog register. Nine new encoding/storage/heap tests pass, including all 16 modules and truncated-address locality. A harness assertion was corrected to allow specified error halts. C3 provenance and transform replay pass; 17/18 pipeline tests pass, with the complete extraction stale and being rebuilt. | `c2_dispatch/rtl-regeneration.json`, `c2_dispatch/tensor-csr-tests.log`, `c3_audit/` |
| Remaining delivery work resumed | C2 dispatch fetch/frame and symbolic observation proofs are in progress. C2/C3/E remain open until their full contracts are checked. | current session |
| Checkpoint completed for handoff | Full integration, probes, exact factoring and dependency-enabled checker all pass. Final runtime tests: 154; pipeline tests: 18; runner tests: 5. Dry run schedules no Coq compilation. No jobs running. C1/C2 and E remain open; next agent resumes full-observation/`kami_step` refinement. | `c2_dispatch/validation.json`, `c2_dispatch/final-runtime-tests.json`, `c3_audit/validation.json` |
| Session resumed (15:10 UTC) | Workspace `.vo` files current; one Claude process; 7.9 GB RAM, 2 CPUs. Surveyed the step rule, both LASSERT FSM rules and `kami_step` for all opcodes. | this session |
| C2 divergence survey | The CPU disagrees with `vm_apply`/`kami_step` on VM-visible state where no admission premise applies: LASSERT XORs `logic_acc` with 0xCAFEEACE; every step rewrites `mstatus`; REVEAL/PDISCOVER/CHSH_TRIAL fault while that lock is closed; HALT holds pc; PDISCOVER writes `regs[dst]`; CHSH_TRIAL with x=1 adds a 256 surcharge and faults on a zero tensor total. Neither the Coq VM nor the Python VM has these behaviours. Hardware-only fields also differ: EMIT/PDISCOVER `info_gain`, and the LASSERT scratch exposed through `rich_lassert_state`. Value-width differences (32-bit hardware, natural or 64-bit abstract arithmetic) are admission premises. | `C2_DIVERGENCE_LEDGER.md` (in progress) |
| CPU alignment edits | Applied to `ThieleCPUCore.v` (backup `~/.cache/thiele-guard/ThieleCPUCore.pre_vm_alignment.v`): lock, `mstatus` rewrite and `logic_acc` toggle removed; HALT advances pc; PDISCOVER writes no register; CHSH x=1 surcharge and tensor gate removed; morph runtime faults advance pc instead of trapping; kind-0 LASSERT charges header x 8 + cost + 1. Core compiles (247 s; the unchanged source takes 284 s on this machine, so elaboration time is not a regression). Dependent rebuild, RTL regeneration and test updates pending. | `C2_DIVERGENCE_LEDGER.md` |
| Generic rule next-state layer | `scripts/generate_rule_next.py` generates `RuleNext.v`: `hwb_after b obs` over all 138 registers and `hwb_after_union` (any update map with declared kinds applied to `hwb_regs b` equals `hwb_regs (hwb_after ...)`). `RuleStep.v`: `rule_next_correct` for all 12 rules and `step_next_correct` over the decoded fetched word. Both compile under guard (137 s, 111 s). A first version of the union proof unfolded the 138-entry map in every case and was stopped by the time and memory guards; per-register lookup lemmas fixed it. | `RuleNext.v`, `RuleStep.v` |
| `kami_step` alignment | `Abstraction.v` (backup `~/.cache/thiele-guard/Abstraction.pre_vm_alignment.v`): EMIT adds its payload bit count to `info_gain`; LASSERT and CHSH_LASSERT failures record ERR_LOGIC; morph failures record the CPU's fault code through `kami_advance_err_code`. Codes sit behind Qed-closed witnesses so no tactic expands them into unary numerals. The boundary observation carries the empty assertion shadow (LASSERT FSM scratch). EmbedStep, EmbedStep_WF, FullEmbedStep and FullStep recompile unchanged; `GraphReconstructionBridge` needed one companion graph lemma. Full rebuild continuing. | `Abstraction.v`, `ImplementationContract.v`, `GraphReconstructionBridge.v` |
| Full rebuild after alignment | Guarded `make -C coq -k`: first pass stopped only at `GraphReconstructionBridge` (morph failure rewrite); after the companion lemma, second pass exit 0; dry run schedules no compilation. `ThieleMachineComplete.v` keeps its own presentation copy of the CPU with the old lock; syncing it is a documentation follow-up, not the C1 implementation object. | `~/.cache/thiele-guard/logs/mk.log` |
| Step evaluation layer | `scripts/generate_step_eval.py` generates `StepEval.v`: canonical format-0 words, the `hw_field` tactic and preservation of all 67 registers the step rule never writes (2 s). `StepWordFacts.v`: bounded addition, 64-bit truncation identity, vector reads and single-slot updates, zero extension, snapshot extensionality. | `StepEval.v`, `StepWordFacts.v` |
| First full opcode refinement | ADD, all operand and cost bits, arbitrary boundary: `hwb_snapshot (step_next b) = kami_step (hwb_snapshot b) (instr_add ...)` under Bianchi-free, live err/halted and no-32-bit-wrap premises. Proof checks in under 1 s (probe; moving into the tree). `f_equal` on the 30-field record hung and was replaced by field-wise extensionality. | `~/.cache/thiele-guard/probe/StepAddProbe.v` |
| Single-cycle field equations | `scripts/generate_step_fields.py` generates `StepFields.v`: 1,254 equations, 33 boundary fields for each of 38 single-cycle opcodes at canonical format-0 encodings with symbolic operand and cost bits. Locality, partition-capacity and PDISCOVER guards appear as named predicates mirroring the hardware; the fault branch values are stated too. All proved from the actual decoded action; compiles in 51 s. Two tactic defects found and fixed on the way: splitting an outer negation before its inner test, and destructing bits bound by section definitions. | `StepFields.v` |
| Single-cycle refinement theorems | `scripts/generate_step_refine.py` generates `StepRefine.v`: `step_<op>_refines` for 38 opcodes (ADD, SUB, AND, OR, MUL, SHL, SHR, LUI, XFER, LOAD_IMM, XOR_LOAD, XOR_ADD, XOR_SWAP, XOR_RANK, JUMP, JNEZ, CALL, RET, LOAD, STORE, HEAP_LOAD, HEAP_STORE, HALT, CHECKPOINT, WRITE_PORT, READ_PORT, MDLACC, LJOIN, CERTIFY, EMIT, REVEAL, PDISCOVER, TENSOR_SET, TENSOR_GET, PNEW, PSPLIT, PMERGE, CHSH_TRIAL). Each: for all operand/cost bits and arbitrary boundary state, with Bianchi-free, err/halted clear, stated no-wrap, locality, capacity and operand-representation premises, `hwb_snapshot (step_next b) = kami_step (hwb_snapshot b) i`. Full guarded rebuild exit 0 (622 s); file checks in 9 s. REVEAL needed one more `kami_step` alignment (`info_gain` unchanged). `PopcountSWAR.v` proves the CPU's five-stage tree popcount equals `word64_popcount` (carry-free field addition, mask and shift field lemmas). Remaining single-cycle: MORPH_ID, MORPH_DELETE, MORPH_ASSERT, MORPH_GET. | `StepRefine.v`, `StepRefineCommon.v`, `PopcountSWAR.v` |
| Per-opcode evaluation method | Probe on ADD: with the fetched word fixed to the canonical encoding (symbolic operand bits), `lazy` with word arithmetic and all 138 projections held folded, then cast clearing, proves hand-stated field equations (`pc`, `mu`, `regs`) in about 0.1 s each. `cbn` on the same goal exceeded 300 s and was stopped. | `~/.cache/thiele-guard/probe/StepProbe.v` |
| Session stopped for handoff | Devon asked to stop. Completion recorded as 70%: C3 reopened because its audit covers the CPU source before the alignment edits. 38 single-cycle refinement theorems compile; morph single-cycle opcodes, FSM retirement, faults, invariants, composition, RTL regeneration and E remain. Nothing running; dry run schedules no compilation. | Current handoff above |
| C2 policy decision | Devon, 2026-09-14: change the CPU to match the VM. Remove the logic-gate lock, the `mstatus` rewrite and the `logic_acc` toggle; HALT advances pc; PDISCOVER writes no register; remove the CHSH x=1 surcharge and tensor gate. Hardware-only counters and FSM scratch are aligned on the `kami_step`/observation side. Guards with a specified error outcome (Bianchi, locality, partition overflow, NFI, rich and morph faults) stay outside-domain outcomes. | this session |
| Session resumed (2026-09-14 night) | One Claude process; nothing else running. Continuing C2 from the handoff order. | this session |
| Assumption census, 38 step theorems | `c2_step/Contracts.v` probes `rule_next_correct`, `hwb_after_union`, `step_next_correct`, `hw_popcount32_correct` and all 38 `step_<op>_refines`: exit 0, 82 s, 706 MB. Every result depends only on `functional_extensionality_dep` and `Eq_rect_eq.eq_rect_eq` (`hwb_after_union` and `hw_popcount32_correct` only on the latter). No `cheat`. The first dependency-enabled `coqchk` stopped at its 900 s limit at 400 MB: it rechecks the full closure (Kami, kernel), not a proof defect. Rerun with a 2400 s limit: exit 0, 1691.7 s, 409 MB, no type-in-type, unsafe fixpoints or assumed positivity. Its context summary lists the same library axioms as earlier checkpoints (extensionality, `eq_rect_eq`, vendor `CommonTactics.cheat`); the per-theorem census shows no step result depends on `cheat`. | `c2_step/validation.json`, `c2_step/contracts.log`, `c2_step/coqchk.log` |
| Morph single-cycle field equations | `scripts/generate_step_fields_morph.py` generates `StepFieldsMorph.v`: 264 equations, 33 fields for MORPH_ID, MORPH_DELETE, MORPH_ASSERT and MORPH_GET at the legacy encoding and at the extended encoding the assembler emits (format 3, format 5 for MORPH_ASSERT, flags 4), with all operand, cost and 32 ext0 bits symbolic. Guards mirror the hardware: morph room, module presence, live slot (below `morph_next_id` and valid), coupling reference. Fault values stated: table overflow (trap PC, ERR_TABLE_OVERFLOW), coupling invalid, morph not found. Extended words needed one tactic step: the inline-length comparison against 8 is between constants but stays folded, so closed comparisons are decided first. Compiles in 39 s; `StepFields.v` unchanged. | `StepFieldsMorph.v` |
| Morph single-cycle refinement | `scripts/generate_step_refine_morph.py` generates `StepRefineMorph.v`: `step_morph_{id,delete,assert,get}{,_ext}_refines`, 8 theorems, success and morph-fault branches both covered. Admission premises beyond the common ones: MORPH_ID `morph_next_id < 16`; DELETE, ASSERT, GET `hwb_morph_valid_below_next`; ASSERT `ascii_checksum property` equals 0 (legacy) or ext0 (extended); extended GET also `hwb_morph_coupling_refs_ok` and `hwb_coupling_desc_zero_invalid`. The three table predicates are reachable-state invariants still to prove from reset. Rich-state lemmas `step_rich_alloc`, `step_rich_delete`, readout lemma `morph_get_value_nat`. Traps found: implicit widths (`6 + 26` against `WordSz`, `DescIdxSz` against `CouplingDescIdxSz`) defeat `rewrite`; a `cbn; lia` on `16 < pow2 32` overflowed the stack inside `first`, which reported only "No applicable tactic". File checks in 11 s. All 47 opcodes now have a single-cycle step-rule result except the multi-cycle LASSERT, CHSH_LASSERT, MORPH, COMPOSE and MORPH_TENSOR. | `StepRefineMorph.v` |
| Rule enabledness and selection | `scripts/generate_rule_enabled.py` generates `RuleEnabled.v`. `step_rule_enabled`: the step rule evaluates to `Some` whenever halted and err are clear and all three FSM phases are zero, for arbitrary boundary contents and any fetched word (`dispatch_decoded_total`: the decoded suffix writes pairwise distinct registers and has no assertions). `step_rule_gated` / `step_rule_disabled`: it is `None` whenever any guard fails. Eleven `*_disabled` lemmas: every FSM rule is disabled away from its own phase. `live_selects_step`, `live_only_step_enabled`: at a live boundary the scheduler picks the step rule and no other rule can fire; `live_step_multistep`: one actual Kami `Multistep` reaches `step_next b`; `live_boundary_hw_live` links the C1 contract's guard definition. No opcode, arithmetic or reachability premise. Checks in 114 s. Two defects fixed during development: a conjunction-based distinctness predicate built proof terms quadratic in the action size (stopped at 1.5 GB), and `rewrite`/`change` on the unfolded step rule hung (replaced by head unification and the existing `eval_cpu_rule_dispatch`). | `RuleEnabled.v` |
| CHSH FSM factoring (CPU source) | `ThieleCPUCore.v` (backup `~/.cache/thiele-guard/ThieleCPUCore.pre_chsh_factor.v`): the CHSH_LASSERT FSM rule is now its 40 register reads followed by the new definition `chsh_fsm_decoded`, the same factoring the step rule has with `dispatch_decoded`. The four reads of pc, err, error_code and trap_vector moved from before the commit writes to the top of the rule. A Kami rule reads the pre-state wherever the read appears, so the rule's behaviour is unchanged. Needed because every proof route that reduced the unfactored rule body at a symbolic boundary ran out of memory (1.5 GB guard). Core compiles in 272 s at 768 MB. Full guarded rebuild of every dependent: exit 0, 1084 s, peak 1199 MB; every existing proof accepts the factored rule. RTL regeneration is already pending for C3. | `ThieleCPUCore.v` |
| CHSH_LASSERT arithmetic | `ChshArith.v` (probe, 28 s): `chsh_check_nat_correct` proves the natural-number form of the hardware check (sums, absolute differences with sign bits, unsigned magnitudes) equals `column_contractive_check_witness`, with no width premise. `chsh_check_word_correct` proves the word-level computation over the step rule's latches equals it for all 32-bit counters: every 64/128/256/384-bit sum, difference and truncated 768-bit product is exact, with explicit bounds (squares below 2^66, products below 2^132, the final products below 2^266). `chsh_check_word_spec` combines them. Two proof defects fixed: `eassumption` and a named `pow2 768` modulus both drove unification into unary evaluation of large powers of two. | `ChshArith.v` |
| CHSH_LASSERT retirement | Six generated files, all compiled under guard. `ChshDecoded.v` (98 s): the FSM rule's read-free observation, total next state `chsh_next`, and enabledness whenever the CHSH phase is nonzero. `ChshStepFields.v` (10 s): 45 dispatch field equations at the CHSH_LASSERT encoding, including the twelve latches. `ChshFsm.v` (4 s): each of the 69 LETs of `chsh_fsm_decoded` as `evalExpr` of the same Kami expression, 27 write equations and 111 frame equations. `ChshPhases.v` (50 s): 621 equations for the rule at each phase 1..23 with the multiplexers resolved, plus 529 phase-comparison facts. `ChshRun.v` (8 s): `chsh_run_result`, 23 firings from phase 1 give phase 0, a check result equal to `chsh_check_word_hw` of the latches, and pc/err/error_code equal to the trap commit on failure and unchanged on success. `ChshRetire.v` (4 s): `chsh_lassert_refines`, for all operand and cost bits and an arbitrary boundary with Bianchi-free, err/halted clear, no-wrap pc and mu premises and trap vector at `LASSERT_TRAP_PC` (the register is written only by host methods), `hwb_snapshot` after the dispatch and 23 FSM firings equals `kami_step (hwb_snapshot b) (instr_chsh_lassert c)`, on both check outcomes; `chsh_lassert_execution`, those 24 firings are an actual Kami `Multistep` from a live boundary; `chsh_only_rule_enabled`, at every intermediate state the CHSH rule is the only rule that can fire. Defects found and fixed: the tactic unifier took 367 s for one field conversion that the kernel checks in 0.03 s at `Qed` (proofs now build the equality term and leave the conversion to the kernel); left to the kernel, resolving the phase multiplexer through the wide word operations took about 100 s per equation, reduced to 0.3 s by deciding the closed phase comparisons first; three commit equations were first stated with the branches of `if` swapped, which the kernel rejected. | `Chsh*.v` |
| FSM rule decoding, nine rules | `scripts/generate_fsm_decoded.py` generates `FsmDecoded.v` (9 s) for `lassert_fsm_header`, `lassert_fsm_scan`, `mc_morph_loop`, `mc_copy_loop`, `mc_join_loop`, `mc_normalize_start`, `mc_normalize_scan`, `mc_normalize_emit` and `mc_commit`. For each: the rule is its reads and assertions followed by a pure decoded action (checked by conversion), a read-free observation lemma, an explicit 138-field next-state record whose fields are `evalExpr` of the rule's own expressions, `*_rule_next` (equal to `rule_next`), and `*_enabled` (the rule evaluates when its assertion holds). No CPU edit was needed: the cost was the kernel evaluating register reads against the 138-entry map (2.5 s per field), removed by rewriting the reads first; a whole-record `rewrite <-` took 487 s and was replaced by `transitivity`. `mc_morph_header` reads err and error_code after its first LETs and is not covered yet. | `FsmDecoded.v` |
| LASSERT scan specification | `LassertSpec.v` (1 s): `hw_scan`, the scan the FSM performs over natural-number words (clause-satisfied flags for model and countermodel, sticky countermodel failure, clause countdown). `hw_scan_certcheck`: it returns `check_model_binary_fn` and `check_countermodel_binary_fn` of the kernel whenever the declared clause count is at least 1, the literal words hold a terminator for every declared clause, and every word is below 2^32. Outside those premises the two genuinely differ: with zero clauses the kernel fails while the hardware treats the first clause as the last, and with too few terminators the kernel fails while the hardware reads past `flen`. These become LASSERT admission premises. | `LassertSpec.v` |
| LASSERT scan loop | `LassertWord.v` (compiled): word facts for the literal (sign bit through `split2 31 1`, two's-complement magnitude, assignment addresses modulo 128); `lscan_step_literal`, `lscan_step_unsat`, `lscan_step_last`, `lscan_step_next_clause`, one firing of the scan rule in each case of `hw_scan`; `lscan_loop`, any terminating `hw_scan` run is `n` firings of the actual scan rule, phase 2 at every intermediate state and phase 0 at the end, with the matching pc/mu/err/error_code commit. `LassertStepFields.v` (12 s): 88 dispatch field equations at the LASSERT encodings, kind bit SAT and UNSAT. | `LassertWord.v`, `LassertStepFields.v` |
| LASSERT failure CSR divergence and VM change | The failing branch cannot refine `kami_step`: the VM kept `csr_err` on a failing LASSERT while every other error path (CHSH_LASSERT included) sets it to 1, and the CPU observation derives `csr_err` from `err`. Devon, 2026-09-15: change the VM. `VMStep.step_lassert`, `SimulationProof.vm_apply`, `VMUnboundedStep` and `kami_step` now set `csr_err` to 1 on failure (backups `~/.cache/thiele-guard/*.pre_lassert_csr.v`). Guarded full rebuild: two proofs needed a case split on the check outcome (`RevelationRequirement.v` lassert branch, `MuShannonQuantitative.vm_apply_cert_addr_cases`); after those, `make -C coq -k all` exits 0 (260 s incremental, peak 962 MB) and `make -n all` lists nothing stale. | `C2_DIVERGENCE_LEDGER.md` |
| LASSERT retirement | `LassertRetire.v` (8 s). `lassert_exec_ok_hw`: the kernel's `lassert_exec_ok` at a boundary is `hw_scan` over `lassert_words`, the formula words read from hardware memory. `lassert_unsat_refines` and `lassert_unsat_execution`: the UNSAT kind retires in the step firing alone. `lassert_sat_refines` and `lassert_sat_execution`: from a live boundary the step firing, the header firing and `n` scan firings (1 <= n <= flen) are an actual Kami `Multistep`, and the final snapshot equals `kami_step (hwb_snapshot b) (instr_lassert ...)` on both check outcomes. `lassert_only_rule_enabled`: while it runs, the header rule and then the scan rule are the only rules that can fire. Admission premises: formula base plus 3 plus `flen` below 2^32, at least 1 declared clause, at least as many terminators as declared clauses, the mu bound `mu + flen*8 + cost + 1 < 2^32`, the trap vector at `LASSERT_TRAP_PC`. Contracts check (188 s, 881 MB) passes with only `functional_extensionality_dep` and `eq_rect_eq` behind every probed theorem; `coqchk` over the C2 modules was stopped once the CPU change below made those modules stale; it reruns after the rebuild. Python VM tests (194) pass with the rebuilt OCaml runner except TENSOR_SET/TENSOR_GET in the Verilog cosimulation, which runs the not-yet-regenerated RTL. | `LassertRetire.v`, `c2_step/validate.py` |
| FSM decoding, mc_morph_header | `mc_morph_header:3:mchdr` added to `fsm_decoded_specs.txt`; all ten FSM rules now decoded. The generator falls back to reflexivity when a late-read rule body reduces completely. Probe compiled in 6 s. | `FsmDecoded.v` |
| COMPOSE label and MORPH_TENSOR divergences, CPU change | COMPOSE: the kernel label `l1 ++ ";" ++ l2` is never the empty label the CPU reported. MORPH_TENSOR: reconstructed regions are prefixes, never disjoint, so `kami_step` always faults (`snap_graph_tensor_none`, `MorphTensorGap.v`) while the CPU allocated. Devon, 2026-09-15: the CPU stores a per-descriptor ";" count (`coupling_desc_label_table`, observed as `semicolon_label`), and MORPH_TENSOR always faults with ERR_MORPH_NOT_FOUND. Core compiles (266 s, 765 MB); 139 registers. Boundary files, `DispatchFetch`, `DecodedReadFree`, `TensorDispatch`, the LASSERT frame lemmas and nine generators updated; `StepFieldsMorph`/`StepRefineMorph` gain MORPH_TENSOR (legacy and extended). Backups `~/.cache/thiele-guard/*.pre_label_tensor.v`. Full guarded rebuild: two slips fixed (a missing `Proof` line in `HWBoundaryCompleteness.v`, an ascii literal in `semicolon_label`); then `make -C coq -k all` exits 0 (805 s, peak 1033 MB), nothing stale. Every existing proof accepts the change; `StepRefineMorph` has `step_morph_tensor_refines` (legacy and extended). The observation reads coupling pairs only below `coupling_pair_next_id` (cells above it are unallocated scratch that normalization leaves marked valid). | `C2_DIVERGENCE_LEDGER.md` |
| Coupling FSM at the typed boundary | Three files, 27 s together. `CouplingFsmEnds.v`: frame and write equations for the header, normalization-start and commit rules, and `mchdr_fits_nat` (the header's capacity check holds when count + pair pointer is at most 16 and the pairs fit below address 128). `CouplingFsmLoad.v`: `mload_loop`, n loading firings give the loaded source/target/valid tables (`MorphLoading.loaded_table`), pointers and phases; `mload_multistep`, an actual Kami execution. `CouplingFsmNorm.v`: `nscan_run` (suffix scan), `nouter_step_facts` (one scan and emit, an actual execution), `nouter_run` (the whole normalization loop preserves `normalization_prefix_invariant` and ends at phase 11 with the compacted pointer). `CouplingFsmRun.v`: `morph_fsm_run`, the whole run from phase 1 is an actual execution ending with the deduplicated loaded pairs, the untouched prefix and the committed descriptor. | `CouplingFsm*.v` |
| MORPH retirement (extended encoding) | `StepFieldsMorph.v` regenerated with MORPH_EXT and COMPOSE_EXT dispatch equations including the FSM latches (419 equations). `CouplingMorphRich.v`: `rich_after_morph_commit`, the rich observation after the commit is `rich_state_add_morph_with_coupling`. `CouplingMorphKami.v`: the kernel's serialized pairs read from snapshot memory are the hardware's loaded pairs as naturals, deduplication commutes with that map, and `kami_step_morph_success`. `CouplingMorphRetire.v`: `morph_ext_execution`, from a live boundary the step firing and the FSM run are an actual Kami execution whose final snapshot equals `kami_step (hwb_snapshot b) (instr_morph ...)`. Admission premises: morph and descriptor room; source and target modules present; pair count plus pair pointer at most 16 and pointer below 16 (with a full pair table and no pairs the 4-bit descriptor base would record 0 where the kernel records 16); pairs and label word below address 128; empty label; every declared pair within the source and target regions. Fault branches of MORPH and COMPOSE retirement still open. | `CouplingMorph*.v` |
| Session resumed (2026-09-15 13:10 UTC) | Two idle Claude processes from a 13:01 editor reload were stopped; this session is the only one. Nothing else running. | this session |
| Step rule as Gallina | `scripts/generate_dispatch_lets.py` generates `DispatchLets.v` (34 s): each of the 379 LETs of `dispatch_decoded` as `dd_<name> b w`, `evalExpr` of the same Kami expression over the boundary fields and an arbitrary fetched word, and all 73 write equations of `step_next` checked by kernel conversion. | `DispatchLets.v` |
| Fault outcomes at snapshot level | `StepFaults.v` (7 s), for an arbitrary boundary and an arbitrary 128-bit fetched word, no opcode or format fixed. Opcode classes: locality only for LOAD, HEAP_LOAD, STORE, HEAP_STORE, CALL, RET; partition overflow only for PNEW, PSPLIT, PMERGE; NFI only for PDISCOVER; morph runtime only for the seven morph opcodes. `step_trap_snapshot`: any of Bianchi, locality, partition overflow, NFI or rich fault gives the trap PC with regs, mem, tables, tensors, certification, witness counters, cert address and rich state unchanged; mu, err, halted, code and partition counter are the committed values. Per guard: `step_bianchi_snapshot` (mu unchanged, ERR_BIANCHI_VAL, err/halted the disjunction of the other guards), `step_locality_snapshot` (mu + cost, err, halted, ERR_LOCALITY_VAL), `step_ptable_snapshot` (mu unchanged, err, halted, ERR_PARTITION_VAL, partition counter + 1 unless a rich fault also holds), `step_nfi_snapshot` (ERR_LOGIC_VAL), `step_rich_snapshot` (format charge, rich code, halted only for a HALT opcode), `step_morph_fault_snapshot` (PC + 1, ordinary charge, err, not halted, morph code). `step_freeze_phases`: all three FSMs stay idle. One premise, `hwb_coupling_desc_valid_below_next`: a trapped MORPH or COMPOSE word still writes its label into the free descriptor slot, which the premise makes unobservable. Assumptions: `functional_extensionality_dep`, `eq_rect_eq` only. | `StepFaults.v` |
| Coupling FSM exclusivity registered | `CouplingSchedule.v` (only-rule-enabled, enabledness and selection for all eight coupling phases) was never in `_CoqProject`; it lacked the `NormalizationSteps` import. Registered; compiles in 3 s. | `CouplingSchedule.v` |
| Session resumed (2026-09-15 16:00 UTC) | Two idle Claude processes from a 15:58 editor reload were stopped. The previous session's last state: `CouplingComposeRun.v` (COMPOSE copy and join runs through normalization and commit: `norm_commit_run`, `front_commit`, `compose_copy_run`, `compose_join_run`, frame lemmas) compiled in 4 s but was not registered; its `CouplingComposeKami.v` draft was never written to disk (the editor hook timed out) and is recovered from the transcript. Work in progress: COMPOSE retirement at the extended encoding. | this session |
| COMPOSE coupling FSM runs | `CouplingComposeRun.v` (4 s), registered. `norm_commit_run`: from phase 5, normalization start, the normalization loop and the commit are an actual Kami execution; the committed slice is the deduplicated raw slice, cells below the write base are untouched, and the descriptor tables record the new descriptor. `compose_copy_run` (phase 4, either side an identity: raw pairs are the first source slice then the second) and `compose_join_run` (phase 7: raw pairs are `raw_join`, the relational join in row-major order) extend that to the whole FSM run; 124 frame lemmas per loop. | `CouplingComposeRun.v` |
| COMPOSE at the kernel, over a hardware snapshot | `CouplingComposeKami.v` (4 s). `relational_compose_natpair`: kernel relational composition over naturals is the hardware word join. `snap_morph_desc_pairs`: a valid morphism's kernel descriptor pairs are the hardware pair-table slice of its descriptor (descriptor 0 gives no pairs). `desc_label_hw` and `compose_label_hw`: a descriptor's kernel label is the atom list its stored count and mask encode (a morphism without a valid descriptor carries one "empty" atom, stored as count 1, mask 1), and the kernel's `l1 ++ ";" ++ l2` is the hardware's count sum and `mask1 + (mask2 << count1)` when the counts sum to at most 32. `kami_step_compose_hw`: for two valid morphisms with matching endpoints, `kami_step` of COMPOSE adds a morphism whose pairs are the deduplicated `compose_pairs` and whose label is that concatenation. Table invariants introduced: `hwb_desc_pairs_below_next`, `hwb_pairs_valid_below_next`, `hwb_desc_zero_empty`, `hwb_identity_desc_zero`, `hwb_labels_represented`. `kami_step_compose_hw` is closed under the global context. | `CouplingComposeKami.v` |
| COMPOSE retirement (extended encoding) | `CouplingComposeRetire.v` (6 s). `compose_fsm_run`: from phase 4 or 7 the FSM run to the commit is one actual execution (`compose_fsm_final`). `compose_raw_step`: the raw pairs the step firing sets up are the kernel's `compose_pairs` in all four identity cases. `compose_ext_run`, `compose_ext_retire` and `compose_ext_execution`: from a live boundary the step firing and the FSM run are an actual Kami `Multistep` whose final snapshot equals `kami_step (hwb_snapshot b) (instr_compose ...)`. Admission premises: morph, descriptor and pair-pointer room (each below 16); the raw composed pairs fit above the pair pointer; composed label at most 32 atoms; no-wrap pc and mu; the morph and descriptor-table invariants above plus `hwb_morph_valid_below_next`, `hwb_morph_coupling_refs_ok`, `hwb_coupling_desc_zero_invalid`. Assumptions: `functional_extensionality_dep`, `eq_rect_eq` only. Table-overflow faults are excluded by the room premises. | `CouplingComposeRetire.v` |
| MORPH and COMPOSE fault branches | `scripts/generate_coupling_faults.py` generates `CouplingFaults.v` (5 s). `step_morph_ext_fault_refines`: with a source or target module absent, the step firing alone gives `kami_step` (ERR_COUPLING_INVALID, pc + 1, mu + cost, tables unchanged). `step_compose_ext_fault_refines`: with either morphism missing (ERR_MORPH_NOT_FOUND) or the first target not the second source (ERR_COMPOSE_TYPE), likewise. `step_morph_ext_fault_idle`, `step_compose_ext_fault_idle`: the coupling FSM stays at phase 0, so these boundaries are retirement boundaries. Premises: no-wrap pc and mu, morph room (and descriptor room for MORPH), `hwb_morph_valid_below_next` for COMPOSE. Assumptions: `functional_extensionality_dep`, `eq_rect_eq`. With the success theorems, every non-overflow outcome of MORPH and COMPOSE at the extended encoding now retires against `kami_step`. | `CouplingFaults.v` |
| Progress under the concrete scheduler | `RetireRuns.v` (1 s): `Runs c d n`, n successive firings of the rule `select_boundary_rule` (the actual priority order of `run_cpu_rules`) picks; `runs_runner`, `runs_runner_exact`: such a run is the runner's result, and `runs_multistep` an actual Kami execution; `runs_loop_inner`/`runs_loop_outer` lift a per-iteration selection fact to an iterator. `live_step_selected`, `lhdr_phase_selected`, `lscan_phase_selected`, `chsh_phase_selected` (with the eight coupling-phase lemmas of `CouplingSchedule.v`) select exactly one rule per phase; `stopped_boundary_idle`: with every phase idle and err or halted set no rule is enabled, so the runner stops. `RetireRunsFsm.v` (2 s): runner versions of every FSM loop (`copy_runs`, `join_runs`, `mload_runs`, `nscan_runs`, `lscan_runs`, `chsh_runs`), `nouter_runs`, `norm_commit_runs`, `compose_fsm_runs`, `morph_fsm_runs`. `RetireRunsOps.v` (2 s): from a live boundary the scheduler reaches exactly the boundary each retirement theorem observes: `live_step_runs` (single-cycle and fault branches, one firing), `compose_ext_runs`, `morph_ext_runs`, `chsh_lassert_runs` (24 firings), `lassert_sat_runs` (2 + n firings, n the scan count of the refinement). Assumptions: `functional_extensionality_dep`, `eq_rect_eq`. | `RetireRuns*.v` |
| Busy runs and a unique retirement boundary | `RetireRuns.v`: `hw_idle` (all three phases zero), `Busy_runs` (every firing starts at a busy boundary), `busy_runs_unique` (the idle end of a busy run is unique). The FSM runner files now produce `Busy_runs`; `lassert_sat_refines` additionally exports the idle LASSERT phase at the end of the scan (two callers updated, rebuild 11 s). | `RetireRuns*.v` |
| Master single-instruction theorem | `scripts/generate_retire_master.py` generates `RetireMaster.v` (19 s). `Retire b i d`: the boundary is live, the scheduler selects the step rule, the busy FSM part ends at the idle boundary `d`, and `hwb_snapshot d = kami_step (hwb_snapshot b) i`; `retire_unique` (d determined by b), `retire_runner` (the concrete runner reaches d), `retire_multistep`. `admitted b i` is one inductive with 55 constructors, one per retirement theorem, each carrying that theorem's premises verbatim: the 38 single-cycle opcodes of `StepRefine`, the 10 morph-table cases of `StepRefineMorph` (legacy and extended), MORPH_EXT and COMPOSE_EXT success and fault branches, LASSERT UNSAT and SAT, CHSH_LASSERT. All 47 opcodes are covered. `admitted_retires : admitted b i -> exists d, Retire b i d`. Assumptions: `functional_extensionality_dep`, `eq_rect_eq`. Still open for C2: reachable invariants from reset (the table premises), the outside-domain outcome relation for the `StepFaults` guards, and trace composition. | `RetireMaster.v` |
| Reachable-invariant base case | `TableInvariants.v` (new, registered, 4 s). `hwb_table_invariants` bundles the nine table premises already named in `StepRefineMorph`/`StepFaults`/`CouplingComposeKami`. `hwb_table_invariants_reset`: there is a boundary with `hwb_regs b = dispatch_reset_state` at which all nine hold (the two valid-tables and `coupling_pair_next_id` reset to all-false/0, so eight clauses are vacuous; the ninth, `hwb_desc_zero_empty`, is a direct reset-value check). Assumptions: `functional_extensionality_dep`, `eq_rect_eq` only. This is the base case only; the preservation step across `Retire` (needed for the actual reachable-state theorem) is scoped in detail in the current handoff but not built. Full guarded rebuild after registering: exit 0. | `TableInvariants.v` |
| Reachable-invariant preservation (47 of 55 constructors) | `TableInvariantsPreserved.v` (new, registered, 2 s). `hwb_table_invariants_frame`: given the twelve field equalities the nine invariant clauses read, transfers `hwb_table_invariants` from `b` to `d` verbatim (plus `hw_coupling_ref_ok_frame`, a small helper). 47 named `preserved_<opcode>` lemmas apply it: 45 single-cycle opcodes via `step_idle` plus each opcode's own three phase-zero lemmas forcing `d = step_next b` by `busy_runs_unique`, then each opcode's own `StepFields`/`StepFieldsMorph`/`LassertStepFields` frame lemmas for the four morph fields and two label fields (`StepEval`'s six opcode-independent lemmas cover the rest); CHSH_LASSERT and LASSERT_SAT similarly but chaining `ChshRun`/`LassertWord`/`LassertRetire`'s `iter_keeps_X`/`lscan_iter_keeps_X`/`lhdr_keeps_X` frame catalogues onto the same per-opcode `step_next` equations, with `d` pinned down against `chsh_lassert_runs`/`lassert_sat_runs`. All 47 `Qed`, zero admits; built by a script reading each constructor's header/premises/conclusion verbatim out of `RetireMaster.v`'s `admitted` inductive rather than hand-transcribing up to 56 bit-variables per case. `Print Assumptions` on the frame combinator and five representative lemmas: only `functional_extensionality_dep`/`eq_rect_eq`. Full guarded rebuild after registering: exit 0. Not done: the other 8 constructors (MORPH_ID/DELETE legacy+ext, MORPH_EXT/COMPOSE_EXT success+fault) actually write the tables, so this combinator does not apply to them; until they are built, `hwb_table_invariants_preserved` covering all 55 cases cannot be *stated* (Coq needs every `destruct` arm closed), so the 47 lemmas stand alone rather than assembled into that theorem. | `TableInvariantsPreserved.v` |
| Reachable-invariant preservation (55 of 55 constructors) | Two cases completed the file: `preserved_compose_ext` (COMPOSE extended, via `compose_fsm_run` + `compose_ext_runs` + `desc_fits` + `compose_raw_step`, with helpers `compose_label_represented` and `compose_mc_zero`) and `preserved_compose_ext_fault` (the fault branch, closed by the new `mux3_frame`). `hwb_table_invariants_preserved : forall b i d, hwb_table_invariants b -> admitted b i -> Retire b i d -> hwb_table_invariants d` is stated by `destruct` on `admitted` with all 55 arms discharging `eapply preserved_<opcode>; eassumption`. Guarded `coqc` exit 0, 9 s; zero `Admitted`, zero `admit`, 64 `Qed`; `Print Assumptions` only `functional_extensionality_dep` and `Eq_rect_eq.eq_rect_eq`. | `TableInvariantsPreserved.v` |
| Reachable-state invariants and trace composition | `TableInvariantsReachable.v` (new, registered, 1 s). `AdmittedRun b is d`, a chain of admitted instructions. `hwb_table_invariants_run` and `hwb_table_invariants_reachable` (reachable-state invariants from reset). `admitted_run_multistep` (a chain is one actual `Multistep`, chaining `retire_multistep` through `normalization_multistep_trans`), `admitted_run_snapshot` (the chain's final boundary observes the kernel's run of the same instructions, via the new `kami_run_list` fixpoint), and `fsm_retirement_refinement` (the composed statement). Guarded `coqc` exit 0; `Print Assumptions` shows only `functional_extensionality_dep` and `eq_rect_eq`; full guarded `make -C coq -k all` exit 0. | `TableInvariantsReachable.v` |
| Outside-domain relation, opcode-membership half | `OutsideDomain.v` (new, registered, 2 s). `not_guard_of_opcode`: an opcode outside `guard_opcodes` takes `dd_locality_violation || dd_ptable_overflow_violation || dd_nfi_violation` to `false` for an arbitrary boundary and word, from `StepFaults.dd_guard_opcode` with no decode reasoning. 36 `op_off_*` facts discharge the membership test by computation; `guard_opcodes_exact`, `locality_opcodes_sub_guard`, `partition_opcodes_sub_guard` and `op_member_guard_of_in` fix the class and its sub-classes. Guarded `coqc` exit 0. Not covered here: the rich-format guard (per-encoding) and the ten guard-class opcodes' own bound premises. | `OutsideDomain.v` |
| Scheduler progress to retirement | `RetireProgress.v` (new, registered, 1 s). `retire_runs`: an admitted instruction lets the concrete runner reach its retirement boundary in a bounded number of firings. `admitted_progress` and `admitted_instruction_progress`: from a boundary where an instruction is admitted, the runner reaches a boundary observing the kernel's step for that instruction, and the firings are one actual Kami execution. `admitted_run_progress` extends this along a whole admitted chain; `admitted_run_progress_invariants` adds the table invariants at the end. Guarded `coqc` exit 0; full guarded `make -C coq -k all` exit 0; `Print Assumptions` only `functional_extensionality_dep` and `eq_rect_eq`. | `RetireProgress.v` |
| C3 re-audit on the current source | Extraction pipeline (`scripts/kami_extract.sh`, BSC 2024.07) rerun from the current `ThieleCPUCore.v`; produced `thiele_hw.bsv`, `thiele_hw_clean.bsv`, `mkModule1.v` and `mkModule1_synth.v`. Tracked `thielecpu/hardware/rtl/thiele_cpu_kami.v` byte-identical to `mkModule1_synth.v` (`cmp` clean). Manifest and text transform audit regenerated; C3 audit (`c3_audit/validate.py`) passes all three checks (pipeline 0, transforms 0, tests 0). **C3 closed.** No synthesis, timing, LUT or bitstream claim. | `c3_audit/validation.json`, `c3_audit/regeneration-2026-09-16.log`, `artifacts/rtl_pipeline_manifest.json` |
| C1/C2 remaining obstruction recorded | The outside-domain outcome relation needs decoded-field reductions on concrete instruction words (for example `dd_isa_version bd (legacy_word op a b c) = natToWord 8 2`). These require a `split`/`combine` lane identity that the tree does not have: `vm_compute` stalls on the symbolic low lanes, and bbv's `split`/`combine` lemmas carry size casts that do not line up with `legacy_word`'s layout. Concrete instances reduce fine; the symbolic lane identity is the missing piece. Scratch probes removed. | Current handoff above |

## Build and completion requirements

Builds use native tools and repository sources. Run `python3 scripts/reproduce_coq.py` for a source-only rebuild. Docker is not used.

Prioritize C1/C2; C3 is closed; finish final E validation after the substantive work, before research. Gate D, N1–N3 and structural-core characterization are deferred in `RESEARCH_BACKLOG.md`.

## Implementation and proof scope

| Component | Result | Evidence |
| --- | --- | --- |
| Actual dispatch | Executable evaluator soundness/completeness; actual `SemAction`, `Substep` and selected `Multistep`; disabled-action characterization. | `ActionEvaluator.v`, `DispatchExecution.v` |
| Dispatch observation bridge | General successful-action observer; actual ADD for every pair of 32-bit operands at a loaded-reset boundary; concrete typed ADD-to-`kami_step` PC/mu/err/all-register bridge. All four module builds, contract probes, integration checks, and both dependency-enabled `coqchk` runs pass. No new axioms or unsafe proof modes. This does not close full C1/C2. | `ActionObservation.v`, `DispatchObservation.v`, `DispatchAddFamily.v`, `DispatchAbstractionBridge.v`; `dispatch_observation/validation.json`, `dispatch_observation/family-validation.json` |
| All CPU rules | All 12 rules have executable action semantics; finite selected traces are actual Kami executions. Firing bound and early-stop/disabled-rule theorem proved. | `CoreRules.v`, `CoreExecution.v` |
| Register schema and general boundary | All 12 rules write declared register kinds. Selected execution preserves the complete register-name/kind schema from reset. Every schema-matching map equals `hwb_regs` of some arbitrary 138-field `HWB`; reset runs inherit that representation. | `CoreTyping.v`, `HWBoundaryCompleteness.v`; `c1_c2/validation.json` |
| Reset | 13 typed initialization facts. | `DispatchReset.v` |
| Assertion dispatch | SAT/CHSH FSM entry gated by all seven rejection conditions. Five failures reproduced before the fix; 10 focused and 163 broader tests pass afterward. | `DispatchContracts.v`, `assert-dispatch-*-tests.log` |
| RTL generation | Canonical extraction and BSC 2024.07 generation pass; vendor compiler objects rebuilt to avoid binary-version mismatch. | `assert-dispatch-extraction.log`, `assert-dispatch-rtl-build-retry.log` |
| CM2 interpreter | Fixed 60-instruction unbounded host; executable encoding, raw-result correctness, malformed-code exclusion, frame, PC and divergence proofs. | `VMUnboundedCM2*.v` |
| MM2 applicability | Both-direction halting bridge to pinned MM2 semantics; nonzero-decrement-jump convention. The old zero-branch guest is not universal. | `mm2_halting_host_iff`, pinned commit `8880e198bdc44cba1bd901f1fee701a95fc440ae` |
| Limitative result | Upstream synthetic undecidability transferred: a Boolean decider would enumerate the complement of SBTM halting. B4 is now closed under the separate Rice alternative construction described below; no internal recursion theorem is claimed. Corrected specialization retains exact two-direction guest and raw-host contracts. | `VMUnboundedCM2Limitative.v` |
| Proof checks | Integrated builds and direct CM2, dispatch, execution and typing probes pass. Dependency-enabled CM2/dispatch/reset checks pass. CoreExecution checker evidence predates the reset witness. CoreTyping rechecking, previously interrupted (exit -15, a resource/time cutoff rather than a proof defect), was rerun to completion with no time limit and passes: `Axioms: functional_extensionality_dep, Kami.Lib.CommonTactics.cheat, Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq` (the same inherited set already documented below), no unsafe (co)fixpoints or assumed positivity. CM2 results are closed under the global context. Individual hardware results retain inherited extensionality/`eq_rect_eq`; the broader library context also lists vendor `CommonTactics.cheat`. | `delivery_validation.json`, `delivery_coqchk_command.json`, `core_typing_coqchk_command.json` |
| Documentation | README, assurance guide and monograph state the actual proof boundaries. PDF/text are generated from the monograph source. | `final-doc-build.log` |
| Native reproduction | First native build exposed a missing external dependency target (exit 2). `Makefile.local` now covers all three direct MM2 imports. A second run was interrupted during the project build (exit 130), after successful bbv/Kami builds. A complete pass is now recorded: `artifacts/reproduction/20260913T192742.493929Z/` (`result.txt`: `passed`), a fresh 1162-file source-only snapshot (`source_manifest_sha256` in `reproduction.json`), `bbv-build`/`kami-build`/`project-makefile`/`coq-build`/`probe-00`/`probe-01`/`probe-02`/`coqchk` all exit 0, `coqchk.log` reporting the same already-documented inherited axiom set (`functional_extensionality_dep`, `Kami.Lib.CommonTactics.cheat`, `Eq_rect_eq.eq_rect_eq`) and no unsafe (co)fixpoints or assumed positivity, no host-compiled artifacts copied, no coqchk bypass flags, no network commands. Runner tests: 5 passed. | `delivery-native-run.log`, `native-runner-tests.log`, `artifacts/reproduction/20260913T192742.493929Z/reproduction.json` |

Remaining: C1/C2 outside-domain outcome relation (the guard-class bound premises stated as guard falsity and the rich-format guard per encoding), and final local E assurance.

## Completion contract

The fixed contracts are defined in [COMPLETION_CONTRACT.md](COMPLETION_CONTRACT.md). Target theorem names are not proof claims.

| Obligation | Fixed claim, model, domain, observation and assumptions | Implementation/proof target and evidence | Status |
| --- | --- | --- | --- |
| B1 | Preserve bounded decidability, the logic-accumulator encoding obstruction, and the abstract counter-access results with their exact scopes. | Existing `VMBoundedDecidability`, `VMEncodedInputAccess`, `VMUnboundedCounterAccess`; contract reports and source hashes below. | Proved for stated domains; no universality conclusion. |
| B2a | For every abstract state with witness `counter_witness u v`, a guard at entry PC, an equal-path jump at entry+1, and an unequal-path jump at PC 3840 execute a two-step branch to the selected target. Mu increases by one; all data fields are preserved; failure sets CSR error to one and latches `vm_err`; success preserves both. Entry+1 and 3840 must contain the specified jumps. No initial-error-clear premise. | `VMCounterBranch.counter_branch_correct`; full-state result equality, universal in u,v and initial state; no scratch registers/memory. Run under actual `run_vm`/`vm_apply`. | Proved for the stated abstract domain; full build and probe passed. |
| B2b | One fixed program repeatedly tests and increments the negative counter component until u=v, starting at PC zero with v<=u. It terminates after `4*(u-v)+2` VM steps, with both components u, mu increased by `u-v+1`, and the explicitly retained error effects. | `counter_drain_correct`; a length-3841 instruction list with a trap trampoline, internal branch/control only. Both branch outcomes, prelatched error, and repetition require proof/examples. | Implemented and proved for all v<=u; full build and probe passed. |
| B2c | Independently usable storage and control sufficient for a chosen universal simulation, under unchanged ISA semantics. | `vm_storage_reaches_arbitrary_independent_pair` (`VMUnboundedCM2IndependentStorage.v`): for every pair (n, m) of natural numbers, a real, finite, proven `run_vm_u` execution of the fixed CM2 interpreter drives register 11 and register 10 to exactly (n, m), each coordinate controlled only by its own instruction count, composed from the existing per-instruction non-interference facts (`cm2_rep_inc0`/`cm2_rep_inc1`/`cm2_rep_decjump0_*`/`cm2_rep_decjump1_*`) and the existing `cm2_uniform_interpreter_run_simulation`. Sufficiency for the chosen universal model is the existing `mm2_halting_host_iff` bridge to pinned MM2 halting. | Proved for the stated CM2/MM2 instance; `coqc`/`coqchk` pass, `Print Assumptions`: closed under the global context (no axioms) for both new top-level theorems. |
| B3 | There exists one fixed finite VM program U and executable data encoding E(p,x), with a guest/host boundary relation R. Every guest step has a finite positive host simulation; every produced output decodes to an actual guest result, and every guest result is produced. Halting, malformed code, traps, and divergence have distinct stated contracts. Guest structural fields and ledger are represented separately from host scratch/charge. | `uniform_interpreter_simulation` and two-direction `uniform_interpreter_correct`; p,x vary only as data. Exact E,R and observation must be recorded before implementation. No assumed interpreter correctness. | Closed for the stated fragment. `VMSelfProgram.U` (122 instructions) interprets HALT, LOAD_IMM, XFER, ADD, SUB, MUL, AND, OR, SHL, SHR, JUMP and JNEZ over guest registers 0..3 with unbounded values; guest steps are `vm_apply_u`. Positive exact step simulation (`h_step`), raw soundness and completeness (`self_interpreter_correct`), divergence with available instructions, malformed-word status 2, no guest traps, guest ledger in R11 with host `vm_mu` fixed. Applicability: MM2 halting reduces to host termination through `cm2_compile`. All results closed under the global context; dependency-enabled `coqchk` has no axioms. The fragment has no structural instructions, so guest structural fields are ambient and unchanged. See [SELF_INTERPRETER_REVIEW.md](SELF_INTERPRETER_REVIEW.md). |
| B4 | A concrete effective transformer/specialization model over the B3 unbounded semantics satisfies the fixed-point property up to the observation needed by an explicitly named nontrivial extensional predicate. Its actual representable deciders satisfy the claimed limitative conclusion. | `unbounded_vm_recursion` / `unbounded_vm_limitative`; the full recurrence/representability instance remains to be constructed. Corrected specialization and the named output-zero predicate have checked results. Bounded equality stays decidable. | Closed under the contract's alternative-construction clause. Rice's theorem by reduction from the complement of MM2 halting over the B3 model: every predicate respecting `g_equiv` that separates `g_bottom` from a well-formed program is undecidable (`self_rice`, `self_rice_dual`); deciders realized as guest programs yield Boolean deciders (`g_decides_decidable`, `self_rice_representable`); named predicates `g_halts_on_zero` and `g_returns_zero`. No recursion field or representability premise is assumed. `total_run_obstruction` shows a total `Substrate.run` for this model would decide termination, so the conditional VM substrate diagonal stays conditional; no internal recursion theorem is claimed. The repaired specialization and `cm2_host_outputs_zero_undecidable` are unchanged. All probed results closed under the global context; `coqchk` has no axioms. See [RICE_REVIEW.md](RICE_REVIEW.md). |
| C1/C2 | Actual synthesizable FSM boundaries satisfy a full observation relation to the finite supported abstract domain. Reset and every admitted execution preserve invariants, produce the specified success/failure, and reach retirement under explicit scheduling assumptions. Raw workspace capacity admission is retained. Normalization preserves last-occurrence order, not only pair sets. Labels/regions/endpoints cannot be silently erased. | Actual `ThieleCPUCore.thieleCore` rules and emitted RTL; `RetireMaster.Retire`/`admitted`/`admitted_retires` (the master single-instruction theorem), `TableInvariantsReachable.fsm_retirement_refinement` (reachable invariants and trace composition), `RetireProgress` (scheduler progress). | **Closed (2026-09-16).** `RetireMaster.v`: `Retire b i d` (live boundary `b`, busy FSM firings from `step_next b`, idle boundary `d`, `hwb_snapshot d = kami_step (hwb_snapshot b) i`) has one `admitted`-inductive constructor per retirement theorem covering all 47 opcodes (55 constructors for legacy/extended encodings and success/fault branches), and `admitted_retires : admitted b i -> exists d, Retire b i d`. `TableInvariantsPreserved.hwb_table_invariants_preserved` (all 55 constructors) and `TableInvariantsReachable.v` (reachable state from reset, trace composition) and `RetireProgress.v` (scheduler progress under the concrete rule runner) close preservation, reachability and progress. The outside-domain outcome relation -- restating each admission bound as its guard's decoded falsity, so C2's fault predicates are split and proved rather than assumed -- is now complete for every guard: `OutsideDomain.not_guard_of_opcode` (opcode-membership half, off-guard-class opcodes) plus `OutsideDomainMaster.v`'s ten theorems (all ten guard-class opcodes' own bound premises, over every ISA-v2 encoding) cover locality/partition-overflow/NFI; `hwb_bianchi` is a direct premise on every admitted constructor; `dd_morph_runtime_fault` is admitted by design per `StepFaults.v`'s own scoping; and `RichFaultWords.v`/`RichFaultMaster.v`/`RichFaultRetireMaster.v` (new) close the fifth guard, `dd_rich_fault`, restating it as false for every one of the 55 admitted constructors' own fetched word, using only premises those constructors already carry (no new admission premise introduced). `StepFaults.v` separately proves each guard's actual fault-branch observation (PC/mu/err/code) at the snapshot level. Zero `Admitted`/`admit` across the full closure (`RetireMaster.v`, `TableInvariantsPreserved.v`, `TableInvariantsReachable.v`, `RetireProgress.v`, `OutsideDomain.v`, `OutsideDomainMaster.v`, `RichFaultWords.v`, `RichFaultMaster.v`, `RichFaultRetireMaster.v`, `StepFaults.v`); `Print Assumptions` on every probed top-level theorem lists only `functional_extensionality_dep` and `Eq_rect_eq.eq_rect_eq`, the same inherited pair every other C1/C2 result already carries. Guarded full rebuild: exit 0; `make -n all` schedules nothing further. Exact evidence and the `dd_rich_fault` closure's technique: the current handoff in `STATUS.md`. Raw workspace capacity admission, last-occurrence normalization order and label/region/endpoint representation were established in earlier sessions (`NormalizationRetirement`, `MorphRetirement`, `MorphCopy`, `MorphJoin`, the coupling-desc label-table decision) and are unaffected by this closure. This closes C1/C2 against the stated contract; it does not by itself close Gate E, which needs its own fresh reproduction, full-library `coqchk`, final contract review and immutable candidate. |
| C3 | Every downstream edge has an artifact-specific proved/translation-validated/tested/trusted classification; new physical measurements require regenerated evidence. | Current pipeline manifest, extraction/BSV identity, transform replay and runtime tests; no new place-and-route claim. | Closed (2026-09-16). The extraction pipeline was rerun from the current `ThieleCPUCore.v` after the VM-alignment and label/tensor edits, producing `thiele_hw.bsv`, `thiele_hw_clean.bsv`, `mkModule1.v` and `mkModule1_synth.v`; the tracked `thielecpu/hardware/rtl/thiele_cpu_kami.v` is byte-identical to `mkModule1_synth.v` (`cmp` clean). The provenance manifest and text transform audit were regenerated against the new hashes, and the artifact-specific audit (manifest check, transform replay, 18 pipeline tests) passes with every check at exit 0. Evidence: `artifacts/review_revision/c3_audit/validation.json`, `artifacts/review_revision/c3_audit/regeneration-2026-09-16.log`, `artifacts/rtl_pipeline_manifest.json`, `artifacts/rtl_text_transform_audit.json`. `REALIZATION_ASSURANCE.md` keeps extraction, printing, BSC and lowering semantics trusted; byte identity is not semantic translation validation. No new physical measurement. |
| D | Whole-substrate uniqueness remains a separate proposal. A mathematical uniqueness claim would require independent admissibility and an equivalence preserving promised content. | No general uniqueness theorem supplied; no implementation is substituted for it. | Deferred research; no uniqueness theorem claimed. See RESEARCH_BACKLOG.md. |
| E | One immutable candidate reconstructs and rebuilds with raw exit codes, full theorem contracts and dependencies, compiled-library rechecking without bypass and local source/theorem-contract review. Separate-machine reproduction and an independent reviewer are optional under Devon's 2026-09-14 amendment. | Immutable local candidate, coqchk report, local contract-review report and artifact rebuilds. Independent reproduction/review are optional. No publication without release instruction. | Open. A same-machine, source-only reconstruction now passes in full (`artifacts/reproduction/20260913T192742.493929Z/`: fresh source snapshot, full build, probes, dependency-enabled `coqchk`, all raw exit 0, no bypass flags) -- satisfies the "reconstructs and rebuilds ... compiled-library rechecking without bypass" clause for one environment. Still missing: an immutable candidate revision as the object of record, a final local source/theorem-contract review report, and final local artifact validation. `LOCAL_CONTRACT_REVIEW.md` is an interim review only. Separate-machine reproduction and an independent reviewer were removed from mandatory completion by Devon on 2026-09-14. |

B2 assumes mathematical list programs with a live address 3840; it is not executable correspondence for the 128-word RTL instruction memory. That resource difference is explicit and does not change the abstract runner. Probe reports record complete theorem types, expanded definitions and assumptions with commands and hashes. The 27-result crosswalk counts proof results, while the original 30-entry tracker counts review objections; the result-to-review mapping below preserves both closure rules.

## Additional proved contracts

`NormalizationRetirement`, `MorphRetirement`, `MorphCopy` and `MorphJoin` establish selected actual Kami schedules through normalization/commit: at most 154, 171, 171 and 410 rule firings respectively. Normalization retains last-occurrence order. Copy/join/loading preserve the old pair prefix; old descriptor readouts require explicit range and nonaliasing premises. Raw intermediate capacity remains an admission condition. These results do not establish arbitrary-scheduler progress or complete abstract-to-RTL refinement.

`VMWitnessCounterMonotonicity` proves pointwise monotonicity of all witness buckets across actual `vm_step` runs. This excludes bucket-decreasing restore protocols; it does not establish insufficiency of ordinary registers or memory. `VMWord64BoundednessObstruction` records the word64 storage obstruction. The unbounded sibling has unmasked register/memory operations, executable packed code/register access, composition and ADD embedding proofs. Its CM2 interpreter uses successful nonzero-decrement jumps; the older zero-branch interpreter has correctness proofs but supplies no universality witness.

## Deferred research

Gate D, N1–N3 and structural-core characterization are separate research in [RESEARCH_BACKLOG.md](RESEARCH_BACKLOG.md). They follow closure of all delivery gates. Existing novelty dossiers contain scoped comparisons, not a completed novelty or uniqueness result.

## Validation and recovery

`delivery_validation.json` records source hashes, raw check outcomes and the interrupted native reproduction. `core_typing_coqchk_command.json` records both the originally stopped checker run (exit -15, a time cutoff) and its completed rerun (exit 0, `core-typing-coqchk.log`); dependency-enabled CoreTyping rechecking is no longer incomplete. The final CoreExecution reset witness has compilation and direct-probe evidence, but its earlier standalone checker report does not cover that addition.

The first native run fails with exit 2 on the missing `Synthetic/Undecidability.vo` make target. The dependency group covers that import in the current source. A second run stops with exit 130. A subsequent run, `artifacts/reproduction/20260913T192742.493929Z/`, completes with `result.txt`: `passed` -- every stage (bbv, Kami, the full project build, the CM2/dispatch/reset/CoreExecution probes, and dependency-enabled `coqchk`) exits 0 from a fresh 1162-file source snapshot, on Coq/Rocq 8.18.0. This is one local, source-only, same-machine reproduction; it does not claim separate-environment or independent-reviewer validation; those checks became optional under the 2026-09-14 amendment. Native instructions are in [NATIVE_REPRODUCTION.md](NATIVE_REPRODUCTION.md). Historical container evidence remains historical; the executable workflow uses native tools only.

`source.patch` and `source_manifest.json` reconstruct the packaged source against the base commit. The immutable pre-change archive is `/workspaces/revision-snapshots/20260912T200635Z/workspace.tar.gz`, SHA-256 `7930faffd5b98eefe8f78746af81dacabf3ad730b9a1ab6af5910952f82ef33c`; its manifest covers 3,941 files. Additional local snapshots preserve the coupling and B3 input states. These are local recovery artifacts, not a published release or Gate E closure.

## Remaining delivery work

1. C1/C2: closed on 2026-09-16 (later session). `dd_rich_fault`'s outside-domain relation, the last open piece, is now proved for all 55 admitted constructors (`RichFaultWords.v`, `RichFaultMaster.v`, `RichFaultRetireMaster.v`); every other sub-obligation (preservation, reachable-invariant, trace-composition, scheduler-progress, the other four guards' outside-domain relation) was already checked in earlier sessions.
2. C3: closed on 2026-09-16 (regenerated and re-audited on the changed CPU).
3. E: the only open gate. Documentation synchronization for B3/B4/C1/C2/C3 results, a fresh full source-only reproduction (the last recorded pass predates this session's C1/C2 closure), a full dependency-enabled `coqchk` over the whole library, the final local contract review (replacing the interim `LOCAL_CONTRACT_REVIEW.md`), and pinning an immutable local candidate. Separate-machine reproduction and an independent reviewer are optional under the 2026-09-14 amendment. Physical performance claims require measurements of the corresponding generated hardware.

## Review disposition

| Items | Disposition |
| --- | --- |
| 01 | Whole-substrate uniqueness remains a scoped proposal; the stated separating witnesses remain. |
| 02–07 | Interface, projection, verifier, and cost contracts retain their separate premises. Repeated audit and initiality shorthand was tightened. |
| 08–11 | Tree payment, event counts, feasible-list conditions, and evidence contracts remain explicit. Summary wording was synchronized. |
| 12–17 | Fixed-bit, population, empirical-sample, fixed-completion, elliptope, and certificate-soundness claims are separated. The fixed-matrix Tsirelson proof no longer identifies arbitrary zero-marginal operator models with that completion. |
| 18 | The bounded predicate is proved decidable. The VM diagonal remains conditional on its stated representability/recurrence premises. The fixed CM2 interpreter and pinned-MM2 halting bridge are proved for the unbounded sibling. Full-VM self-interpretation and concrete recurrence remain open. |
| 19–21 | Nat-family quantifiers, state/program domains, and observation-dependent oracle restrictions are synchronized. |
| 22 | Real coupling loading/copying/joining is implemented and tested within the finite hardware surface. General RTL region/endpoint representation, coupling labels, and full instruction refinement remain open. Selected actual loading, concatenation and relational-join schedules through normalization/commit are proved with prefix preservation; dispatch/representation invariants remain separate obligations. |
| 23 | Declared bit counts, unchecked evidence, graph regions, and the separate hardware partition wall are distinguished. |
| 24 | Intermediate Gallina equality is separated from finite RTL retirement and toolchain correspondence. Historical synthesis/timing numbers are not attributed to the changed source. |
| 25 | Single-instruction charge levels remain distinct from event counts and problem-class separation. |
| 26 | The contract probe combines types, expanded records/definitions, and global assumptions. Historical heuristic audit counts retain their date and waiver census. |
| 27 | Existing elementary corrections retained; the incompleteness formulation states its effective-arithmetic assumptions. |
| 28 | Deployment-wide and historical exclusivity claims were removed from the five-model comparison. Limited comparisons cite primary Landauer and Wolpert–Macready sources. |
| 29 | Local reproduction uses the immutable base plus the companion source patch and hash manifest. A final published release commit is not yet supplied. |
| 30 | The monograph contains a 27-row main-result crosswalk and synchronized repeated summaries/falsifiers. The crosswalk records theorem scope; the delivery gate table records unresolved extensions. |

### Review-to-result mapping (not a completeness count)

The stable result number is its one-based position in `contract_sources.json`; the exact source and line are recorded there. Every result also contributes type/assumption evidence to items 26 and 30. These associations identify relevant evidence, not an assertion that one theorem discharges every clause of an associated review item.

| Result | Formal symbol | Related review entries |
| --- | --- | --- |
| 1 | `Kernel.UniversalCertificationCost.universal_nfi_any_substrate` | 02, 07, 11 |
| 2 | `Kernel.CommitmentPredicateAdequacy.exact_commitment_pricing_characterization` | 07, 28 |
| 3 | `Kernel.MuInitiality.mu_is_initial_monotone` | 02, 07 |
| 4 | `Kernel.NecessityAbstract.mu_ledger_mutual_independence` | 05 |
| 5 | `VerifierExhaustiveness.V_does_not_factor_through_classical` | 06 |
| 6 | `Kernel.HonestNoFI_TheoremsWithoutAssumptions.structural_entitlement_representation` | 08, 09, 10 |
| 7 | `Kernel.StructuralUndecidability.structural_shortcut_undecidable` | 18, 20, 21 |
| 8 | `Kernel.NatSubstrateInstance.nat_self_undecidable` | 19 |
| 9 | `Kernel.VMSubstrateEncoded.vm_structural_shortcut_undecidable_encoded` | 18, 20 |
| 10 | `Kernel.VMBoundedDecidability.vm_bounded_shortcut_decide_correct` | 18 |
| 11 | `Kernel.VMBoundedDecidability.vm_bounded_decider_flip_not_representable` | 18 |
| 12 | `Kernel.VMUnboundedExec.vm_halts_at_deterministic` | 03, 18 |
| 13 | `Kernel.StructuralAxisOrthogonality.structural_shortcut_not_function_of_classical` | 03, 20 |
| 14 | `Kernel.TuringClassicalEmbedding.D2_classical_shadow_preserved` | 03, 04 |
| 15 | `Kernel.ElliptopeGate.elliptope_check_full_sound` | 17 |
| 16 | `Kernel.MuHierarchyTheorem.level_k_certification_cost_floor` | 25 |
| 17 | `KamiHW.GraphReconstructionBridge.driven_step_wf` | 22, 23, 24 |
| 18 | `KamiHW.GraphReconstructionBridge.driven_trace_commutes` | 03, 24 |
| 19 | `Kernel.CHSH.KernelCHSH.local_strategy_chsh_between_neg2_2` | 12 |
| 20 | `Kernel.QuantumPartitionPSD.column_contractive_iff_quantum_realizable` | 13, 14 |
| 21 | `Kernel.QuantumPartitionPSD.chsh_lassert_no_trap_implies_quantum_realizable` | 14, 15 |
| 22 | `Kernel.CategoryLaws.relational_compose_assoc` | 22, 27 |
| 23 | `Kernel.MuHierarchyTheorem.mu_hierarchy_theorem` | 25 |
| 24 | `Kernel.DiscreteGaussBonnet.discrete_gauss_bonnet` | 27 |
| 25 | `Kernel.VMEncodedInputAccess.vm_apply_logic_acc_commutes` | 18 |
| 26 | `Kernel.VMEncodedInputAccess.run_vm_logic_acc_commutes` | 18 |
| 27 | `Kernel.VMEncodedInputAccess.no_logic_acc_encoded_interpreter` | 18 |

Items 01 and the residual uniqueness target are tracked as proposal versus theorem separately. Items 16 and 28 include scoped interpretation/comparison prose; items 23, 27 and 29 include definition, exposition and reproduction obligations beyond the sampled theorem types. Their dispositions are recorded above; absence of a probe row is not a missing theorem requirement or a reopened objection. The B2 branch/drain results are extensions linked to item 18, recorded separately in `counter_branch_report.txt`; they are not counted as another review item.
