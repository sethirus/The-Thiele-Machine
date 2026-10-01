---
name: ground-truth-plan-execution
description: "Authoritative tracker for Devon's 2026-09-30 COMPLETE PLAN: THE THIELE MACHINE, TO GROUND TRUTH; supersedes the older 11-item execution status"
metadata:
  node_type: memory
  type: project
  originSessionId: f6985b3e-12aa-4174-8f86-800155332120
modified: 2026-10-01T00:20:00Z
---

# Authority

The controlling instruction is Devon's pasted `COMPLETE PLAN: THE THIELE
MACHINE, TO GROUND TRUTH` in session
`f6985b3e-12aa-4174-8f86-800155332120`, transcript record beginning at the
2026-09-30 04:27:59 UTC user message. It contains Rules R1 through R12 and
Parts 0 through 8. It replaces the older 11-item closeout as the execution
plan. It also replaces the earlier request for no more commits: R9 requires a
commit after every item. Stop only before merge or tag.

The older `research-plan-execution.md` is historical evidence. Its DONE or
changed-claim labels do not close an item in this plan.

# Current authoritative checkpoint, 2026-10-01

Part 1 is closed. The repository is on `work/research-plan` at
`d5cb4e7e` with a clean worktree. The current assumption receipt is coherent
for 13,318 queries across 450 files. The latest result hook passed 1,193 tests,
the complete Coq build, vacuity and assumption checks, and Inquisitor.

Completed post-Item-1.1 sequence:

- `282e30e8`: compliant Item 1.2 freeze.
- `1b6e8c5b`: Item 1.2 closes 19 PROVED and 36 REFUTED. The frozen 21/34
  prediction was wrong for `generalized_billed_schedule_equivalence` and
  `generalized_surcharged_schedule_equivalence`.
- `37b33024`: compliant Item 1.3 freeze.
- `66feb214`: Item 1.3 REFUTED the universal event-swap claim with a
  fixed-register-width zero-cost graph-allocation event; certification still
  satisfies the frozen five-result bundle.
- `900f2f2a`: assumption-receipt totals are synchronized automatically without
  weakening any gate.
- `adfbeac0`, `3f745351`: Item 1.4 freeze and PROVED result. The audit covers
  8,156 of 8,156 physical lines and 41 exact corrections; the final independent
  read passed.
- `4888677e`, `10aeb40d`: Item 1.5 Round 1 freeze and REFUTED result. Frozen
  `README.md:600` incorrectly called the general pointer criterion a theorem.
- `61d682a2`, `d5cb4e7e`: corrected Item 1.5 Round 2 freeze and PROVED result.
  The ledger covers 40 of 40 occurrences and the corrected independent read
  passed. Round 1 remains REFUTED.

The next work is Part 2 Item 2.1, in order. Do not reuse the quarantined Part 2
scratch as a freeze or result. First write and observe a red freeze test, then
commit a dated exact statement for monotone multi-valued records and the Round
4 decomposition question before attempting any proof.

# Standing rules

- Do the numbered items in order. Do not skip, merge, or reorder them.
- Commit an exact dated freeze before any proof attempt. A changed definition
  starts a new dated round. Keep earlier rounds unedited.
- Final outcomes are PROVED, REFUTED, PROVED BUT KNOWN, or BLOCKED. A result
  with assumptions is PARTIAL under R4 and is not PROVED.
- Use real specifications with cited sections. Record every interpretation.
- Run the five R6 hollowness checks before a proved result counts.
- Use at least three genuinely different proof strategies before BLOCKED.
- Every commit keeps the full gates on. The final report also needs a fresh
  serialized Coq rebuild.
- Published prose is timeless ground truth. Freeze and process records live in
  `research/rounds/` and external trackers.
- Preserve Devon's voice. No em dashes, no `we` or `our`, no correction
  framing, no bulk prose rewrites, and no hand edits to generated plaintext.
- Keep the name No Free Insight. Never add AI attribution.
- Guard every Coq build, use `make -j1`, and keep each Coq process below the
  project memory ceiling.

# Repository truth at the 2026-09-30 Codex audit

- Workspace: `/workspaces/The-Thiele-Machine`
- Branch: `work/research-plan`
- HEAD: `0b32407da22ff923364c19f472dd85d30a2fbac6`
- The branch is eleven commits ahead of cached `origin/main`.
- The audited Part 1 work is preserved in stash object
  `9641ba231bf2e9dcc95d0182fbb4cc6ce4eaff53`. The worktree is clean at Part 0
  Item 0.2 Round 2 result commit `bcd4df1eed79ea3c17a2a68c0b0028cf4a248c9d`.
  Item 1.1 is committed and the worktree is clean. Nothing is staged and there
  are no conflicts.
- Do not reset, clean, drop, pop, or restore the Part 1 stash wholesale.
- The older stale Claude pair was terminated by exact PID. The current VS Code
  Claude pair was left running and idle. No Coq, vacuity, pytest, Inquisitor,
  receipt, or publication process is active.

Durable commits after v3.3.0:

- `34971852`: late research baseline.
- `d930fcac`: weak and strong uniqueness refutations; Round 3 freeze.
- `89760103`: schedule form; Round 4 and incremental freeze; EVM/Casper work.
- `d9effe75`: record axis, minimal narrowing, cost-framework work, extraction
  boundary correction.
- `be27f21c`: classifier and zero-gap prose corrections.
- `2bb7e5ea`: outcome-led documents and prose-audit repair; retained as evidence
  from the first, order-invalid Part 0 attempt.
- `a9c8270e`: Part 1 event-swap definitions and predictions; chronology-invalid
  as a Ground Truth preregistration and preserved only as history/input.
- `5d1245e6`: Item 0.1 PROVED operationally; Part 0 Round 2 freeze.
- `bcd4df1e`: Item 0.2 PROVED operationally; exact baseline result record.
- `e486c49e`: compliant Item 1.1 Round 2 freeze.
- `0b32407d`: Item 1.1 PARTIAL; complete event-generic classification and
  exact non-certification evidence.

# Part 0

- The first attempt is technically useful but not protocol-complete. Commit
  `2bb7e5ea` contains the work current when the plan arrived, and the later
  guarded clean build produced 445 Coq objects with zero Admitted, exit 0,
  3,190 seconds, and peak Coq RSS 1,096 MB.
- Exact chronology audit found that Part 1 began before the Item 0.1 commit hook
  finished. Part 1 proof drafting then overlapped the Item 0.2 clean rebuild.
  No contemporaneous Item 0.2 result commit was made. The gate evidence on
  `2bb7e5ea` is also a union of runs, not one post-plan all-green invocation.
- Part 0 restarted in order at
  `research/rounds/2026-09-30-part0-round2-freeze.md`. The file freezes the
  strict Item 0.1 commit and the exact full-gate and isolated-rebuild surface
  for Item 0.2.
- Item 0.1 Round 2 is PROVED operationally at
  `5d1245e6dd0af40cf56b831a0b06a91adda383a6`. Its strict hook passed 1,157
  tests and Inquisitor, the commit has exactly the frozen two-path diff, the
  stash ref is unchanged, and the post-commit worktree was clean.
- Item 0.2 Round 2 is PROVED operationally at
  `bcd4df1eed79ea3c17a2a68c0b0028cf4a248c9d`. Every frozen check has a
  successful recorded execution. The isolated export compiled 446 of 446
  frozen Coq sources with zero `Admitted.` commands in 3,091.7 guard seconds
  at 1,095 MB peak Coq RSS. The first external-runner attempt failed before
  compilation because a multiline `find` expression lacked shell
  continuations; that failure and remedy remain disclosed in the result.
- Three independent final reads passed the evidence, R6, and protocol review.
  The strict result preflight passed 1,157 tests and Inquisitor in 359.6
  seconds at 1,040 MB peak Coq RSS. The result commit hook passed 1,157 tests
  and Inquisitor in 355.5 seconds at 1,040 MB peak Coq RSS. Its diff is exactly
  `INQUISITOR_REPORT.md`, `artifacts/vacuity_audit.json`, and
  `research/rounds/2026-09-30-part0-round2-results.md`.
- Result record SHA-256:
  `c91f7c6541267e437829bf0981b673757025126cc7a6d0afa8a2f2051a776527`.
  Preflight log SHA-256:
  `5f55a3f72e9b9283eac594cc586f88d9ec94f7e99055b593749087d73c641a5e`.
  Result commit-hook log SHA-256:
  `2ca59aef3b6ce26859cd3c097a2cd06ccdefa62105ef49d41d7610d1a257354a`.
- Part 0 wrong predictions: none. The first rebuild-runner failure was a
  mechanical failed attempt, not a changed outcome prediction.
- Keep stash object `9641ba231bf2e9dcc95d0182fbb4cc6ce4eaff53`
  quarantined. Do not restore it wholesale. Later items may recover individual
  ideas only after their new compliant freezes.
- For Items 0.1 and 0.2 only, PROVED is interpreted operationally as concrete
  Git and command evidence because the items are imperatives, not mathematical
  propositions. Do not introduce a vacuous Coq theorem to mimic repository
  state. No theorem item receives this exception.

# Quarantined Part 1 work

The stash-only sources are:

- `coq/kernel/foundation/EventSwap.v`
- `coq/kernel/nfi/EventGenericInstances.v`
- `docs/event_genericity.tsv`
- `research/rounds/2026-09-30-part1-results.md`
- `tests/test_event_genericity.py`
- their registered project/manifest entries, generated Coq outputs, receipts,
  proof DAG, PDFs, and publication count changes.

Current generated evidence:

- Assumption receipt: 13,133 statements across 448 files; 5,789 globally
  closed; 7,344 use only standard-library assumptions; zero project-local or
  third-party axiom findings.
- Vacuity: 805/805 clean, exit 0, 807.6 seconds, peak Coq RSS 1,441 MB.
- The two result sources compiled individually.
- `INQUISITOR_REPORT.md`, the verification receipt, strict pytest, prose,
  meaning, and citation gates are not current for the result tree.

# Part 1 protocol and correctness findings

The `a9c8270e` freeze does not satisfy R1 chronology. Claude drafted and
compiled Part 1 proofs around 04:42 and 04:43 UTC; the freeze commit completed
at 04:52. Preserve the commit and its files, but never describe it as successful
preregistration. The mathematical statements and proofs may still be valid.

The current item 1.1 completion claim is false:

- The freeze lists 22 generic theorems.
- Four have discharged door theorems and sixteen appear as partial
  applications. That covers 20.
- `tests/test_event_genericity.py` deliberately exempts two while the source,
  result record, and monograph claim all 22.
- `honest_erasure_accounting_implies_a2` is genuinely generic and needs a
  concrete door erasure-accounting instance.
- `thiele_represents_simulating_cert_system` requires its event to reflect into
  VM `vm_certified` and concludes VM certification. Its G classification is
  suspect and needs a statement-level reclassification.
- Open premises are conditional applications. Under R4 they are not proved
  concrete instances.

The 100-theorem claim ledger is not a defensible meaning of "main theorem cited
anywhere." The compliant Item 1.1 Round 2 freeze uses the literal tracked
human-facing documentation surface plus a pinned digest of the external release
draft. It contains 39 sources, 1,143 proof occurrences, 4,066 nonproof
occurrences, and 472 valid full proof identities. Thirteen descriptive LaTeX
theorem labels have explicit proof or aggregate bindings; resolving them added
seven identities that the earlier 465-identity code-span scan missed. The three
stale alleged proof names `pyexec_preserves_cert_addr`, `info_bits_correct`, and
`single_op_mu` were deleted with corrected README counts before the freeze.

The new inventory must be occurrence-typed rather than string-presence based.
It must record source and parser hashes, path, line, raw spelling, declaration
kind, resolved logical identity, ambiguity binding, and every excluded
non-proof token. It must fail on an unknown theorem-context token, ambiguous
occurrence, source drift, or any difference between the classification rows
and the frozen universe. The old test's `if not matches: continue` behavior and
its Definition-name escape are forbidden acceptance paths.

The least distortive stale-reference repair is deletion with corrected counts,
not arbitrary replacement. In `coq/nofi/README.md`, retain `Certified_spec`
and `trace_run_mu_monotone`, then use `(+2 more)`. In
`coq/thermodynamic/README.md`, retain `num_states_pos` and `fan_in_pos`, then
use `(+15 more)` for `LandauerDerived.v`; retain `mu_nonnegative` and
`mu_additive`, then use `(+12 more)` for `ThermodynamicBridge.v`. Substituting
new theorem names would change the valid identity universe from 465 to 468.
The post-repair scan must still determine the count rather than force it.

The external release draft is
`/home/codespace/.cache/thiele-guard/release/v3.4.0-release-notes.md`, SHA-256
`587ff9131c86d128d2eb3349c866894c382590964017495a516086bea1ac4182`.
It currently adds no new theorem identity, but a dated immutable copy must be
included as freeze input before claiming that release notes are in scope.

Item 1.4 is unfinished. Claude began the line-by-line document pass, then the
reader tasks were cut off by the session limit. The README, monograph, math
specification, THIELE_MACHINE, CITATION, and external release notes have not all
received a completed manual R10 pass on the current tree. Item 1.5 was checked
informally: Chapter 26 remains in the open part and is labeled a conjecture.

The current result file and prose must not be committed until the 22-versus-20
gap, classification, R4 labels, and full document pass are corrected.

# Part 2 contamination warning

The files under `/home/codespace/.cache/thiele-guard/drafts/p2/` are scratch
only. Claude drafted proofs before Part 1 closed and before a Part 2 freeze
commit. This violates R1 and item order. Do not install those files as a frozen
round or as results.

The probabilistic scratch definition also admits the empty relation, making
its uniqueness statement vacuous, never constrains positive weights, and does
not use `pm_mu` in its claimed schedule equivalence. Part 2 must be designed
again after Part 1 closes. The strengthened probabilistic relation needs
nonempty/initial coverage, successor matching, record agreement, and a real
ledger or schedule condition.

# Item 1.1 Round 2 freeze

- Compliant freeze commit: `e486c49eb275c9e7d49d8f257d8afe845d9c770e`.
- Parent: `bcd4df1eed79ea3c17a2a68c0b0028cf4a248c9d`.
- Frozen predictions: G 49, C 55, I 28, M 67, N 273.
- Four proof identities remain inside functor bodies and require concrete
  functor instances; none is exempted.
- Extraction tests: 6 passed. Full commit hook: 1,163 tests passed,
  Inquisitor OK, guard exit 0, 365.7 seconds, peak Coq RSS 1,041 MB.
- Commit-hook log SHA-256:
  `9d96f8aa656aa296e3bfd97930fdc19ae81e793ca883d13f6595f8afab741b6b`.
- Worktree is clean after the commit. No Item 1.1 semantic acceptance test or
  proof was attempted before the freeze.

# Item 1.1 Round 2 result

- Result commit: `0b32407da22ff923364c19f472dd85d30a2fbac6`.
- Outcome: PARTIAL, not PROVED.
- Frozen claim surface: 39 sources, 1,143 proof occurrences, 4,066 nonproof
  occurrences, and 472 distinct proof identities. Exact classes are G 49,
  C 55, I 28, M 67, N 273. No class prediction was contradicted.
- Of the 49 G identities, 35 have CLOSED Coq specializations to concrete
  non-certification events and 14 are PARTIAL with pricing, distribution,
  physical, compression, or blind-window premises explicit.
- The concrete witnesses include a two-state door-opening record, a distinct
  three-state saturating meter, a toggle/revocation model, record and history
  latches, and a VM program-counter event.
- The No Free Insight functor has a closed concrete door instance. The three
  Mu Chaitin functor-body identities remain conditional on
  `CERT_PRICING_POLICY`. The current VM schedule refutes that global field via
  a zero-cost `MORPH_ASSERT` carrying a positive payload. Three genuine
  strategies are recorded in the result.
- The post-implementation proof-occurrence rows remain byte-identical to the
  frozen 1,143 rows. The live full occurrence verifier is intentionally
  reported as drifted: four publication hashes changed when current receipt
  numbers were installed, and 51 nonproof rows gained declaration annotations
  from required interface fields `S` and `mu`. This independently prevents a
  PROVED outcome; frozen inputs remain unedited.
- TDD red was captured externally before evidence existed. The unchanged
  semantic test then passed. The final strict suite passed 1,165 tests.
- Final full vacuity: 852/852 OK, zero vacuous or error results, 390.7 guard
  seconds, 1,453 MB peak Coq RSS.
- Final assumption receipt: 13,177 aligned queries across 447 files, 5,824
  globally closed, 7,353 using only standard-library axioms, zero project or
  third-party findings. It completed in 49.8 seconds at 642 MB peak Coq RSS.
- Routine assumption receipts must use the repository persistent
  content-addressed cache. The final record reused 426 exact-hash groups and
  executed the one changed group. Never pass a new empty
  `THIELE_ASSUMPTION_WORK_DIR` for ordinary item closure. A cold cache is only
  for an explicit final or forensic requirement.
- Final standalone Inquisitor: 461 files, zero HIGH/MEDIUM/LOW findings. The
  strict commit hook passed 1,165 tests and Inquisitor in 495.3 seconds at
  1,045 MB peak Coq RSS.
- Result record SHA-256:
  `0f56e29c33d6743dd2b4c85fa03968562b4fc471aa2336480f5418924965a44c`.
  Commit-hook log SHA-256:
  `a4f2d8d5d72ff6bbca8b09889f0c68221bb22891b20337ff5eb007fcafdf2586`.
- The worktree is clean. Preserved stash object
  `9641ba231bf2e9dcc95d0182fbb4cc6ce4eaff53` remains unchanged and must not be
  restored wholesale.

# Exact next sequence

1. Confirm the worktree is clean and push through `d5cb4e7e` to
   `origin/work/research-plan`.
2. Begin Part 2 Item 2.1 only. Add and observe the freeze acceptance test red.
3. Freeze the exact multi-valued record definitions, decomposition statement,
   prediction, success/failure rules, and three BLOCKED strategies in a dated
   file and commit that freeze through the full gate.
4. Only after the freeze commit, add and observe the semantic test red. Then
   prove or refute the exact statement, complete R6 including an independent
   adversarial read, run all gates, and commit the result.
5. Continue to Item 2.2 only after Item 2.1 has one allowed final outcome.
6. Complete the manual item 1.4 pass across all six requested documents and the
   external release notes. Run fresh independent adversarial reads. Confirm
   item 1.5 remains open and secondary.
7. Run all current-tree gates. At minimum: guarded serial Coq build if sources
   changed, full vacuity for changed Coq, fresh receipt, strict pytest,
   Inquisitor, prose/meaning/citation audits, assumption consistency, PDFs, and
   generated artifact checks.
8. Commit honest per-item results. Do not claim compliant preregistration for
   the old Part 1 work.
9. Update this memory and the external tracker with each hash and item
    outcome. Then begin Part 2 with new freezes, one item at a time.

# 2026-09-30 Item 1.2 freeze checkpoint

- HEAD is `282e30e8` on `work/research-plan`; the worktree was clean after the
  commit.
- The freeze binds all 55 Item 1.1 class-C identities to exact propositions in
  `coq/kernel/foundation/EventGeneralizationTargets.v` and exact translations
  in `research/rounds/2026-09-30-part1-item1.2-round1-targets.tsv`.
- Predictions: 21 PROVED, 34 REFUTED, 0 BLOCKED.
- The definitions-only target file compiles. Freeze tests pass 3/3. The strict
  hook passed 1,168 tests and Inquisitor. The assumption receipt is coherent at
  13,177 queries across 448 files.
- The first commit attempt correctly failed on a stale receipt fingerprint.
  Persistent-cache regeneration then completed in 32.1 seconds and the retry
  passed. Never create an empty ordinary receipt cache.
- Immediate next action: create the semantic result/evidence test and observe
  it fail because no result file exists, then implement shared non-certification
  event witnesses and the 55 closed proofs or refutations.

# Remaining plan

After Part 1, Parts 2 through 8 remain open under the expanded acceptance
criteria: multi-valued, revocable, probabilistic, and cross-base records; a VM
or real-fragment recursion theorem; pricing and physics questions; real RFC
9162, Necula PCC, concrete RAM/Janus, TPM authenticity, and full cost-framework
models; the twelve-event pointer study; the sourced field survey and ranked
outside-framework candidate loop; then final exact documentation, every gate,
a fresh rebuild, and one final commit. Stop before merge or tag.

# 2026-10-01 continuation handoff

- Devon explicitly replaced the slow per-item commit cadence with Part-level
  batching. Keep TDD, immutable dated freezes, exact R2/R4 outcomes, R6, and
  all full gates at each Part boundary. Do not stop after minor work.
- Part 2 completed at `dc43689f`; see the four Part 2 result files for exact
  mixed outcomes and blockers. Its full gate passed 1,207 tests and Inquisitor.
- Part 3 completed at `2438ae9c`. Exact VM guest recursion is BLOCKED because
  no verified runtime evaluator consumes a computed guest-program code; VM
  guest Rice is PROVED independently through `rice_prog`. Full gate: 1,210
  tests, 13,353 queries over 461 files, no project/third-party axioms,
  Inquisitor OK.
- Part 4 completed and was pushed at `fd953dc1`. The final batch contains
  `PricingPhysicsTarget.v`, `PricingPhysicsAudit.v`, four preserved freeze
  rounds, the result report, and `tests/test_part4_pricing_physics.py`.
  Independent adversarial verdict: PASS on 4.1-4.4. Final gate: 1,213 tests,
  13,359 queries across 463 files, no project/third-party axioms, vacuity clean,
  Inquisitor OK.
- Expected Part 4 outcomes: 4.1 PROVED BUT KNOWN; 4.2 PARTIAL because logical
  merge does not derive economic/cryptographic/physical payment; 4.3 PARTIAL
  because μ has no intrinsic joule scale and Landauer calibration is explicit;
  4.4 PROVED BUT KNOWN within the present model, with no independent physical
  prediction beyond Landauer.
- Next: begin Part 5.1 from RFC 9162 Sections 2.1.1-2.1.4. Existing
  `TransparencyLog.v` explicitly lacks Merkle internals and cannot close the
  item. Do not revive the per-item commit cadence.
