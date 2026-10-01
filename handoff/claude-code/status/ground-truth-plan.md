# Ground-truth plan tracker (outside repo)

Source: Devon's pasted "COMPLETE PLAN: THE THIELE MACHINE, TO GROUND TRUTH" (2026-09-30).
Rules R1-R12. Stop only before merge/tag. Commit after every item (R9).
Freeze records: research/rounds/<date>-<item>.md + Coq definition files, committed before proofs.

## Calls made (for reports)
- C1: Paste treated as Devon's instruction; R9 supersedes "no more committing".
- C2: R1 freeze records live in research/rounds/ (dated); published docs stay ground truth.
- C3: Full vacuity sweep rerun whenever any Coq file changes; doc-only commits reuse the prior sweep only when no proof input changed.
- C4: The 100-theorem monograph claim ledger is rejected as the Item 1.1 universe. It omits proof citations even inside the ledger section. The corrected round uses the literal tracked human-facing documentation surface plus a pinned digest of the external release draft: 472 valid proof identities after occurrence-level typing and explicit resolution of descriptive theorem labels. Three stale alleged theorem references were repaired before the universe froze.
- C5: The freeze in a9c8270e is preserved as history but is not claimed as compliant preregistration. Proof drafts existed before that commit completed.
- C6: Part 2 scratch files are quarantined. They were proved before a Part 2 freeze and include a vacuous probabilistic relation.
- C7: The old Claude process pair from 2026-09-29 was terminated by exact PID on 2026-09-30. The current pair was left intact.
- C8: The first Part 0 attempt is retained as technical evidence but is not treated as protocol-complete. Part 1 began before the Item 0.1 hook finished, and Part 1 proof drafting overlapped the Item 0.2 rebuild.
- C9: Part 0 Round 2 is complete in order. Commit `5d1245e6` closes Item 0.1 operationally. Commit `bcd4df1e` closes Item 0.2 operationally with the exact full-gate and isolated-rebuild record in `research/rounds/2026-09-30-part0-round2-results.md`.
- C10: For the two operational Part 0 imperatives only, PROVED means reproducible Git and command evidence. No hollow Coq proposition about repository state will be introduced. This exception does not apply to theorem items.
- C11: The first Round 2 rebuild runner failed before compilation because a multiline `find` expression lacked shell continuations. The failure is retained. The unchanged frozen input passed on attempt 2: 446/446 source objects, zero Admitted, 3,091.7 guard seconds, and 1,095 MB peak Coq RSS.
- C12: The three stale Item 1.1 citation tokens were deleted with corrected `(+N more)` counts rather than replaced by arbitrary theorem names. Replacement would have silently changed the proof universe.
- C13: Thirteen descriptive LaTeX theorem labels are explicit proof or aggregate bindings. Resolving them added seven proof identities that the code-span-only scan missed, producing the frozen total of 472 rather than 465.
- C14: Item 1.1 is PARTIAL. All 472 proof identities are classified and all 49 G identities have exact non-certification Coq witnesses, but 14 G witnesses retain explicit premises, three non-G Mu Chaitin functor bodies remain conditional on a global pricing policy refuted by the current VM schedule, and the live nonproof/source inventory does not remain byte-identical to the freeze.
- C15: Routine assumption receipts use `build/probe/assumption-cache`. Reuse is keyed by exact `.vo`, query, Coq-version, and load-path hashes. Never create a new empty `THIELE_ASSUMPTION_WORK_DIR` for ordinary closure. The Item 1.1 final receipt reused 426 unchanged groups, executed one changed group, and assembled all 13,177 aligned results in 49.8 seconds.
- C16: Item 1.2 Round 1 freezes all 55 class-C identities as exact Coq propositions. Predictions are 21 PROVED and 34 REFUTED. A counterexample is an accepted result, not a weakened claim.
- C17: The strict hook's full Kami and repository build follows R8. Item-development iterations use guarded targeted builds; no gate is bypassed. The Item 1.2 freeze receipt used the persistent cache and completed in 32.1 seconds.
- C18: Item 1.2 closes 19 PROVED and 36 REFUTED, not the frozen prediction of 21 and 34. The two wrong predictions are `generalized_billed_schedule_equivalence` and `generalized_surcharged_schedule_equivalence`.
- C19: Item 1.3's universal swap claim is REFUTED by a fixed-register-width zero-cost `PNEW [] 0` graph-allocation event. Certification still satisfies the frozen five-result bundle.
- C20: Item 1.4 audited all 8,156 physical lines in the six frozen documents and made 41 exact corrections. The result is PROVED at `3f745351`; the strict result hook passed 1,181 tests and Inquisitor.
- C21: Item 1.5 Round 1 is REFUTED because frozen `README.md:600` called the general pointer criterion a theorem. Round 2 freezes the correction separately and is PROVED. Round 1 remains immutable and REFUTED.
- C22: Part 1 is closed. The next numbered work is Part 2 Item 2.1. Quarantined pre-freeze Part 2 drafts remain unusable as freezes or results.

## Repository status at 2026-10-01 checkpoint

- Branch: work/research-plan
- HEAD: `d5cb4e7e`
- Worktree: clean, 0 staged, 0 conflicts.
- Preserved Part 1 stash: `9641ba231bf2e9dcc95d0182fbb4cc6ce4eaff53`.
- Current receipt: 13,318 queries across 450 files; coherent snapshot with zero receipt inconsistency.
- Current vacuity artifact: 852 total, 852 ok, 0 vacuous, 0 errors.
- Item 0.2 result-hook evidence: 1,157 tests, Inquisitor OK, 355.5 seconds, sampled peak Coq RSS 1,040 MB.

## Status
| Item | Freeze commit | Outcome | Result commit | R6 a-e / remaining |
|---|---|---|---|---|
| 0.1 | 5d1245e6 | PROVED operationally | 5d1245e6 | Exact parent/path/stash/clean-tree checks pass; strict hook: 1,157 passed, Inquisitor OK, sampled peak Coq RSS 1,056 MB. |
| 0.2 | 5d1245e6 | PROVED operationally | bcd4df1e | All frozen checks have successful executions; isolated rebuild 446/446, zero Admitted; R6 independent read PASS; exact three-path strict-hook commit. |
| 1.1 | e486c49e, compliant Round 2 | PARTIAL | 0b32407d | 472 exact classes: G49/C55/I28/M67/N273. G evidence: 35 CLOSED, 14 PARTIAL. Three Mu Chaitin functor bodies remain conditional; live source/nonproof byte identity also fails and is disclosed. R6 complete; 1,165 tests, 852/852 vacuity, zero project axioms, Inquisitor OK. |
| 1.2 | 282e30e8, compliant Round 1 | 19 PROVED, 36 REFUTED | 1b6e8c5b | All 55 source identities have exact closed wrappers; two predictions were wrong; full R6 evidence is committed. |
| 1.3 | 37b33024, compliant Round 1 | REFUTED universal swap; certification sanity PROVED | 66feb214 | Fixed-width graph-allocation counterevent; closed Coq results; R6 adversarial read corrected the report wording. |
| 1.4 | adfbeac0, compliant Round 1 | PROVED | 3f745351 | 8,156/8,156 line audit, 41 corrections, independent final PASS, 1,181 tests and Inquisitor. |
| 1.5 | 4888677e Round 1; 61d682a2 Round 2 | Round 1 REFUTED; Round 2 PROVED | 10aeb40d; d5cb4e7e | Frozen README overclaim preserved as the Round 1 counterexample; corrected 40/40 ledger and independent PASS in Round 2; 1,193 tests and Inquisitor. |
| 2.1-2.4 | none valid | OPEN | none | External drafts are contaminated and must not be reused as freezes/results. |
| 3.1 | none | OPEN | none | Existing L theorem does not close the VM or real-fragment target. |
| 4.1-4.4 | none under this plan | OPEN | none | Earlier merge/permanence results are inputs, not acceptance closure. |
| 5.1-5.5 | none under this plan | OPEN | none | Real CT, PCC, concrete machines, TPM authenticity, and full framework embeddings remain. |
| 6.1-6.4 | none | OPEN | none | Precise proliferation and 12-event real-system test remain. |
| 7.1-7.7 | none | OPEN | none | Survey, ranked candidates, and proof loop remain. |
| 8.1-8.4 | none | OPEN | none | Final documents, gates, rebuild, commit, and report remain. |

## Part 0 R12 report

- Outcomes: Item 0.1 PROVED operationally at `5d1245e6`; Item 0.2 PROVED operationally at `bcd4df1e`.
- Evidence: result record SHA-256 `c91f7c6541267e437829bf0981b673757025126cc7a6d0afa8a2f2051a776527`; strict result-hook log SHA-256 `2ca59aef3b6ce26859cd3c097a2cd06ccdefa62105ef49d41d7610d1a257354a`.
- Calls: use operational PROVED only for the two Part 0 imperatives; retain the first attempt as evidence; quarantine the Part 1 stash; retain both rebuild attempts; distinguish guard summaries from payload logs.
- Wrong predictions: none. The first rebuild-runner failure was a failed mechanical attempt, not a changed outcome prediction.

## Immediate next actions

1. Push `d5cb4e7e` and its predecessors to `origin/work/research-plan` after confirming the clean tree.
2. Start Part 2 Item 2.1 only. Add a red freeze test, then commit an exact dated freeze before any proof or counterexample work.
3. Define monotone multi-valued records and the exact Round 4 decomposition target without importing the quarantined pre-freeze drafts.
4. After the freeze commit, add the semantic acceptance test, prove or refute the exact statement, complete all five R6 checks including an independent adversarial read, run the full gate, and commit the outcome before Item 2.2.

## 2026-10-01 accelerated continuation

- Process call C23: at Devon's explicit direction, retain TDD, dated immutable
  statement freezes, outcome labels, and all boundary gates, but batch commits
  and full gates at Part boundaries instead of after every minor item.
- Part 2 is complete at `dc43689f`: 2.1 has proved threshold decomposition and
  a refuted single-latch claim; 2.2 proves actual revocation is outside
  permanence and refutes price-transfer; 2.3 refutes probabilistic uniqueness;
  2.4 proves the frozen weak equivalence laws but blocks actual RAM and L
  adapters for exact recorded reasons. The boundary gate passed 1,207 tests,
  13,350 assumption queries over 459 files, zero project/third-party axioms,
  full vacuity, and Inquisitor.
- Part 3 is complete at `2438ae9c`: the exact VM guest recursion theorem is
  BLOCKED after three recorded strategies because actual execution lacks
  runtime evaluation of a computed guest-program code. The guest Rice theorem
  is PROVED independently by the existing concrete `rice_prog` reduction.
  The boundary gate passed 1,210 tests, 13,353 assumption queries over 461
  files, zero project/third-party axioms, full vacuity, and Inquisitor.
- Part 4 completed at `fd953dc1` and is pushed. Outcomes: 4.1 PROVED BUT KNOWN,
  4.2 PARTIAL, 4.3 PARTIAL, and 4.4 PROVED BUT KNOWN. The first 4.4 target was
  rejected by Inquisitor as tautological; immutable round 4 strengthens it to
  the full finite-state logarithmic heat bound, grounds scales in
  `VMState.vm_mu`, and adds entropy-permutation invariance. Final boundary:
  1,213 tests, 13,359 queries over 463 files, zero project/third-party axioms,
  full vacuity, and Inquisitor OK.
- Immediate next action: Part 5.1 from RFC 9162 Sections 2.1.1 through 2.1.4,
  without per-item commits or idle checkpointing.

## Part 1 Item 1.1 R12 report

- Outcome: PARTIAL at commit `0b32407da22ff923364c19f472dd85d30a2fbac6`.
- Exact counts: 39 frozen sources, 1,143 proof occurrences, 4,066 nonproof occurrences, 472 identities; G49/C55/I28/M67/N273; 35 CLOSED G and 14 PARTIAL G.
- Obstruction: the current VM schedule refutes the Mu Chaitin functor's global payload-pricing field. Three conditional functor-body wrappers are not concrete unconditional instances.
- Inventory limitation: all frozen proof rows remain identical, but 51 nonproof rows gain `S`/`mu` declaration annotations and four publication hashes change for current receipt numbers. The result does not claim the byte-for-byte freeze success condition.
- Gates: full vacuity 852/852; full receipt 13,177 aligned queries and zero project/third-party findings; strict tests 1,165 passed; Inquisitor 461 files and zero findings; verify, claim, research, RTL, citation, semantic, and publication checks passed.
- Commit hook: 1,165 tests and Inquisitor OK, 495.3 seconds, peak Coq RSS 1,045 MB; log SHA-256 `a4f2d8d5d72ff6bbca8b09889f0c68221bb22891b20337ff5eb007fcafdf2586`.
- Result record SHA-256: `0f56e29c33d6743dd2b4c85fa03968562b4fc471aa2336480f5418924965a44c`.
- Wrong predictions: no class prediction was wrong. The concrete-instance expectation was wrong for three Mu Chaitin bodies, and live byte-for-byte nonproof/source reproduction was wrong.
