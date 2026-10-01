# Research execution status

> Historical tracker for the older 11-item plan. The authoritative current
> plan and status are `/home/codespace/.cache/thiele-guard/ground-truth-plan.md`
> and Claude memory `ground-truth-plan-execution.md`. Do not use old DONE
> labels below to close an item in the 2026-09-30 Ground Truth plan.

User authorization on 2026-09-29: complete the original research plan and its
Phase 1.5 addition, without shortcuts, using TDD. No merge or release requested.

## Required order and evidence

1. Finish the theorem meaning audit and verify the inherited working tree.
2. Commit dated StructuralCore rounds before uniqueness or discrimination tests.
3. Add failing executable contract checks before implementing each result.
4. Preserve failed conjectures and their original definitions.
5. Complete real-spec interpretations and comparisons, not vocabulary aliases.
6. Finish framework embeddings, verifier application, physics and prior-work map.
7. Re-anchor the claims to the actual outcomes; rebuild receipts and publications.
8. Run full verification and save the work on work/research-plan.

## Current evidence

- HEAD remains 8ed7ba74. No research-plan commit yet.
- Full suite excluding the intentionally stale assumption receipt now passes:
  1114 passed, 1 deselected in 110.53 seconds. MasterSummary and RTL freshness
  failures were repaired and independently rechecked.
- New audit regressions: four expected failures, followed by passes after fixes.
- Meaning gate now resolves qualified source identities, wrapped LaTeX, claim
  ledger entries, and theorem names without underscores. Last extension found
  ReceiptTheorem missing; its source statement has now been recorded.
- Citation audits of both LaTeX sources pass after indexing inline constructors
  and classifying TPM2_Quote and the stdlib classic axiom.
- CommitmentBitContract replaces the overclaiming HardnessHypothesis name.
  The main result is commitment_contract_verifier, a construction under an
  exact disclosure contract, not a hardness theorem. Consumers updated.
- Unused equiv_refl deleted, rather than weakening the invariance scanner.
- F3 scalar examples named unit_residual_is_nonzero and pi_times_unit_is_nonzero.
  No VM independence claim is attached to them.
- CostSemanticsComparison currently proves writer identities and a lower-bound
  potential argument only. It does not finish the four framework embeddings.

## Running checks

- Inquisitor: logs/inquisitor-tdd.log. Guarded, serialized build passed.
- Full existing vacuity manifest: logs/vacuity-tdd.log, jobs=1.
- Receipt regeneration is the next baseline operation. Do not change source or
  compiled files during that run. Cache now binds source, compiled, tool and
  completed-batch fingerprints.

### 04:02 UTC update

- Inquisitor now passes with 0 HIGH and 0 MEDIUM after the explicit TPM
  application to V_does_not_factor_through_classical. The quote adapter is
  proved lossless; VM states are truth labels, not physical-cost claims.
  Coq regression was red (missing quote_projection), then green.
- Existing vacuity sweep: 608 theorems, zero positives/errors. Six new research
  files added to the manifest and checked with --merge: 698 total, zero positives.
- Found an actual interrupted-cache bug: new source was saved before Coq ran,
  leaving old answers reusable after interruption. Timestamp evidence on
  501-1000.v (03:57) versus old output (00:21). Stopped affected receipt runs.
  Added failing regressions, then transactional completion records with hashes
  of source, stdout, stderr and count. Legacy batches cannot be reused.
- Selective batch imports now load each queried library and its Coq-resolved
  dependencies instead of all 433 libraries for every batch. Unknown prefixes
  retain all imports. Four red tests then green, including live Coq equivalence.
  Receipt tests plus fingerprint tests: 27 passed.
- The previous receipt attempt was deliberately stopped after tool changes.
  The final baseline run will use jobs=2, the memory guard, and 13027 queries.
  Every prior cache record is invalidated by the script fingerprint.
- Test rebuild path changed from make -j4 to -j1 after a failing command-capture
  regression. Compiler builds remain serialized; query workers are independent.
- Prior-work table added to monograph Section 1 with primary sources and exact
  contribution boundaries. Fixed QIF exact-decoding versus zero-leakage confusion,
  known-state heat-floor wording, and work-witness versus elapsed-effort wording.

## Remaining research obligations

- Phase 0 audit closure; no blanket completion claim from a coverage test.
- Smallest observer-narrowing counterexample: current four-state example is
  valid but no minimum-state theorem is recorded.
  Additional scope issue: observer_narrowing_priced compares |Omega| with
  final knowledge even though seen includes the initial observation. An
  initially nonuniform prior can narrow at the empty trace. Preserve this
  original definition, preregister an incremental target comparing
  knowledge Omega [] s0 to knowledge Omega t s0, then prove the existing
  homogeneous-prior witness also refutes that stronger reading. A three-state
  cycle with observations false,false,true is a candidate minimal example;
  with at most two states, an initially hidden pair exhausts the state space,
  making the observation constant forever. Do not claim minimality until proved.
- Round 1 and round 2 uniqueness, discrimination, and stronger history quotient.
- Actual EVM, CT, TPM, Casper, PCC semantics and explicit interpretation choices.
- Full framework-comparison deliverables, with upper/lower AARA directions clear.
- Explicit V_does_not_factor_through_classical application to the TPM view.
- Physics and eight-entry prior-work map validated against primary sources.
- Final headline, re-anchoring, further extensions, receipts, PDFs, full checks.

## 05:00 UTC continuation checkpoint

- `coq/kernel/foundation/StructuralCoreRound2.v` is registered, compiled and
  still definition-only. It fixes the round-two honest-extension and stronger
  equivalence predicates before any uniqueness or discrimination test.
- The full guarded Coq build passes serialized at a recorded peak of 738 MB.
- Inquisitor passes at 0 HIGH and 0 MEDIUM. The merged vacuity artifact covers
  698 theorems with no positive findings or errors.
- Both citation audits pass. The theorem-meaning gate includes ReceiptTheorem
  and the explicit TPM quote application.
- The next required sequence is: regenerate the assumption receipt, update its
  published counts, rebuild PDFs, run every gate, then commit the dated baseline.
  Only after that commit may uniqueness and discrimination tests be added.
- Three read-only parallel reviews are active for real specifications, framework
  comparisons, and plan completion. They are forbidden to edit or build.
- No merge or release has been authorized.

## External source checkout

Casper upstream is checked out read-only for study at
/tmp/thiele-research-sources.h6bCsg/casper-proofs, commit
d8fe05df57e59909bf5c3392579e66ac1b78dab8. LICENSE.md is NCSA-style.
It needs Coq 8.8, mathcomp 1.7, FCSL PCM, CoqHammer and finmap; current project
uses Coq 8.18 and opam is absent. No dependency installation or port yet.

## Process boundaries

All local edits use apply_patch. No em dashes or correction-history prose in
publications. Keep No Free Insight. Guard every Coq build with time/RSS limits,
memory floor and make -j1. Parallel agents are read-only unless explicitly
assigned an isolated implementation after the baseline commit. Final repo must
not retain a process tracker; this file is deliberately outside the repo.

## 2026-09-29 pre-baseline semantic audit

- A final read-only review found that several valid toy theorems were described
  as deployed protocol, security, or faithful-system results. Red-first audit
  tests now prevent those interpretations from returning.
- Pointer-observable exports now say synthetic labelled Boolean models. They do
  not prove forgery resistance, observer independence, metering, deployment, or
  protocol correspondence.
- Gas, explicit-finalize, report, and carried-claim files now identify
  themselves as abstract wrappers. TPMQuoteGap is a deliberately scoped
  abstraction of Version 185 quote fields with authenticity assumed externally.
- The verifier theorem is stated with its supplied collision and explanation
  premises. Full-state, exact commitment-bit, and reported-response transcripts
  are three sufficient interfaces, not an exhaustive trichotomy.
- Round 1's weak existential MM2 property is now named
  `halting_problem_coverage`, not Turing equivalence. The unbounded VM has no
  unsupported hardware-faithful word-width claim.
- `observer_narrowing_can_be_free` records the existential result actually
  proved: one admissible compression price assigns zero to the injective
  measurement. Compression pricing is a lower bound and may overcharge it.
- The ideal plan order was not historically met across all work: framework and
  research modules had already been authored before the first commit. The next
  commit is therefore a late baseline snapshot, but both structural rounds are
  still definition-only and no uniqueness or discrimination test exists yet.
- Full serialized Coq rebuild after these repairs passed in 74.0 seconds at a
  peak Coq RSS of 738 MB. The 25 targeted audit/meaning tests pass.
- Next: regenerate the full assumption receipt and derived publications, pass
  every gate, commit the dated baseline, and only then add uniqueness or
  discrimination tests.

## 2026-09-29 pause and Claude-resume checkpoint

The user asked Codex to stop active work and make the state easy for Claude to
resume. All Codex-started processes and read-only subagents have been stopped.
There is no background Coq, guard, or vacuity process.

### Exact repository state

- Workspace `/workspaces/The-Thiele-Machine`
- Branch `work/research-plan`
- HEAD `8ed7ba74`
- No files are staged and no research commit exists yet.
- The dirty tree is intentional. `git diff --stat` currently reports 306
  tracked files changed; the new `.v`, theorem-meaning, and regression-test
  files are untracked. Preserve all of it. Never run `git clean`, reset, or a
  checkout that discards this work.
- Both structural rounds remain definition-only. No uniqueness or
  discrimination test/result has been authored. Preserve that until the late
  baseline commit succeeds.

### Evidence completed at this pause

- Full assumption receipt: exit 0, 3,219.1 seconds, peak Coq RSS 1,247 MB.
  Artifact timestamp: `2026-09-29T05:56:07.829124+00:00`.
- Receipt totals: 13,028 queries over 433 files; 5,692 globally closed; 7,336
  stdlib-dependent; zero project-local/third-party axioms. The five constants
  and their exact use counts are in
  `artifacts/print_assumptions_all_proofs.json`.
- Consistency checker passes. The generator inventory contains 13,027
  addressable declarations and the receipt contains one additional generated
  probe query; the authoritative published receipt total is 13,028.
- Receipt log:
  `/home/codespace/.cache/thiele-guard/logs/receipt-final-baseline.log`.
- Completed receipt inputs/cache were preserved at
  `/home/codespace/.cache/thiele-guard/receipt-work-archives/completed-prebaseline-20260929`.
  This explains why the user's old IDE tabs under
  `build/probe/receipt-work/` no longer resolve.
- Published counts corrected in README, CITATION, Zenodo metadata,
  THIELE_MACHINE, and monograph source. No stale public-source count remains.
- Publication build passed: 196-page monograph and 69-page math spec, with PDF
  and plaintext outputs regenerated.
- Citation resolution audit passed for both LaTeX sources. Semantic audit had
  two advisory findings only: explicitly mention iff near
  `vm_structural_shortcut_undecidable_encoded` if polishing prose, and retain
  the documented alias status of `level_k_verification_floor`.
- Proof dependency, MasterSummary, RTL text-transform, and RTL pipeline
  generators completed successfully after the scope/name corrections.
- Earlier final-scope full Coq build passed in 74.0 seconds at 738 MB peak, and
  the targeted audit/meaning suite passed 25 tests.

### Interrupted operation

A new full vacuity sweep was in progress when the user paused. Codex sent
interrupt to the guard, then explicitly terminated the orphaned process group.
No process remains. The in-progress run did not overwrite the audit. The
current `artifacts/vacuity_audit.json` is the earlier valid result with 698
total, 698 ok, and zero vacuous/error findings. It must nevertheless be rerun
against the final baseline tree.

### Resume commands before the baseline commit

Run these without editing Coq sources concurrently:

1. `python3 /home/codespace/.cache/thiele-guard/run_guarded.py --seconds 3600 --coq-seconds 900 --log /home/codespace/.cache/thiele-guard/logs/vacuity-prebaseline-resume.log -- python3 scripts/vacuity_gate.py --manifest scripts/vacuity_targets.json --jobs 1 --output artifacts/vacuity_audit.json`
2. Guarded `python3 scripts/inquisitor.py --report INQUISITOR_REPORT.md`; require
   zero HIGH and zero MEDIUM.
3. `python3 -m pytest tests/ -q --tb=short --strict-backends -n 0`.
4. `python3 scripts/generate_verification_receipt.py` to refresh the tracked
   verification receipt after the renamed pointer theorem and latest gates.
5. `python3 scripts/check_assumption_consistency.py`, both monograph citation
   audits, `python3 scripts/generate_rtl_pipeline_manifest.py --check`, and
   `python3 scripts/audit_rtl_text_transforms.py --check`.
6. If any publication source changes, rerun
   `bash monograph/build_monograph.sh` and the citation audits.
7. Remove no evidence. Verify no repository-local temp directory exists, stage
   every intended change, and commit. The modified strict hook requires a fully
   staged clean worktree, performs serialized builds, tests, and generators,
   and must run without bypass. Suggested honest message:
   `research: freeze late preregistered baseline`.
8. Update both handoff files with the resulting commit hash. Only after that
   may a red uniqueness or discrimination test be introduced.

### Work after the baseline

The leading structural counterexample is an escalating CPU-time surcharge
wrapper around `ThieleCore`. It should preserve Round 1 halting coverage and
Round 2 projection/honest-extension fields while defeating step-cost
bisimulation. Keep the original conjectures visible and prove their negations
if the counterexample works. Then evaluate RAM, a Janus-style reversible
machine, and CPU-time billing against the fixed criteria.

For observer narrowing, preserve the original four-state theorem. Add a new
dated incremental definition comparing initial knowledge with final knowledge,
then prove the three-state false/false/true cycle witness and the two-state
impossibility under the exact homogeneous-hidden-pair premises.

Actual-spec and framework work is still substantive, not editorial. Use pinned
primary sources for KEVM/EVM, RFC 9162, TPM v185, Casper FFG, and Necula PCC;
record negative mappings honestly. Complete graded writer/effect, scoped
Danner-Licata, AARA upper-potential versus A2 lower-potential, and linear-token
comparisons. Finish re-anchoring, real-protocol verifier analysis, primary-source
physics/prior-work validation, decision summary, full receipt regeneration,
publication rebuild, and all final gates. No merge or release is authorized.

## Baseline committed, 2026-09-29 14:42 UTC

- Commit 34971852cf2e2e5a7892e5fb85b18740ce44af0a on work/research-plan, "research: freeze late preregistered baseline". Passed the strict pre-commit hook under the guard (1205 s, peak Coq RSS 1476 MB): serial vendor + Coq rebuild, extraction, vacuity, full suite (1130 passed).
- Frozen definitions in that commit: StructuralCore.v sha256 fd57d8602957cc0b85f3cc7c7c4cd3f304bbc39abd5882804f5477e4ded2fca7; StructuralCoreRound2.v sha256 95b6644d94e519119184b2460328b2472a5b94b7501c535008765a74b74be9ee. Both definition-only; no uniqueness or discrimination test or theorem exists at this commit.
- Next (in order): red uniqueness contract test (CPU-time surcharge wrapper as leading escape) for rounds 1 and 2; discrimination set (RAM, Janus-style reversible, CPU billing); item 4 incremental observer definition + 3-state witness + 2-state impossibility; item 1 audit closure incl. logged drifts (46 vs 47 opcodes in receipt claim and parity/cross-layer docstrings; ocaml_extraction_faithful called "axiom" in OCamlExtractionBridge.v comments though it is a Theorem); items 6, 8, 9, 10, 11, 14, decision summary. Casper FFG route (port Coq 8.8 proofs vs paper model) needs Devon's decision. No merge or release without asking.
## 2026-10-01 final Codex handoff

Devon asked Codex to stop and hand the proof to Claude for continuation and
home-PC pickup. The exact pushed snapshot is commit
`25f55ae01605531f3ec818c64d0a82315106ef0c` on remote branch
`handoff/native-recursion-2026-10-01`. Read the tracked file
`research/rounds/2026-10-01-part3-item3.1-round3-handoff.md` before editing.
The native theorem remains unproved and the targeted TDD state is intentionally
one failure and one pass. `VMMMAReduction.vo` builds and its seven printed
declarations are closed. Do not merge, tag, release, weaken the theorem, use
host dispatch, or use fixed-width register packing.
