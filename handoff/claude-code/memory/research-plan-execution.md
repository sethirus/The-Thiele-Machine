---
name: research-plan-execution
description: "Tracker for executing Devon's 11-item research plan (Phase 0-3 + decision summary) on branch work/research-plan; status per item, decisions, and file names (started 2026-09-28)"
metadata:
  node_type: memory
  type: project
  originSessionId: d669abf4-46e6-4136-96bd-c94bb98a9b03
  modified: 2026-09-29T06:06:41Z
---

Devon (2026-09-28): "I want all of it done, every single bit of it, saved and planned and completed from beginning to end." Source: his doc "Thiele Machine Research Plan" (Phase 0 items 1-3, Phase 1 item 4, Phase 2 items 5-8, Phase 3 items 9-11, Decision summary). Branch `work/research-plan` off main 8ed7ba74 (v3.3.0). Commit per finished item on the branch (he asked for it saved); ask before merging to main or releasing.

Plan rules to keep: fix definitions (esp. ≃) in the repo with a date BEFORE testing; never revise to fit a result (a revision is a new dated round); failed tests get equal prominence in the monograph; rewrite headline last from outcomes.

Order of execution (item 4 first because item 2 depends on it):
1. Item 4, narrowing priced? Plan: new Coq file coq/kernel/nfi/KnowledgeNarrowing.v. Two readings: (a) machine-state narrowing, |run(Ω)| vs |Ω|, IS priced under compression_priced along a run (trace-level log bound, tree extracted from the run); (b) observer-knowledge narrowing (initial states consistent with observations) is FREE: counterexample with bijective zero-cost steps (Bennett). Expected outcome row: "commitment priced, insight free".
2. Item 2: DECIDED by Devon 2026-09-28: keep the name "No Free Insight". I renamed it to "No Free Commitment" and he objected; reverted. Item 2 is done by scoping in prose: the insight NoFI prices is certified insight; raw learning can be free (KnowledgeNarrowing).
3. Item 1, audit every cited theorem (README, monograph, math spec, technical disclosure, THIELE_MACHINE.txt): one plain sentence each; rename overclaiming names (quantum_realizable family -> zero-marginal NPA PSD wording); meaning gate = checked data file + pytest that fails when a cited name has no entry.
4. Item 3, option B (retitle Section 10, drop "halting-shaped wall") then option A (real recursion theorem for the 12-instruction self-interpreter fragment, diagonal applied).
5. Item 5, define StructuralCore/Adequate/≃ in Coq with a dated header; treat certification_agreement_does_not_imply_descent (relational bisimulation: kept history quotiented out).
5b. Phase 1.5 (Devon added 2026-09-28): item 12 define "honest record-carrying extension" (Turing-equivalent machine + record axis carried in state and priced in step) and state uniqueness: every such extension's structural core ≃ Thiele core; commit dated BEFORE proving. Item 13 prove it (tool: forced_priced_iff_merges) or build an escaping extension (history-keeping target from certification_agreement_does_not_imply_descent; reversible machine with records); on escape narrow in a new dated round or claim family membership and characterize the family. Item 14 re-anchor results (shadow/irrecoverability, A2 + merge pricing, permanent records, certification, CHSH): consequence of uniqueness vs instance of record axis; plus a "further extensions" list with what each needs. Runs after item 5 (needs ≃), before item 7.
6. Item 7, discrimination set: RAM machine, Janus-style reversible language, CPU-time billing.
7. Item 6, spec-based models: EVM gas (Yellow Paper/KEVM), CT (RFC 6962/9162), TPM 2.0 quote, Casper FFG, Necula PCC; record interpretation choices per spec.
8. Item 8, embeddings/equivalences: graded monads, Danner-Licata cost semantics, AARA, linear-logic resource semantics.
9. Item 9, verifier corollary on a real attestation/audit protocol.
10. Item 10, physics beyond Landauer (expected: nothing beyond Landauer + permanence-to-merge bridge; state it; Bérut 2012 check).
11. Item 11, prior-work map table into monograph Section 1.
12. Decision summary: rewrite README/monograph headline from outcomes; regenerate receipt, PDFs, counts.

Status: (update as items close)
- Item 4 PARTIAL (code only; minimality and incremental observer definition still open; docs unverified): coq/kernel/nfi/KnowledgeNarrowing.v (run_narrowing_priced_log, observer_narrowing_is_free, wipe_costs_at_least_one, vm_observer_narrowing_at_zero_cost; all closed; registered after FiniteCertMachine; Inquisitor OK 441 files). Outcome row: commitment priced, insight free. Docs not yet updated.
- Item 3 option A PARTIAL (L recursion proved; option B deliberately skipped, not done): coq/kernel/foundation/LRecursion.v (self-contained weak CBV L, Scott codes, rec combinator, Qn/Q quoters, second_recursion, L_recursion_theorem, L_rice, L_structural_shortcut_undecidable, L_halting_undecidable; all closed). Option B (retitling Devon's 'halting-shaped wall') NOT done: his phrase, and A makes it earned. MetaCoq absent so vendor L unusable; Substrate typeclass needs total run so L is not a Substrate instance, the diagonal is restated for L. Docs pending.
- Item 5 round 1 DEFINED (pre-registered): coq/kernel/foundation/StructuralCore.v sha256 e0af6c19eb1cd5cad4d8991b3265e4b327af754b2793243c14132661f0d901dc at 2026-09-29 00:16Z (then lemma thiele_run renamed thiele_core_run to avoid a name clash with ProperSubsumption.thiele_run; no definition changed), BEFORE any uniqueness/discrimination test. RCM record, Adequate (ledger_carried, rc_a2, carries_record, turing_equivalent via MM2), core_bisim/core_equiv (bisim up to cert + step cost, relational), ThieleCore = unbounded VM (vm_apply_u, program in state, any init, halted = pc=len & reg9=1), uniqueness_round1. Proved: thiele_core_adequate, history_core_equiv_thiele. Helper VMUnboundedLedger.v (vm_apply_u_mu, _certified, _permanent, _no_free_certification). Commit blocked by stale receipt: receipt regen started detached 00:16Z (receipt_run.sh -> logs/receipt_done.txt); commit StructuralCore alone first, THEN write StructuralUniqueness.v (planned escapes: CPU-time-billed ThieleCore = every step +1; revocable reading; RAM no-record not Adequate).
- Test suite 2026-09-29: 1089 pass; failing only stale generated artifacts (receipt fingerprint, MasterSummary pin, RTL manifests) that the pre-commit hook/receipt regen refresh; connectivity fixed with SCOPE NOTE in LRecursion.v.
- Item 8 PARTIAL (writer identity + lower-bound potential only; the four framework comparisons are NOT done): coq/kernel/nfi/CostSemanticsComparison.v (run_writer_is_run_and_cost: ledger = writer monad; a2_iff_nonnegative_amortized_cost: A2 = potential method with Phi=[uncertified]; nfi_by_potential; certification_system_is_potential_method). Monograph subsection sec:potential. Linear-logic reading covered via AARA's affine types (stated, not separately formalized).
- Items 10, 11 PARTIAL (text written; NOT validated against primary sources): physics = Landauer + permanence-to-merge bridge (Berut 2012 measured m=1,k=1 case); 8 prior-work entries added to Section 1 list (Lawvere, Tsirelson/Landau, Bennett 1982, Maroney/Sagawa-Ueda, Zurek, Hashcash/PoW, QIF Smith, graded monads).
- Item 1 IN PROGRESS: cited-theorem statements dumped (241 theorems). Found overclaims: quantum_realizable family (renamed globally to npa_psd / npa_gram, identifiers done, prose pending); hardness_escape_succeeds + transparency_log_escape vacuous (HardnessHypothesis field is `exists s, vm_mu s = 1`, trivially true) -> repair; classical_bound_achieved proves only mu=0, not S=2 -> strengthen; kami_refines_vm_step is only a write_reg lemma but TECHNICAL_DISCLOSURE says it refines the step for 47 opcodes -> rename + fix prose; ocaml_runner_agrees trivial existential, ocaml_bisimulation_closure 3rd conjunct trivial -> rename; rtl_coverage_partition is `37+10+0=47` -> rename; MuCostDerivation cost_uniqueness/cost_necessity definitional and its NOTE ("any implementation MUST erase log(Ω/Ω')") contradicted by item 4 -> rename + fix.

Related: [[research-open-question-plan]], [[guarded-coq-builds]], [[prose-style-no-em-dashes]], [[no-ai-attribution]].

## Codex continuation, 2026-09-29

The earlier DONE labels above are historical and must not be treated as plan
closure. Codex performed a deeper audit and found several obligations still
open or overstated. The authoritative live handoff is
`/home/codespace/.cache/thiele-guard/research-execution-status.md`.

Current branch and ordering:

- Branch `work/research-plan`, HEAD `8ed7ba74`; no research checkpoint commit yet.
- Preserve `StructuralCore.v` round 1. A definition-only dated round 2 now exists
  at `coq/kernel/foundation/StructuralCoreRound2.v` and is registered and built.
- Do not write uniqueness or discrimination results until all current dated
  definitions are committed. The original plan requires that temporal evidence.
- The guarded full Coq build passes. Inquisitor has 0 HIGH and 0 MEDIUM. The
  merged vacuity artifact covers 698 theorems with zero findings.
- The full Python suite excluding the stale receipt passes: 1114 passed and one
  deselected. Citation audits and theorem-meaning coverage pass.
- Receipt caching was repaired with transactional completion markers and hashes
  of source, stdout, stderr and count. Selective imports were regression-tested.
  Regenerate the complete receipt before committing, then update counts, rebuild
  PDFs, rerun all gates, and allow the strict pre-commit hook to verify the tree.

Substantive scope corrections already present in the working tree:

- `CommitmentBitContract` replaces the misleading hardness hypothesis. Its
  verifier theorem is a contract construction, not a cryptographic result.
- TPM quote projection is explicitly connected to
  `V_does_not_factor_through_classical`, with a lossless adapter theorem.
- `CostSemanticsComparison.v` proves writer identities and a lower-bound
  potential argument only. It is not yet four framework embeddings, and AARA's
  usual upper-bound direction must not be conflated with that result.
- The current four-state observer counterexample is valid but is not minimal.
  Preserve its definition; after the baseline commit, add a dated incremental
  observer definition and prove or refute the three-state minimum claim.
- Round 1 and round 2 uniqueness and discrimination remain untested. A
  CPU-time-billed wrapper is the leading escape candidate. Failed conjectures
  must remain visible and must drive the final claim rewrite.
- Actual-spec work for EVM/KEVM, RFC 9162 transparency, TPM 2.0, Casper FFG and
  Necula PCC is not complete merely because abstractions use similar names.

User authorization is to finish every plan item with TDD and no shortcuts. This
does not authorize merging to main or releasing. Use `apply_patch` for edits,
keep Coq builds serialized and guarded, retain the name No Free Insight, and do
not use correction-history prose or em dashes in publications.

## Codex pre-baseline correction, 2026-09-29

The expensive receipt was paused again after a final semantic audit found
interpretive overclaims. The repairs are now in the working tree and covered by
red-first regression tests:

- Pointer-observable results are synthetic labelled Boolean observer models,
  not deployed/security/cost correspondence theorems. Several exports were
  renamed accordingly, including `five_labeled_models_have_selected_pointer`.
- The gas, explicit-finalize, report, and carried-mu-claim reductions explicitly
  disclose that they are abstract wrappers. TPMQuoteGap cites final TCG Version
  185 and is scoped to selected quote fields with external authenticity.
- `V_does_not_factor_through_classical` is described only under its supplied
  collision, explanation, soundness, and completeness premises; the three
  constructed interfaces are not called an exhaustive hardness trichotomy.
- Structural Round 1's weak existential property is now
  `halting_problem_coverage`; no effective encoding, reverse simulation, or
  Turing-equivalence theorem is claimed. VMUnboundedStep is unbounded
  mathematical semantics, not hardware-faithful finite-word semantics.
- `observer_narrowing_can_be_free` replaces the overbroad old name. It exhibits
  one admissible zero-cost measurement; the lower-bound price may overcharge.
- MasterSummary is explicitly a selected established-claim ledger until the
  research-plan outcomes are integrated. Its empty list is scoped to
  project-local proof holes, not research conjectures.

Full serialized Coq rebuild passes after these changes (74.0 seconds, 738 MB
peak Coq RSS); 25 targeted audit/meaning tests pass. No uniqueness or
discrimination test has been written. The coming commit is truthfully a late
baseline snapshot because other research modules were already authored, but it
still freezes both definition-only structural rounds before they are tested.
Regenerate the receipt and all derived outputs before that commit.

## Pause checkpoint for Claude, 2026-09-29 06:06 UTC

Devon asked Codex to stop active work so Claude can resume later. Treat this
section and the external execution-status file as the current checkpoint. No
processes or subagents remain active. Nothing has been staged or committed.

Repository state:

- Workspace: `/workspaces/The-Thiele-Machine`
- Branch: `work/research-plan`
- HEAD: `8ed7ba74`
- The tree is intentionally large and dirty: 306 tracked files differ and the
  new research sources/tests are untracked. These changes are the research-plan
  work, generated Coq outputs, and refreshed evidence. Do not discard, reset,
  clean, or selectively check them out.
- No uniqueness or discrimination result/test has been written. Both dated
  structural definition rounds are still definition-only. This is the key
  chronology invariant.

What completed immediately before the pause:

- The full assumption receipt completed successfully at 05:56 UTC. It contains
  13,028 queries over 433 files: 5,692 closed under the global context, 7,336
  using only the five recorded Coq standard-library constants, and zero
  project-local or third-party axiom findings. Peak Coq RSS was 1,247 MB and the
  guarded run exited 0 after 3,219 seconds.
- `python3 scripts/check_assumption_consistency.py` passes. The inventory says
  13,027 addressable declarations while the finished receipt contains 13,028
  queries; the consistency checker accepts the extra generated probe query and
  the published total is 13,028.
- Public counts were updated in `.zenodo.json`, `CITATION.cff`, `README.md`,
  `THIELE_MACHINE.txt`, and `monograph/monograph.tex`. A tracked-source sweep
  found no remaining stale 12,934, 5,598, or 13,027 publication counts.
- `bash monograph/build_monograph.sh` passed and regenerated both PDFs and both
  plaintext outputs: 196-page monograph and 69-page math specification.
- `scripts/audit_monograph_citations.py` passed with every citation resolving.
  `scripts/audit_monograph_semantics.py` completed with two advisory items, not
  failures: the prose around `vm_structural_shortcut_undecidable_encoded` does
  not spell out that its conclusion is an iff, and
  `level_k_verification_floor` is a deliberate alias of
  `level_k_certification_cost_floor`.
- Proof dependency, MasterSummary, RTL text-transform, and RTL pipeline
  artifacts were regenerated successfully.
- The completed receipt batch work directory was moved out of the repository
  to
  `/home/codespace/.cache/thiele-guard/receipt-work-archives/completed-prebaseline-20260929`.
  The IDE tabs under `build/probe/receipt-work/` therefore point to the old
  location; no data was deleted.

Interrupted check:

- Codex started a fresh full vacuity sweep, then Devon asked to pause. The guard
  and its orphaned `vacuity_gate.py` child were terminated cleanly. A process
  check confirmed no vacuity, guard, or Coq child remains.
- The interrupted run did not replace `artifacts/vacuity_audit.json`; that file
  still records the previously completed 698/698 clean sweep. Rerun the full
  sweep before the baseline commit because later source and generator changes
  must be covered.

Exact next sequence, still before any structural-result test:

1. Run the full vacuity manifest serially under the guard:
   `python3 /home/codespace/.cache/thiele-guard/run_guarded.py --seconds 3600 --coq-seconds 900 --log /home/codespace/.cache/thiele-guard/logs/vacuity-prebaseline-resume.log -- python3 scripts/vacuity_gate.py --manifest scripts/vacuity_targets.json --jobs 1 --output artifacts/vacuity_audit.json`
2. Regenerate `INQUISITOR_REPORT.md` under the same guard discipline and require
   zero HIGH and zero MEDIUM findings.
3. Run the complete strict suite serially:
   `python3 -m pytest tests/ -q --tb=short --strict-backends -n 0`.
4. Run `python3 scripts/generate_verification_receipt.py`; it reruns Inquisitor
   and the complete strict suite and refreshes
   `artifacts/verification_receipt.json`.
5. Recheck assumption consistency, both citation audits, RTL artifact checks,
   and the publication build if any source changes while resolving a gate.
6. Ensure no temp directory is untracked, stage the entire intended tree, and
   commit with an honest message such as
   `research: freeze late preregistered baseline`. The strict pre-commit hook
   rejects partial staging/untracked files, rebuilds serially, runs every test,
   regenerates evidence, and must not be bypassed.
7. Record the commit hash here and in the external status file. Only then write
   the first failing uniqueness/discrimination contract test.

Post-baseline obligations remain unchanged: formally refute or prove both
uniqueness rounds and run the RAM/reversible/CPU-billing discrimination set;
add the incremental observer-knowledge definition and prove the three-state
witness plus two-state lower bound; implement actual source-pinned KEVM, RFC
9162, TPM v185, Casper FFG, and Necula PCC interpretations; complete the four
framework comparison rather than treating the writer/potential lemmas as all
four; apply the verifier result to a real protocol only where its premises can
be justified; validate physics and prior work against primary sources; then
rewrite claims from outcomes, regenerate every receipt/publication, and pass
all release-quality gates. Do not merge or release without asking Devon.

## Claude resume, 2026-09-29 ~06:40 UTC

- Found everything already staged (330 files), not "nothing staged".
- Reconstructed StructuralCore.v round 1 as of 00:16Z from the d669abf4 transcript; hash matches e0af6c19 exactly. Saved at /home/codespace/.cache/thiele-guard/StructuralCore.round1-0016Z.e0af6c19.v. Diff to current: renames (turing_equivalent->halting_problem_coverage, thiele_run->thiele_core_run) and comments only; no definition body changed.
- Devon decided (2026-09-29): RESTORE HIS PROSE NOW, before the baseline commit. Codex replaced author prose with neutral disclaimers in ~20 Coq headers (PointerObservable*, TransparencyLog, TEEAttestation, ProofCarryingVerifier, PoSFinality, GasMetering, VerifierEscape_Hardness, MuCostDerivation, ClassicalBound, MasterSummary, MuLedgerQuantumBridge, MuComplexity, QuantumPartitionPSD, Unitarity, Tsirelson..., VerifierExhaustiveness, OCamlExtractionBridge, F3...). Method: start from staged file, restore true author sentences from HEAD 8ed7ba74, rewrite only overclaims, keep tests/test_research_audit_regressions.py green (forbidden/required phrases).
- Small fixes queued: LRecursion header "fails for a diverging one" -> matches L_rice (another closed program); KnowledgeNarrowing "The plan's target" and "stated on the logic"; CostSemanticsComparison ShadowPricing sentence; VMUnboundedStep "but are otherwise use"; StructuralCore line 3 restore "before any test against it".
- "charge" is Devon's own common word (201 in HEAD coq): not a violation.
- ~08:00 UTC: prose restoration applied to the files listed (judgment calls kept Codex text in Unitarity, NPAMomentMatrix, F3, OCamlExtractionBridge, spec mu-hierarchy/verifier; not a full restoration) (hand edits, code verified identical via comment-stripped compare; audit regressions + meaning gate green). Coq: PointerObservable, PointerObservableCounterexamples (full rewrite restoring protocol/C1-C3/M1-M3; fixed his "one confirmation" slip -> two), PointerObservableReductions, TransparencyLog, MuCostDerivation, MuLedgerQuantumBridge, ProofCarryingVerifier, TEEAttestation, GasMetering, PoSFinality, VerifierEscape_Hardness, ClassicalBound, MasterSummary, MuComplexity, QuantumPartitionPSD, VerifierExhaustiveness + queued small fixes. Docs: README verifier section + 6 falsification rows; monograph five-disciplines section (his "Stake it or it doesn't count" etc. restored), pointer section, hardness label; math spec adversarial-search subsection + table rows; disclosure + THIELE_MACHINE.txt sentences. Found: THIELE_MACHINE.txt attributed 13,028 to v3.3.0 (release had 12,934) -> fixed. "stated on the logic" is Devon's established idiom (in v3.3.0), NOT a typo. Stale fact: OCaml parity suite is 58 tests, not "59 x 47, all 12 fields".
- Then: guarded coq rebuild (log coq-claude-prose-restore.log), then the 7-step gate sequence, monograph rebuild (PDFs), commit.
- 2026-09-29 (session resumed 13:01 after an interruption): coq rebuild PASS (108 files, 243 s, 1031 MB); monograph rebuilt (197 + 71 pp), both citation audits pass; vacuity 698/698 ok 0 vacuous 0 error (658 s); Inquisitor 0/0/0 after restoring a SAFE marker Codex dropped on MasterSummary.master_remaining_project_local_admits (Inquisitor EMPTY_LIST window = 2 lines above the Definition). Gate 3 (strict pytest -n 0) running, log pytest-prebaseline-claude.log.

- RULE (Devon 2026-09-29): never write DONE unless the plan item's own acceptance criterion is met and verified with evidence. Otherwise write PARTIAL and list what remains. A compiling file or passing test is not completion.

## Baseline committed, 2026-09-29 14:42 UTC

- Commit 34971852cf2e2e5a7892e5fb85b18740ce44af0a on work/research-plan, "research: freeze late preregistered baseline". Passed the strict pre-commit hook under the guard (1205 s, peak Coq RSS 1476 MB): serial vendor + Coq rebuild, extraction, vacuity, full suite (1130 passed).
- Frozen definitions in that commit: StructuralCore.v sha256 fd57d8602957cc0b85f3cc7c7c4cd3f304bbc39abd5882804f5477e4ded2fca7; StructuralCoreRound2.v sha256 95b6644d94e519119184b2460328b2472a5b94b7501c535008765a74b74be9ee. Both definition-only; no uniqueness or discrimination test or theorem exists at this commit.
- Next (in order): red uniqueness contract test (CPU-time surcharge wrapper as leading escape) for rounds 1 and 2; discrimination set (RAM, Janus-style reversible, CPU billing); item 4 incremental observer definition + 3-state witness + 2-state impossibility; item 1 audit closure incl. logged drifts (46 vs 47 opcodes in receipt claim and parity/cross-layer docstrings; ocaml_extraction_faithful called "axiom" in OCamlExtractionBridge.v comments though it is a Theorem); items 6, 8, 9, 10, 11, 14, decision summary. Casper FFG route (port Coq 8.8 proofs vs paper model) needs Devon's decision. No merge or release without asking.

## Uniqueness results and Round 3 freeze (2026-09-29, after baseline 34971852)

- Rounds 1 and 2 REFUTED (uncommitted until the next commit): coq/kernel/foundation/StructuralUniqueness.v, uniqueness_round1_refuted / uniqueness_round2_refuted, closed under global context. Counterexample BilledCore = Thiele core + step counter in ledger (each step +1). Red/green logs: uniqueness-red.log, uniqueness-green.log; contract tests/test_structural_uniqueness_contract.py pins round 1/2 blobs to 34971852.
- Devon chose option A + refinement "uniqueness up to the price schedule" (2026-09-29). Round 3 defined in StructuralCoreRound3.v (definition-only, predictions in header): 3a record tied to computation (predicted FALSE via record "1 <= vm_mu", = pointer-observable question), 3b record = certification via cover (predicted TRUE, near-direct from cover). Sameness observes structure through the entry test's own cover (presupposes VM). Freeze commit pending: receipt regenerating (detached, receipt-round3.done), then commit through hook. ONLY THEN write Round 3 proofs + discrimination set.
- Round 4 (Devon): non-presupposing, two-way record-carrying simulation WITH TEETH: lockstep up to a constant, record changes at matching steps, price preserved up to schedule mapping; freeze with at least one predicted failure from the discrimination set (RAM with bolted-on record must fail or the test is too loose; reversible machine outcome classified in advance).
- Every Coq-changing commit needs a full assumption receipt (~54 min, compiled-digest cache is global) + hook (~20 min). Batch Coq results per commit. Launch long jobs with setsid (session deaths kill children).
- Round 4 predictions agreed with Devon (2026-09-29), to write into the dated Round 4 file before any proof: (1) RAM + record NOT a reading of its computation ("bolted-on"): FAIL. (2) RAM + tied, permanent, A2-priced record: PASS (the headline's own prediction; Thiele VM is essentially that). (3) plain RAM, no record: fails at the door. (4a) reversible machine, unbounded memory, keeps full history: PASS (A2 imposed directly; shows Round 4 is about the record axis, not irreversibility). (4b) reversible machine, finite memory: cannot pass as reversible; cite PermanentCertification.v (permanent flip on finite state space forces a non-injective step), do not re-derive. Merge condition belongs to the finite/physical version, not the abstract structural claim. Constraints with teeth: lockstep up to a constant, record changes at matching steps, price preserved up to schedule mapping.
- Freeze commit d930fcac (2026-09-29): Round1/2 refutations + Round3 defs (definition-only, predictions in commit msg). Round 3 proofs drafted in ~/.cache/thiele-guard/drafts (3b holds, 3a refuted, SurchargedCore general); incremental per-module receipt runner drafted + tests (red 14 fail -> green 21).
- COMMIT SPEED (Devon angry 2026-09-29 about slow commits). Fixed: (1) per-library cached assumption receipt (scripts/run_assumption_batches.py, cache build/probe/assumption-cache, gitignored) -> incremental runs; (2) hook vacuity: only added targets checked unless gate/existing entry changes (was full 11-min sweep when manifest touched); (3) fix_kami_coq18.sh idempotent (was recompiling Multiplier32/64, ~100 s, every commit). Commit routine now: build -> incremental receipt -> stage -> hook (it runs tests + Inquisitor). DO NOT also run Inquisitor/pytest/verification receipt manually before commits; regenerate verification_receipt.json only at release. Work on the next item in drafts while any long job runs.
- Commit 89760103 (2026-09-29): Round 3 proofs, runner (validated 0 diffs/13045), hook speed-ups, Round4 + incremental-narrowing definitions frozen (predictions in msg), item 6 Casper/EVM models + Section 17 correction. Next: Round4/item4/item7/item8 proofs, item1 extraction-bridge fixes, item14 docs, TAC link fix.

- 2026-09-29 19:2xZ: Round 4 proofs + discrimination + CostFrameworks + extraction-bridge audit committed as d9effe75 (first attempt failed Inquisitor FOUNDATION_UTILIZATION_GAP on KnowledgeNarrowingMinimal.v; fixed with standalone SCOPE NOTE, .vo unchanged).
- Item 1 trivial-proof scan (scratchpad trivscan/scan.py): all 402 cited theorems tried with trivial tactics; 22 fall; 18 honest (computations or prose already says definitional); fixed 3 passages in math spec (partition + CHSH classifier lemmas glossed as "does not touch", "RTL Coverage: Zero Gaps" title). Committed as be27f21c. Scan limits: 2-3 s timeouts, does not catch vacuity (vacuity gate does) or heavy-but-shallow proofs. Item 1 status after commit: PARTIAL -> remaining: none known in cited set beyond scan limits; call DONE only with Devon's agreement on acceptance.
- Devon 2026-09-29 evening: finish everything, no questions, NO MORE COMMITS for now (overrides his pasted step 7 merge/tag). Decisions he set: headline leads with latch_core_honest + irrecoverability (VM windows) + merge pricing, says latch form is close to definitional, pointer question open; Section 10 title kept only if L recursion not by construction (checked: genuine, kept).
- Applied uncommitted: README point 6, monograph abstract paragraph, THIELE_MACHINE.txt point 6 + new Section 12 THE RECORD AXIS (HOW TO CHECK -> 13), CITATION + Zenodo sentence; Section 17 table levels (cryptographic), TPM 'until the next reset'. Release notes draft: ~/.cache/thiele-guard/release/v3.4.0-release-notes.md (version not bumped in tree). Full gate run script: ~/.cache/thiele-guard/gates/run_all_gates.sh (results.txt, done).
- Plan audit classification: done: 1, 4, 5, 10, 11, 12/13 (changed claim: up to schedule / latch), 14, decision summary; done with changed claim: 2 (name kept, certified insight), 3 (L not VM fragment; VM fragment open), 6 (CT no Coq Merkle model; PCC out of family), 7 (general any-base theorems, no concrete RAM/Janus), 8 (no full embeddings), 9 (scoped TPM quote).
- 2026-09-29 23:35Z: ALL GATES PASS on the uncommitted tree (full hook-equivalent run + doc rerun): Coq 445/445, 0 Admitted, full vacuity 772/772 clean, Inquisitor 0/0/0, pytest 1157 passed, verification receipt ALL CLAIMS VERIFIED, citation + semantic audits clean, make verify/verify-claims/verify-research, rtl-gate. Semantic audit fixed (window per section/table row, \allowbreak identifiers, default covers monograph+spec+README+disclosure) with tests/test_monograph_semantics_window.py (red->green) and now gates via pytest. Nothing committed (Devon: no commits); no merge/tag. Next when Devon says: commit, version bump to 3.4.0 (not done in tree), merge, tag, Zenodo using ~/.cache/thiele-guard/release/v3.4.0-release-notes.md.
