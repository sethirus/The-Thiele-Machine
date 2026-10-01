---
name: codex-handoff-2026-10-01
description: "READ FIRST when taking over from Codex: exact resume point (uncommitted Parts 5-8 + Item 3.1 Round 3 native recursion in progress), takeover protocol, remaining-work list, efficiency rules"
metadata:
  node_type: memory
  type: project
  originSessionId: 70b36a88-3eae-4541-839f-3a153861a590
  modified: 2026-10-01T05:17:35.138Z
---

## Final Codex handoff, 2026-10-01

Devon asked Codex to stop proof work, hand the tree to Claude, and make it
recoverable on his home PC. Read the tracked handoff first:

`research/rounds/2026-10-01-part3-item3.1-round3-handoff.md`

It supersedes the in-flight details below. The decisive state is:

- The exact native guest recursion theorem is NOT proved. The TDD contract is
  intentionally `1 failed, 1 passed`; the missing declaration is
  `vm_guest_recursion_theorem_closed : vm_guest_recursion_theorem`.
- The new output-preserving MMA -> MMA3 -> four-register guest bridge is
  kernel-checked. The final targeted build of `VMMMAReduction.vo` printed seven
  `Closed under the global context` lines.
- New proved modules are `VMGuestRecursion.v`, `MMAOutputEpilogue.v`,
  `VMMMA3GuestCompiler.v`, and `VMMMAReduction.v`. The last now includes the
  whole-program register permutation and `mma_output_to_guest_r0`.
- Next: verified guest initializer for the nested Goedel-coded MMA3 input,
  internal guest programs for numeric specialization and universal evaluation,
  exact-mu diagonalization, then the frozen theorem. No host dispatch and no
  fixed-width lanes.
- Parts 5-8/public documents are staged drafts, not final ground truth. Audit
  and reconcile them only after the recursion outcome. No merge/tag/release.
- Remote handoff branch: `handoff/native-recursion-2026-10-01`.
- Exact snapshot commit: `25f55ae01605531f3ec818c64d0a82315106ef0c`.
- On the home PC: fetch that branch and check it out. Do not infer completion
  from the snapshot commit; its theorem contract is deliberately red.

Snapshot taken 2026-10-01 05:16 UTC while Codex was still live. Supersedes the
"Current authoritative checkpoint" in [[ground-truth-plan-execution]] (that one
stops at d5cb4e7e and says Part 2 is next; it is stale).

## Where things are

- Branch `work/research-plan`, HEAD `fd953dc1` (Part 4). Committed after Part 1:
  c43d0c22, 3d4bd871, dc43689f (Part 2), 2438ae9c (Part 3), fd953dc1 (Part 4).
- EVERYTHING after fd953dc1 is uncommitted (~130 files). The index was staged
  by Codex as the snapshot for its clean rebuild; do not reset the index.
  Contents: Parts 5-8 proofs/freezes/results, `research/rounds/2026-10-01-ground-truth-final-report.md`
  (8.2/8.3 PENDING), scope-note amendment, and post-report round-2 work done
  on Devon's request: constructive Casper (PROVED, CasperFFG.v), ecosystem
  pointer necessity (REFUTED, EcosystemGame.v), calorimeter/master equation
  (protocol PROVED, intrinsic joule scale REFUTED), VMDynamicEval.v (decoder,
  g_eval, g_smn PROVED), Part 8 Round 2 ground-state rewrite of six public docs.
- Codex's own transcript: `~/.codex/sessions/2026/09/29/rollout-2026-09-29T02-56-15-01a0eb17-*.jsonl`
  (one session since 09-29, ~100 MB). Its narration is the best resume log.

## In-flight item: Part 3 Item 3.1 Round 3 (native guest recursion)

- Freeze: `research/rounds/2026-10-01-part3-item3.1-round3-freeze.md` (04:32,
  uncommitted). Target `vm_guest_recursion_theorem_closed : vm_guest_recursion_theorem`
  in `coq/kernel/foundation/VMGuestRecursion.v`, closed, no host evaluator,
  no fixed 64-bit packing. Predicted BLOCKED. Red test:
  `tests/test_vm_guest_recursion_internal.py`.
- Route: recalg -> MM (vendored `ra_mm_compiler`) -> MMA with output epilogue
  (`MMAOutputEpilogue.v`, being proved at 05:16) -> MMA3 -> guest R0-R3
  (`VMMMA3GuestCompiler.v`, done, closed). Pair-preserving binary
  specialization in R0-R2 is done in VMGuestRecursion.v.
- Note: vendored `mm_mma2` preserves only halting (prime-power encoding), hence the epilogue.
- Hard remaining piece, not started: proving the guest evaluator and the
  numeric code specializer are themselves recalg/MM-computable (needs the guest
  interpreter as an explicit mu-recursive term, or the L-extraction route
  `L/Reductions/MuRec/MuRec_extract.v`). Then diagonal proof. This is large;
  time-box it and record BLOCKED with three strategies if it does not close.

## Remaining after 3.1 (Codex's 04:24 list, still valid)

1. Finish ground-state refactor of the six public docs (README, THIELE_MACHINE.txt,
   monograph.tex, math_spec.tex, CITATION.cff, release notes): no process,
   round, "now/still/yet", "open questions" branding. Devon was angry about
   injected status paragraphs and the "A Checked Account with Open Questions" subtitle.
2. Reconcile the final report table with the round-2 outcomes above and the 3.1 Round 3 result.
3. Theorem meanings + audit entries for every new declaration.
4. Regenerate assumption receipt (synchronizer no longer rewrites historical audit ledgers).
5. Rebuild monograph, math spec, plaintext exports, PDFs.
6. Full gate: pytest, vacuity, Inquisitor, meaning, prose, assumption probe,
   then one isolated from-scratch Coq rebuild of the FINAL tree (the earlier
   rebuild was killed as obsolete at 04:06).
7. Fill 8.2 evidence, commit, push. No merge/tag/release. Devon: not published
   until everything finishable is finished.

## Takeover protocol

1. Confirm Codex stopped: transcript mtime unchanged 10+ min and no coqc/make/pytest
   running. Do not kill the codex app-server PID (it is the VS Code extension).
2. Safety snapshot before touching anything: `git stash create` then
   `git update-ref refs/handoff/codex-final <sha>` plus a tar of untracked files into scratchpad.
3. Read the last ~40 Codex tool calls in its transcript to find the exact proof
   state, then `make -C coq -j1 kernel/foundation/MMAOutputEpilogue.vo` under the guard.
4. Work inline on the main thread. No general-purpose subagents (97% of
   Devon's usage was subagent-heavy sessions). Grep with /usr/bin/grep, read narrow ranges.

## Protocol flags to raise with Devon (do not silently fix)

- The 3.1 Round 3 freeze was never committed before proof work began (R1).
- The final report's "batch commits at Part boundaries" call departs from R9.

## Disk (2026-10-01 06:10)

Root overlay is 32G and hit 99% full. `/tmp` is a separate 118G disk. Moved there:
`~/.cache/thiele-guard/{part0-round2-fresh.*,part8-fresh.*,fresh}` -> `/tmp/thiele-guard-archive/`
(obsolete clean-rebuild exports), and the cabal hackage `00-index.tar` -> `/tmp/home-archive/cabal/`.
Six unused `/vscode/bin/linux-x64` server versions went to `/tmp/vscode-bin-archive/`.
That freed nothing because they sit in the image layer. Do NOT move them back:
copying them into the upper layer would consume ~4G.
Result: ~2.4G free. A clean rebuild export needs ~400M. Put future rebuild exports
under /tmp, not ~/.cache. Next candidate if space runs low: `~/fpga-tools` (3.2G).
