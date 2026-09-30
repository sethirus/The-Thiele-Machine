# Part 0, Round 2 freeze

Frozen 2026-09-30 before the Round 2 execution of Items 0.1 and 0.2.

This record distinguishes technical evidence from compliance with the Ground
Truth procedure. It does not alter an earlier round or claim that earlier
evidence was produced under a freeze that did not exist.

## Outcome convention for operational items

Items 0.1 and 0.2 are imperatives about Git state and command execution, not
mathematical propositions. For these two items, **PROVED** means that the exact
operation has concrete, reproducible evidence. It does not mean that a hollow
Coq theorem about repository state was introduced. This is an interpretation
call required to apply R2 to Part 0. No later theorem item receives this
exception.

## Earlier attempt

Commit `2bb7e5ea8ff99404d244fc9aac77280af1986ceb`, tree
`bddf9392353beb11cb4fd03a05b03bd4b6b5c715`, contains the work that was current
when the Ground Truth instruction arrived. Its final tree has substantial gate
evidence. That evidence is a union of runs, not one all-green invocation after
the instruction. An early broad run contained a semantic-audit failure, a
later document run repaired and reran that audit, and the final commit hook
reran the Coq build, 1,157 tests, Inquisitor, and RTL artifact checks.

The required order was not respected. Part 1 work began before the Item 0.1
commit hook finished, and Part 1 proof drafting began while the Item 0.2 clean
build was still running. No contemporaneous Item 0.2 result commit was made.
Those chronology defects cannot be repaired retroactively, so the earlier
attempt is evidence only and does not close Part 0.

The earlier clean-build attempt exported the tracked `coq`, `scripts`, and
`vendor/coq-undecidability` source subsets. It exported BBV and Kami at
`032537e726ad2b235a16162e83357f054a3039be` and
`db5a214e3e016421af9346a0967160e38b389879`. It removed `.vo`, `.vos`, `.vok`,
`.glob`, `.*.aux`, `.cmx*`, `.cmi`, `.cmo`, and `.o` files. It retained
`coq/.Makefile.coq.d` and
`vendor/coq-undecidability/theories/.Makefile.coq.d`. All `.vo` files began
absent, so the Coq object recompilation itself remains valid.

That guarded serial build exited 0, built 445 Coq `.vo` files, found zero
`Admitted` commands, took 3,190 seconds, and reported a sampled 1,096 MB peak
resident memory for a Coq process. The retained evidence is:

| Evidence | SHA-256 |
|---|---|
| `/home/codespace/.cache/thiele-guard/logs/fresh-build.log` | `430a26c94913646f6a7145d9a99010ece690b0f53a185f2ee215418af220b142` |
| `/home/codespace/.cache/thiele-guard/logs/fresh-build.guard` | `8ad566ba651f5b0043d53da0182b641061a8749cb16b1efd6374d40118bd9279` |
| `/home/codespace/.cache/thiele-guard/fresh.done` | `19eaf43821a7660ec323a87c8457bf74823beb296c39f5e01aa8a683aa50f061` |

## Item 0.1, Round 2: commit all current work

Exact parent: `a9c8270e68c608e4862d4d184aa98ab9d6ba9983`. Its committed Part 1
freeze remains in the ancestry as history and is not accepted as a compliant
preregistration.

Exact action: stage this freeze record and commit it through the strict hook.
The hook-generated `INQUISITOR_REPORT.md` is the only other permitted path in
the commit because the hook refreshes its UTC timestamp. The uncommitted Part 1
result work remains preserved and quarantined in Git stash object
`9641ba231bf2e9dcc95d0182fbb4cc6ce4eaff53`. It is not current worktree state
and must not be restored during Part 0.

Prediction: **PROVED** under the operational convention above.

Success requires all of the following:

- the commit has the exact parent above and its message names Item 0.1 as
  PROVED;
- the strict hook runs without `--no-verify` and exits 0;
- `git diff-tree --no-commit-id --name-only -r HEAD` contains exactly
  `research/rounds/2026-09-30-part0-round2-freeze.md` and the hook-generated
  `INQUISITOR_REPORT.md`;
- `git rev-parse refs/stash` still returns
  `9641ba231bf2e9dcc95d0182fbb4cc6ce4eaff53`, and
  `git cat-file -e 9641ba231bf2e9dcc95d0182fbb4cc6ce4eaff53^{commit}` exits 0;
- `git status --porcelain=v2` is empty.

Failure is any unmet condition above. The hook is run once as a guarded
preflight before `git commit`; its staged-path result must contain exactly the
two permitted paths above. The guarded `git commit` then runs the hook again.
This detects any other generated-file drift before a commit can silently
include it.

The result hash and R6 dispositions belong in the Part 0 result report. This
freeze is not edited after its commit.

## Item 0.2, Round 2: every gate and a from-scratch rebuild

Exact input: the successful Item 0.1 Round 2 commit.

Prediction: **PROVED** under the operational convention above.

### Exact checks

All Coq work is serial and runs under
`/home/codespace/.cache/thiele-guard/run_guarded.py`, with a 1,800 MB per-Coq
process ceiling, a 1,200 MB available-memory floor, and a 3,600 second ceiling
for each Coq process. The guard file must have SHA-256
`64fbcfd9f460ff6907a5bb1b15534960760fc3fc62cfdf2fb20c4b8e3fc6f6fb`
before every run.

1. Run the full manifest in `scripts/vacuity_targets.json` with one worker.
   Success requires zero `vacuous_true`, zero `vacuous_hyp`, and zero `error`.
2. Run `make assumption-receipt-check` and
   `python3 scripts/inquisitor_assumption_gate.py`. Success requires a current
   receipt and no project-local or third-party axiom finding.
3. Run `python3 scripts/inquisitor.py --report INQUISITOR_REPORT.md`. Success
   requires zero high, medium, and low findings.
4. Run `python3 -m pytest tests/ -q --tb=short --strict-backends -n 0`.
   This includes the prose, theorem-meaning, citation, extraction, hardware,
   and generated-artifact gates. Success requires exit 0 and a final pytest
   summary containing only a positive number of passed tests, with zero failed,
   error, skipped, deselected, xfailed, or xpassed tests.
5. Run `make verify`, `make verify-claims`, `make verify-research`, and
   `make rtl-gate`. Every command must exit 0.
6. Make a fresh isolated export using the algorithm below. The frozen
   superproject must record BBV at
   `032537e726ad2b235a16162e83357f054a3039be` and Kami at
   `db5a214e3e016421af9346a0967160e38b389879`.

   - Create the destination with `mktemp -d` and verify it is neither empty nor
     `/` before any deletion.
   - Run `git archive <ITEM_0_1_COMMIT> | tar -x -C <DESTINATION>`.
   - Create `vendor/bbv` and `vendor/kami` inside it. Archive each exact
     submodule commit into its matching directory with `git -C <SUBMODULE>
     archive <COMMIT> | tar -x -C <DIRECTORY>`.
   - Delete only files below the destination matching `.vo`, `.vos`, `.vok`,
     `.glob`, `.aux`, `.*.aux`, `.cmx`, `.cmxa`, `.cmxs`, `.cmi`, `.cmo`, `.o`,
     or `.a`. Also delete only `coq/Makefile`, `coq/Makefile.conf`,
     `coq/.Makefile.d`, `coq/.Makefile.coq.d`,
     `vendor/coq-undecidability/theories/Makefile.coq`,
     `vendor/coq-undecidability/theories/Makefile.coq.conf`, and
     `vendor/coq-undecidability/theories/.Makefile.coq.d`.
   - Run `make -C <DESTINATION>/vendor/bbv -j1`, the exported
     `scripts/fix_kami_coq18.sh`, `make -C <DESTINATION>/vendor/kami -j1`,
     `coq_makefile -f _CoqProject -o Makefile` in the exported `coq` directory,
     and `make V=1 -j1` there, in that order and under one guard invocation.
   - Parse non-option `.v` entries from the frozen `_CoqProject`. Require 446
     unique entries, require every source to exist, and require the matching
     path with suffix `.vo` to exist after the build. Require zero lines matching
     `^[[:space:]]*Admitted\.` in project `.v` sources outside patch files.

   Success requires every command and comparison above to exit 0.
7. Record the commands, exit statuses, counts, elapsed time, sampled peak Coq
   memory, log locations, and SHA-256 digests in a new result record. Do not
   edit this freeze.
8. Before the result commit, compare the worktree with the Item 0.1 commit.
   The only permitted changed paths are
   `research/rounds/2026-09-30-part0-round2-results.md`,
   `artifacts/vacuity_audit.json`, and `INQUISITOR_REPORT.md`. No proof, test,
   checker, or publication input may differ.

### Success and failure

Success is every check above passing on the frozen input, followed by a result
commit whose message names Item 0.2 as PROVED. That commit must run the strict
hook without `--no-verify` and pass it. Any failing check is a failed attempt,
not permission to weaken or edit a gate. Fixing a cause starts another fully
recorded attempt against the same frozen input unless the input itself must
change, in which case a new dated round is required.

Failure of the predicted outcome means that the exact gate set cannot be made
to pass after at least three genuine and materially different remedies or
attempts. Its final R2 outcome would then be **BLOCKED**, with each obstacle,
strategy, command, and result recorded.

### Planned hollowness checks for both items

- Definitional: command success is the acceptance criterion, and no
  mathematical result will be claimed.
- Built in: the checks execute separate compilers, auditors, simulators, and
  test backends rather than trusting a status field in a report.
- Vacuity: concrete Git objects, command logs, and a clean rebuild must exhibit
  execution.
- Swap test: the results are repository-specific and make no event or
  machine-generic claim. A different input commit requires a new run.
- Adversarial read: a separate reader receives this freeze, the result record,
  and the final Part 0 sentence before the Item 0.2 outcome is committed.

## Calls made

- R2 is interpreted operationally only for the two non-mathematical Part 0
  imperatives.
- The earlier attempt is retained as evidence but does not replace this ordered
  run.
- The strict hook is the acceptance surface for Item 0.1. The enumerated checks
  above are the acceptance surface for Item 0.2. Other Make targets that make
  release or completeness claims are not substituted for these exact checks.
- The Part 1 stash is quarantined because it contains results produced out of
  order and a known incomplete acceptance test. Preservation is not acceptance.

## Wrong predictions

No prediction was frozen for the earlier attempt. The Round 2 predictions are
the ones stated above and remain unresolved until their result commits.
