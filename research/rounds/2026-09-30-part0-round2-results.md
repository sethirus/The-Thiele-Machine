# Part 0, Round 2 results

Recorded 2026-09-30 against Item 0.1 commit
`5d1245e6dd0af40cf56b831a0b06a91adda383a6` and the immutable freeze in
`research/rounds/2026-09-30-part0-round2-freeze.md`.

The outcome word **PROVED** has the operational meaning fixed in that record.
It reports concrete Git and command evidence for the two baseline imperatives.
It is not a mathematical theorem and creates no exception for later items.

## Outcomes

| Item | Prediction | Outcome | Acceptance evidence |
|---|---|---|---|
| 0.1, commit all current work | PROVED | **PROVED** | Exact-parent commit `5d1245e6`, two-path diff, strict preflight and commit hooks, preserved stash, clean post-commit tree |
| 0.2, every gate and a from-scratch rebuild | PROVED | **PROVED**, conditional on the strict hook for the commit containing this record | Every required check has a successful recorded execution; isolated rebuild passed on attempt 2 after the recorded runner-syntax failure; zero `Admitted.` commands |

## Item 0.1 evidence

The result commit is
`5d1245e6dd0af40cf56b831a0b06a91adda383a6`, with exact parent
`a9c8270e68c608e4862d4d184aa98ab9d6ba9983` and tree
`04d48344a65d9102377f32c12aef477b77a9c8a8`. Its message names Item 0.1
as PROVED. Its diff contains exactly:

- `INQUISITOR_REPORT.md`
- `research/rounds/2026-09-30-part0-round2-freeze.md`

The committed freeze has SHA-256
`85ba803e4b1c2e10c837a369d7782bfaa923e8d36c2e44fac68bdc1a740d54a0`.
The committed Inquisitor report has SHA-256
`6e69f1dbaca8a92d9106727829d939a03991c413342d9ee471a0497f0a0990b0`.

| Check | Payload log and SHA-256 | Exit | Guard seconds | Peak Coq RSS | Payload result |
|---|---|---:|---:|---:|---|
| Strict preflight hook | `part0-round2-item01-preflight.log`, `2c4a5aa01b5d732a65a5b40659af20e2976a6ceaada948b9d5b9ce7b644e1724` | 0 | 349.3 | 1,041 MB | 1,157 tests passed in 123.30 seconds; Inquisitor OK; hook PASS |
| Strict commit hook | `part0-round2-item01-commit.log`, `ad92a2935fe1b837f2ec65a437e0cdfd6797bdd149f8da08e578763ca8c0bc40` | 0 | 344.8 | 1,056 MB | 1,157 tests passed in 122.70 seconds; Inquisitor OK; hook PASS |

Both logs are below `/home/codespace/.cache/thiele-guard/logs/`. The guard
summaries were emitted to the retained caller transcript, not the payload
logs. The table distinguishes those evidence channels.

The preserved Part 1 work remains at stash object
`9641ba231bf2e9dcc95d0182fbb4cc6ce4eaff53`. The ref still resolves to that
object, and the object resolves as a commit. It was not restored during Part 0.

## Item 0.2 commands and evidence

Every frozen check command used guard
`/home/codespace/.cache/thiele-guard/run_guarded.py`, whose checked SHA-256 was
`64fbcfd9f460ff6907a5bb1b15534960760fc3fc62cfdf2fb20c4b8e3fc6f6fb`.
The guard enforced a 1,800 MB ceiling for each Coq process, a 1,200 MB
available-memory floor, and a 3,600 second ceiling for each Coq process. The
frozen check commands were serial. The payload logs are below
`/home/codespace/.cache/thiele-guard/logs/`.

| Payload command | Payload log and SHA-256 | Exit | Guard seconds | Peak Coq RSS | Observed result |
|---|---|---:|---:|---:|---|
| `python3 scripts/vacuity_gate.py --manifest scripts/vacuity_targets.json --jobs 1 --output artifacts/vacuity_audit.json` | `part0-round2-vacuity.log`, `842db5de24f712d219f384d5707624bd0d560f0cf969a94a1a5f54b3d93c695e` | 0 | 772.2 | 1,391 MB | 772 total, 772 OK, 0 error, 0 vacuous true, 0 vacuous hypothesis |
| `make assumption-receipt-check` | `part0-round2-assumption-receipt.log`, `5515dc11fa363dee3fdebc0cadf071e8b14c2be93cba313f9e89267f791e30a9` | 0 | 6.5 | 0 MB | Fresh semantic fingerprint; exact committed receipt reused |
| `python3 scripts/inquisitor_assumption_gate.py` | `part0-round2-assumption-gate.log`, `3893be7e50f3ebcf46ac2ab06cb763f1d46283ba47dc7a9f5db200d838d22ee4` | 0 | 0.5 | 0 MB | No local assumptions or admitted proofs; critical kernel gate PASS |
| `python3 scripts/inquisitor.py --report INQUISITOR_REPORT.md` | `part0-round2-inquisitor.log`, `77dd7f137403d9544748d4201d07c0f1018adba88937af4bda51e564bc30a96e` | 0 | 161.5 | 527 MB | 460 Coq files; 0 high, 0 medium, 0 low findings |
| `python3 -m pytest tests/ -q --tb=short --strict-backends -n 0` | `part0-round2-pytest.log`, `34f0009020804af11f39a112a60de17188fdb679d2c3162feee921ab6c57bc23` | 0 | 127.4 | 1,008 MB | 1,157 passed in 126.06 seconds; no other result category |
| `make verify` | `part0-round2-make-verify.log`, `e2074037483226625cec94555cfa54596082b18c9808bff6884ffc1771870520` | 0 | 4.5 | 426 MB | All nine checks passed |
| `make verify-claims` | `part0-round2-make-verify-claims.log`, `700041fcc5460203c905dad5cabafbe44795dbeaaa78d0a889a0dec74ce07eb4` | 0 | 0.5 | 0 MB | Both requested Coq targets current |
| `make verify-research` | `part0-round2-make-verify-research.log`, `771319be982481589c21b22f2e70b778729d6b436aa4655a0b0b1466e50fb07d` | 0 | 0.5 | 0 MB | Both requested Coq targets current |
| `make rtl-gate` | `part0-round2-rtl-gate.log`, `7c6b6ef410c39211867d353465686639c096944a54d4ac57c4235e303f64b67e` | 0 | 16.1 | 0 MB | Extracted RTL synthesized; 4,473 cells; gate PASS |

The vacuity artifact produced by the run has SHA-256
`46a2217b220d4cf168b12fef8dc332e33e6669425c7a6807035e74d85a1a7e1c`.
The standalone Inquisitor report produced by the run has SHA-256
`edb756cf30396b703b1721f97fdf9d7bb9bc552d1919de493388b9957689b8da`.
The result commit hook is expected to refresh the report timestamp, so this is
the digest of the standalone frozen check, not a prediction of the committed
report digest.

The full assumption receipt reports 13,100 probed statements: 5,756 closed
under the global context, 7,344 using only standard-library axioms, and zero
user or third-party axiom findings. Its JSON and raw-output SHA-256 digests are
`0a16ab01fc312b84ea3db09ce7411c8479c5923b30b283e808642b838e4326dd`
and `9c0c770e2d1126b50c0b313e7f21dd1ebba0f52f42e0e6b0ae97b3c85d4f425e`.
The assumption-gate report has SHA-256
`7af3b4dc84250879e2024e91434c3a06ed67c0b9ea3c80f12587e52963bcff5f`.

### Isolated rebuild attempts

The payload in both attempts was
`bash /home/codespace/.cache/thiele-guard/part0_round2_rebuild.sh`. The script
verified the exact superproject and submodule objects, made a guarded
`mktemp -d` export, removed only the frozen artifact classes, and ran BBV,
Kami, and the main Coq build serially in the frozen order.

Attempt 1 failed before any compiler ran. Its runner had SHA-256
`0b52909c79404bd43d794fa83f69839d319ce7130955ad9837db4030dba9f101`.
A multiline `find` expression lacked shell continuation characters, so `find`
received an unmatched opening parenthesis. The guard reported exit 1 after
2.0 seconds and 0 MB peak Coq RSS. The payload log records the exact error and
has SHA-256
`bd8d869d6f5e4cceb249753652a3a7f574182b16589fe166665b094da996b59d`.
The failed export remains at
`/home/codespace/.cache/thiele-guard/part0-round2-fresh.7k5Ha2`.

The remedy changed only the external runner's line continuation. It did not
change the frozen commit, submodule objects, build order, source-count checks,
or acceptance conditions. `bash -n` passed, and an independent reader found
no remaining runner defect. The repaired runner has SHA-256
`bdacfe198fee7a2d3396a1aad949a685144aa74e2a93e031242b4759e51fa691`.

Attempt 2 used that repaired runner. The guard reported exit 0 after 3,091.7
seconds and 1,095 MB peak Coq RSS. The runner reported 3,091 whole seconds.
Its payload log has SHA-256
`1b541436acc3beb9f2e189a31e27e5d2e8e00c4ea4f5735c33059cfe9819f628`
and records:

- export: `/home/codespace/.cache/thiele-guard/part0-round2-fresh.EzrKRU`;
- superproject: `5d1245e6dd0af40cf56b831a0b06a91adda383a6`;
- BBV: `032537e726ad2b235a16162e83357f054a3039be`;
- Kami: `db5a214e3e016421af9346a0967160e38b389879`;
- frozen `_CoqProject` source entries: 446 total and 446 unique;
- existing sources after export: 446 of 446;
- matching `.vo` files after the build: 446 of 446;
- matching `Admitted.` commands outside patch files: 0.

An independent recount after the runner finished found the same counts, zero
missing sources, zero missing `.vo` files, and zero matching `Admitted.`
commands. The exported and committed `_CoqProject` files both have SHA-256
`2390eb33e12d667c3ab241874cdf26c4e337edff68d20fe50fe3daa126fe50c0`.

## Worktree boundary

Before this result record was added, comparison with Item 0.1 commit
`5d1245e6` showed exactly two tracked differences:

- `INQUISITOR_REPORT.md`
- `artifacts/vacuity_audit.json`

With this record, the permitted result-commit surface is exactly those two
paths plus
`research/rounds/2026-09-30-part0-round2-results.md`. No proof, test, checker,
or publication input differs. The containing commit must pass the strict hook
without `--no-verify`; otherwise the Item 0.2 outcome remains open.

## Hollowness checks

### Item 0.1

- Definitional: no mathematical proposition is claimed. The exact Git action
  and its acceptance checks are the result.
- Built in: commit success was not copied from a status field. The parent,
  tree, path set, hook exits, stash object, and clean post-commit state were
  checked separately.
- Vacuity: commit `5d1245e6` and stash object `9641ba23` exist and resolve.
  Both strict hooks executed their real compiler, test, and audit payloads.
- Swap test: the result is tied to one exact parent and one exact stash object.
  Substituting another repository state fails those comparisons and requires a
  new run.
- Adversarial read: PASS. The independent read found the exact Git scope
  supported and found no mathematical overclaim.

### Item 0.2

- Definitional: no mathematical proposition is claimed. Command execution on
  the frozen commit is the acceptance criterion.
- Built in: separate compilers, assumption tools, vacuity probes, tests,
  synthesis, and Git checks executed rather than trusting this report.
- Vacuity: the isolated build began after the exported compiled Coq artifacts
  were removed and ended with all 446 frozen source-object pairs present. The
  full vacuity manifest also evaluated 772 theorem targets with zero vacuous
  or error result.
- Swap test: every check is bound to `5d1245e6` and its exact submodules. A
  different commit or source manifest requires another run.
- Adversarial read: PASS. The independent read found the gate and rebuild
  scope supported, the failed attempt disclosed, and the final Part 0 sentence
  no broader than the evidence.

## Calls made

- The operational meaning of PROVED is used only for Items 0.1 and 0.2, as
  frozen. Later theorem items receive no such exception.
- The first Part 0 attempt remains technical evidence, not protocol closure.
- The Part 1 stash remains preserved and quarantined through Part 0.
- The first isolated rebuild failure is a recorded failed attempt. Repairing
  an external shell continuation was a retry on the same frozen input, not a
  reason to edit or weaken a gate.
- Failed and successful temporary exports are retained as evidence. No broad
  cleanup command was used.
- Guard timing and peak-memory values come from the captured caller transcript;
  payload-log hashes authenticate payload output. They are not presented as if
  they occupied the same file.

## Wrong predictions

Neither frozen outcome prediction was wrong. The first rebuild runner failed,
but that mechanical attempt did not refute the predicted Item 0.2 outcome. The
unchanged frozen check passed after the runner syntax was repaired.

## Final Part 0 sentence

Part 0 closes only the ordered baseline: Item 0.1 is PROVED operationally by
commit `5d1245e6`, and Item 0.2 is PROVED operationally by the enumerated green
gates and isolated 446-source rebuild on that exact commit. This establishes
repository state and reproducible execution evidence, not a mathematical
claim about the Thiele Machine.
