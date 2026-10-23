# Native reproduction

The repository supports a source-only native rebuild of the formal project. It uses the checked-out sources, pinned dependency trees, and the locally installed toolchain. It does not install packages, download sources, invoke a container runtime, or reuse compiled proof objects from the checkout.

## Prerequisites

Install the native tools used by the gate: Python 3, GNU make, Coq 8.18 with the standard library, CSDP, OCaml with `ocamlfind`, and MetaCoq 1.2.1 for Coq 8.18, which the vendored L extraction tactics need (`scripts/install_metacoq.sh` builds it from pinned, checksum-verified source and installs it; it needs Coq-Equations and the Coq OCaml development libraries).

## Fresh source-only run

From the repository root:

```sh
python3 scripts/reproduce_coq.py
```

The runner creates a fresh directory under `artifacts/reproduction/`, which is ignored by Git. Use `--output PATH` to choose a location outside the source tree. It copies the active Coq sources, the small-machine sources in `minimal/`, the pinned undecidability library, and the explicit build configuration. It records the input hashes, tool paths and hashes, commands, exit codes, selected probes and checked libraries.

The default run regenerates the project Makefile, builds the vendored undecidability modules the project imports, builds the full active Coq project, and invokes dependency-enabled `coqchk` on every module. `--probe REPO_PATH.v` adds a probe file to compile against the built tree, and `--library Logical.Name` replaces the default list of checked libraries. `--jobs N` sets the parallel build width (by default the number of processors, capped at four, or `THIELE_REPRO_JOBS` capped at four). `--prepare-only` records the snapshot and commands without running the checks and is not a passing result.

A failed run can resume only from its captured snapshot:

```sh
python3 scripts/reproduce_coq.py --resume \
  --output artifacts/reproduction/RUN_DIRECTORY
```

Resume verifies the captured source and native tool hashes. A source change requires a fresh run.

## Incremental checkout build

For development in the checkout:

```sh
make coq-gate
```

`make coq-gate` builds incrementally (`make -C coq -j1`) and does not remove stale Coq outputs. Tracked or cached `.vo`, `.glob` and generated Makefile files can survive a source change and invalidate the dependency check, so after pulling run `make coq-clean` first, which removes the `.vo`, `.vos`, `.vok`, `.glob` and `.aux` files under `coq/` and `minimal/`; the continuous-integration workflow does the same. The clean proof gate and the reproducibility scripts also remove the generated Makefile, regenerate it, and expose the first compiler diagnostic before building.

## Parallelism and the assumption receipt

The clean proof gate and the fresh source-only reproduction use bounded parallel rebuilds, by default at most four jobs. `THIELE_PROOF_JOBS` and `THIELE_REPRO_JOBS` can lower that width on a runner with a smaller memory or CPU budget; both are capped at four, and `scripts/reproduce_coq.py --jobs N` sets the reproduction's width directly. The full assumption receipt likewise uses up to four parallel `coqtop` batches by default (`THIELE_ASSUMPTION_JOBS` can lower it and is capped at four), while validating every query and publishing only a complete result. Each batch has a 900-second limit; on a two-core machine set `THIELE_ASSUMPTION_BATCH_SIZE=500` or raise `THIELE_ASSUMPTION_TIMEOUT`. `THIELE_ASSUMPTION_WORK_DIR` keeps validated batch results, so an interrupted run resumes (use a path such as `build/probe/assumption-batches-resume`, which Git already ignores); a saved batch is reused only when it ran exactly the queries the current probe would run.

## Recorded output

A successful run writes `result.txt` only after every requested stage passes and the captured inputs remain unchanged. Other files in the run directory are execution records: `source-manifest.json`, `reproduction.json`, tool versions, stage logs, and checker logs. They are reproducible evidence for that run and belong to no source tree.

## Finite transition-system checks

Run the independent small-system search from the repository root:

```sh
python3 scripts/break_it.py
```

It uses the Python standard library. For the finite scopes below it enumerates transition maps, readings, starts and prefixes as applicable; the probabilistic and unitary cases use sampled inputs. Each check compares the conclusion with the stated premises. Controls remove selected premises and exhibit cases where the conclusion fails. The manuscript supplies the general arguments; these searches exercise their finite instances.

The table records the search scopes and reported outcomes. Run the command above to obtain a result for the current sources.

| Result | Scope | Reported failures | Control |
| --- | --- | --- | --- |
| Step law | every map on up to 6 states, every start | none | one next state: fails |
| Merge or a fresh state (1) | every map, every reading it keeps, every start, up to 6 states | none | permanence, one rule: both fail |
| Merge or a fresh state (2), the exact bound | every map, reading, set of starts and T, up to 5 states; the bound reached | none | no merge: fails |
| Permanent flip merges, toll from merge pricing | every map and every reading it keeps, up to 6 states | none | finiteness, permanence, merge pricing: all fail |
| Merge or revoke | every map and reading, up to 6 states | none | finiteness: fails |
| Reversible keeps nothing | every one-to-one map, reading and start, up to 6 states | none | finiteness, one-to-one: both fail |
| Floor and one unit per crossing | every system of two moves on up to 3 states, prices 0 to 2, runs up to 5 | none | the toll: fails |
| No price per move name meets floor and ceiling once the flag rises | the same systems, runs up to 3 | none | state-dependent price: meets both |
| Squeeze bound | every map and kept reading, up to 6 states | none | permanence: fails |
| Least halving price is the log of the largest pile | every map and every list of states, up to 5 states | none | — |
| Own narrowing priced | every pair of moves on up to 3 states, runs up to 3, every list of starts | none | halving price: fails |
| Entropy ceiling | every map on up to 4 states, random spreads | none | permanence: fails |
| Noisy steps | 400 random tables per size, 2 to 4 states, every closed set | none | columns add to one: fails |
| Unitary steps | 200 random unitaries per size, dimensions 2 to 4 | none | unitary: fails |
| Heat against time | 999 values of p, distances up to 60 | none | — |
| Teaching at zero cost | every zero-cost machine on up to 3 states, every window | none | — |
| No level holds its questions | every assignment on up to 3 states | none | — |
| Certainty bound | every pair of moves on up to 3 states, runs up to 3, random two-valued windows and random spreads | none | halving price: fails |
| Every scale pays the same way | every fine machine on up to 4 states, every described set and coarse description | none | staying inside, finiteness: both fail |

The unitary checks can detect arithmetic errors in preservation of orthogonality; their control uses an invertible map that is not unitary. The heat/time check evaluates the displayed formula. Infinite-state controls are examined on finite prefixes; the infinite claims use the manuscript's arguments. For the floor-and-ceiling result, an instruction-name price cannot charge once for a raise and then make repetitions free: charging by source state provides the stated alternative.
