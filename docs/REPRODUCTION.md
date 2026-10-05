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

The default run regenerates the project Makefile, builds the vendored undecidability modules the project imports, builds the full active Coq project, and invokes dependency-enabled `coqchk` on every module. `--probe REPO_PATH.v` adds a probe file to compile against the built tree, and `--library Logical.Name` replaces the default list of checked libraries. `--prepare-only` records the snapshot and commands without running the checks and is not a passing result.

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

The CI and reproducibility scripts remove stale Coq outputs, regenerate the project Makefile, and expose the first compiler diagnostic before building. The clean proof gate and the fresh source-only reproduction use bounded parallel rebuilds, capped at four jobs. Set `THIELE_PROOF_JOBS` or `THIELE_REPRO_JOBS` when a runner has a different safe memory/CPU budget. The full assumption receipt likewise uses up to four parallel `coqtop` batches by default (`THIELE_ASSUMPTION_JOBS` overrides it), while validating every query and publishing only a complete result. Each batch has a 900-second limit; on a two-core machine set `THIELE_ASSUMPTION_BATCH_SIZE=500` or raise `THIELE_ASSUMPTION_TIMEOUT`. `THIELE_ASSUMPTION_WORK_DIR` keeps validated batch results, so an interrupted run resumes (use a path such as `build/probe/assumption-batches-resume`, which Git already ignores); a saved batch is reused only when it ran exactly the queries the current probe would run. This is required because tracked or cached `.vo`, `.glob`, and generated Makefile files can otherwise survive a source change and invalidate the dependency check.

## Recorded output

A successful run writes `result.txt` only after every requested stage passes and the captured inputs remain unchanged. Other files in the run directory are execution records: `source-manifest.json`, `reproduction.json`, tool versions, stage logs, and checker logs. They are reproducible evidence for that run, not additional source files.
