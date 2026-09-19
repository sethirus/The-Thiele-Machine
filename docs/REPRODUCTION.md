# Native reproduction

The repository supports a source-only native rebuild of the formal project.
It uses the checked-out sources, pinned dependency trees, and the locally
installed toolchain. It does not install packages, download sources, invoke a
container runtime, or reuse compiled proof objects from the checkout.

## Prerequisites

Install the native tools used by the gate: Python 3, GNU make, Coq 8.18 with
the standard library, OCaml, `ocamlfind`, and CSDP. The RTL gates additionally
use `iverilog`, `verilator`, and/or `yosys` as required by the selected
workflow.

## Fresh source-only run

From the repository root:

```sh
python3 scripts/reproduce_coq.py --jobs 1
```

The runner creates a fresh directory under `artifacts/reproduction/`, which
is ignored by Git. Use `--output PATH` to choose a location outside the source
tree. It copies the active Coq sources, vendored bbv, Kami, the pinned
Undecidability library, explicit build configuration, and the probe sources
from [`tests/coq_probes/`](../tests/coq_probes/). It records the input hashes,
tool paths and hashes, commands, exit codes, selected probes and checked
libraries.

The default run builds bbv and Kami, regenerates the project Makefile, builds
the full active Coq project, runs the contract probes, and invokes
dependency-enabled `coqchk`. `--probe REPO_PATH.v` and `--library
Logical.Name` replace the respective defaults. `--prepare-only` records the
snapshot and commands without running the checks and is not a passing result.

A failed run can resume only from its captured snapshot:

```sh
python3 scripts/reproduce_coq.py --resume \
  --output artifacts/reproduction/RUN_DIRECTORY
```

Resume verifies the captured source and native tool hashes. A source change
requires a fresh run.

## Incremental checkout build

For development in the checkout:

```sh
export COQPATH="$PWD/vendor/bbv/src:$PWD/vendor/kami"
make -C vendor/bbv
make -C vendor/kami
make coq-gate
```

The CI and reproducibility scripts remove stale Coq outputs, regenerate the
project Makefile, and expose the first compiler diagnostic before building.
This is required because tracked or cached `.vo`, `.glob`, and generated
Makefile files can otherwise survive a source change and invalidate the
dependency check.

## Recorded output

A successful run writes `result.txt` only after every requested stage passes
and the captured inputs remain unchanged. Other files in the run directory
are execution records: `source-manifest.json`, `reproduction.json`, tool
versions, stage logs, and checker logs. They are reproducible evidence for
that run, not additional source files.
