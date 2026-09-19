# Native source-only reproduction

Build from repository sources with native tools. No container runtime or global
Coq library installation is required.

From the repository root:

```sh
python3 scripts/reproduce_coq.py --jobs 1
```

The default output is a new timestamped directory under `artifacts/reproduction/`.
Use `--output PATH` to choose another fresh directory. The source checkout and
its staged changes are left intact. The runner copies `.v` sources and explicit
build configuration, including the vendored bbv, Kami and pinned MM2 library.
It copies no proof objects, native libraries or generated makefiles. Dependencies
are rebuilt and selected through the copied tree's own `COQPATH`.

Native prerequisites are Python 3, GNU make, Coq 8.18 and its standard library,
OCaml and CSDP (`csdp`). The runner does not install or download them. The
repository contains project/dependency sources and the reproduction procedure;
it does not bundle an operating system or compiler. Missing prerequisites are
reported explicitly.

The runner builds bbv, Kami and the entire project, runs seven contract probes
covering CM2, dispatch, CoreExecution, dispatch observation/abstraction, the
arbitrary-operand ADD family, the concrete cast regression, and corrected
specialization. Dependency-enabled `coqchk` covers CM2Limitative,
CM2Applicability, DispatchContracts, DispatchReset, CoreExecution,
DispatchAbstractionBridge, DispatchAddFamily and VMUnboundedCM2Specialization.
CoreTyping is included through the typed dispatch bridge's dependencies.
Repeat `--probe REPO_PATH.v` and `--library Logical.Name` to select other checks.
Specifying either option replaces that option's defaults.
`--prepare-only` creates the input snapshot and command record without executing
them; its `prepared` status is not a passing reproduction.

An interrupted or failed run can resume with:

```sh
python3 scripts/reproduce_coq.py --resume --output artifacts/reproduction/RUN_DIRECTORY
```

Resume verifies the captured source and native tool hashes, retains failed logs,
and skips successful stages. A source change requires a fresh snapshot. Resume
checks the captured tree; it does not add later checkout changes to that tree.

Each run records:

- `source-manifest.json`: input hashes and sizes, captured before compilation.
- `reproduction.json`: commands, per-command exit codes, tool paths and hashes,
  source mutations, selected probes/libraries and final status.
- `tool-versions.log` and individual build/probe/checker logs.
- `result.txt`: created only after all requested checks pass with no input change.

The process has a 64 MiB stack where the native hard limit permits, and uses
`OCAMLRUNPARAM=l=64M` for existing large proof terms. These resource settings do
not bypass proof checking. The runner replaces inherited `COQPATH` rather than
reusing the checkout's compiled dependencies. It neither runs network commands
nor claims operating-system network isolation.

A fresh local build checks reproducibility from source with the recorded native
toolchain. It is not an independent reviewer or a second operating environment.
Under Devon's 2026-09-14 contract amendment, a second machine and an independent
reviewer are optional follow-up checks, not mandatory delivery gates. Earlier evidence is retained in
`CONTAINER_REPRODUCTION.md` solely as history; that workflow is superseded.
