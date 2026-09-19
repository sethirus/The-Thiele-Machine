# Historical reproduction evidence — superseded workflow

The container workflow is retired. Use
[scripts/reproduce_coq.py](../../scripts/reproduce_coq.py) and
[NATIVE_REPRODUCTION.md](NATIVE_REPRODUCTION.md) for all future reproduction.
No image, daemon or container step is required.

The evidence below describes earlier runs only. Their recorded outcomes and
hashes remain historical evidence; they are not instructions to repeat that
workflow or certification of the current source.

## Execution evidence

The first source-only attempt is preserved at
`/workspaces/revision-snapshots/20260912-container-retirement`. Its vendor build
exited 2 because `Kami/Ext/Extraction.v` could not write
`Kami/Ext/Ocaml/Target.ml`: the copier had omitted that output directory. This
was a reproduction packaging prerequisite failure, not a failed proof. Its
`reproduction.json`, manifest and raw logs retain the failure. The runner now
creates that directory before building. The active explicit extraction paths
in the source tree were enumerated; the existing `build/kami_hw` directory
creation covers the other required destinations.

A fresh attempt at
`/workspaces/revision-snapshots/20260912-container-retirement-retry` copies no
compiled objects from the first attempt or the host. It also includes the
final comment correction in `VerilogSemantics.v`; the first manifest predates
that correction. Consult each attempt's recorded exit status rather than
interpreting the existence of its output directory as success.

The second attempt passed both full vendor builds but stopped at
`AlgebraicCoherence.v` because the base image lacked `csdp`. The project already
lists `coinor-csdp` in its CI dependencies. That failure and exit 2 remain in the
second attempt's logs. The historical image added the missing prerequisite without changing a proof.
The native workflow checks for the locally installed CSDP executable.

The third attempt, `20260912-container-retirement-csdp`, was intentionally
cancelled during early dependency compilation to capture the final comment-only
correction in `CanonicalCPUProof.v`. Its raw process exit and cancellation note
are retained. The fourth attempt, `20260912-container-final-csdp`, captures the
final frozen proof sources and rebuilds from a fresh source-only directory.

The fourth attempt passed the vendor builds, then exhausted the base image's
8 MiB native stack at `VerilogRefinement.v:669`. Its exit 2 and raw diagnostic
are retained. The final supplemental stage records a 64 MiB native stack and
`OCAMLRUNPARAM=l=64M`; these adjust process resources without changing the
proof or disabling checking.

The original copier also omitted `coq/Makefile.local`, which removes the
unwanted generated `Top` root namespace and now enforces canonical extraction
ordering. The future runner includes this file. The final supplemental stage
archives the initial inputs and outputs, snapshots all final inputs including
that configuration and `MorphCopy.v`, removes only container-created project
compiled objects, and rebuilds the complete project. Vendor inputs are checked
byte-for-byte against their successfully source-built versions before retaining
those vendor objects. That supplemental stage was configured to run seven theorem
probes, dependency-enabled `coqchk` on six selected libraries, and the canonical
extraction comparison. It was intentionally cancelled during the project build
to include a locally verified, statement-preserving simplification of the
expensive cost proof and additional completed FSM modules; those configured
checks did not run in that cancelled stage. Its report distinguishes this stage from earlier failed
or cancelled attempts. No host compiled object is copied into any stage.

The completed `supplemental-final-v2` stage passed its full project rebuild,
ten theorem probes, nine-library dependency-enabled `coqchk`, and canonical
extraction check (exit 0). All eight generated outputs match the saved
pre-dispatch-fix host reference. This is a **pre-dispatch-fix checkpoint**:
`ThieleCPUCore.v` changed afterward to fix invalid-version MORPH dispatch, so
these results do not cover that later change. The report deliberately retains
the mismatch against the later host extraction alongside the successful
comparison against the saved applicable reference. See
`container_reproduction_report.json` for the exact manifest, image and logs.
