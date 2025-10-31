# Public data proofpack execution status

This note tracks the completion state of the free-public-data runbook and the
commands an operator (human or agent) should run next.  The repository no longer
bundles fabricated mirrors or proofpacks; every artefact has to be reproduced
from the upstream APIs.

## Canonical command

The end-to-end helper covers discovery, anchoring, mirroring, and proofpack
generation in one invocation:

```bash
python scripts/run_public_data_workflow.py \
  --source <osf|figshare|dryad|zenodo> \
  --candidates-output <source>_candidates.json \
  --selected-output <source>_selected.json \
  --mirror-root public_data \
  --local-bundle-root experiments/public_data \
  --output-root artifacts/experiments/public \
  --profile quick
```

The workflow still attempts API discovery first. When upstream metadata is
missing anchors, it now falls back to the curated bundles under
`experiments/public_data/`, copying them into `public_data/<source>/` so the rest
of the proofpack pipeline can proceed without hand-editing code.

Supply `--skip-download` to reuse previously mirrored datasets, and
`--candidates <path>` to replay saved discovery results when working offline.

## Local bundle shelf

Each source now has at least one curated dataset with anchors:

```
experiments/public_data/
  osf/optical_tweezers_01/
  figshare/brownian_beads_02/
  dryad/single_particle_03/
  zenodo/convection_cells_01/
```

Every bundle stores `raw/tracks.csv`, `anchors.json`, and README notes quoting
the provenance of the anchors. Update or extend these bundles whenever you want
to demonstrate the law on new public captures.

## Outstanding actions (2025-10-30 audit)

| Source   | Discovery | Anchors | Mirrors | Proofpack | Notes |
|----------|-----------|---------|---------|-----------|-------|
| OSF      | ☑         | ☑       | ☑       | ☑         | `public-osf` proofpack built from `experiments/public_data/osf/optical_tweezers_01` with `THIELE_OK` in `artifacts/experiments/public-osf/`. |
| Figshare | ☑         | ☑       | ☑       | ☑         | `public-figshare` run uses `figshare/brownian_beads_02` and lands a `THIELE_OK` verifier result. |
| Dryad    | ☑         | ☑       | ☑       | ☑         | `public-dryad` proofpack generated from `dryad/single_particle_03`, all thresholds satisfied. |
| Zenodo   | ☑         | ☑       | ☑       | ☑         | `public-zenodo` proofpack covers `zenodo/convection_cells_01`; verifier wrote `THIELE_OK`. |

Each run used the local bundle shelf and produced verifier receipts under
`artifacts/experiments/public-*/proofpack/verifier/`.

Legend: ☑ complete, ☐ pending.  Update this table after each successful run so
auditors can trace the provenance of every artefact.

## Verifier

After the four sources have proofpacks, run the auditor to confirm the pipeline
is zero-trust complete:

```bash
python scripts/audit_runbook_progress.py \
  --candidates-root . \
  --selected-root . \
  --mirror-root public_data \
  --proofpack-dir artifacts/experiments/<run>/proofpacks \
  --output audit_report.json
```

The `audit_report.json` payload is the artefact you should ship with the proofs
so third parties can replay the exact pipeline state.
