# Turbulence mirror inventory

This directory tracks the deterministic JHTDB slices that feed the turbulence
proofpack pipeline. Each slug corresponds to a mirrored directory under
`archive/jhtdb/<slug>/` containing a canonical `jhtdb_samples.json` fixture and
associated manifest.

- `allowlist.json` — default, expanded, and rotation allowlists consumed by
  `scripts/run_proofpack_pipeline.py` and the public-data workflow. The
  `default` set keeps the CI smoke runs bounded, while `expanded` enumerates the
  higher-budget mirrors available for scheduled runs. Rotation schedules (for
  example `expanded_nightly`) interleave the small-budget baselines with the
  high-budget mirrors so nightly automation can exercise every payload on a
  rolling cadence by passing
  `--turbulence-rotation-schedule expanded_nightly` (and optionally a
  deterministic `--turbulence-rotation-index`).
- `isotropic1024_16pt/` — 7 temporal slices × 16 spatial points extracted from
  the isotropic 1024 run (points spaced at 0.05 grid units).
- `isotropic1024_20pt/` — 7 temporal slices × 20 spatial points with expanded
  radial coverage for intermediate Reynolds snapshots.
- `isotropic1024_24pt/` — 8 temporal slices × 24 spatial points capturing the
  high-budget regression payload.

Mirrors are stored under `archive/jhtdb/<slug>/` for reproducibility. To include
an expanded budget in a local run, pass `--profile-config` with a
`turbulence_allowlists` entry or specify `--turbulence-dataset <slug>` on the
CLI.
