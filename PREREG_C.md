# PREREG_C: GWOSC blind test of Δ(µ) vs GR (scaffold)

Date (UTC): 2025-12-18

Goal
- Build a receipt-verifiable pipeline that (1) reproduces standard event metadata sanity checks, then (2) evaluates a preregistered Δ(µ) model against GR on held-out GW events.

This file locks the prereg structure. The Δ(µ) waveform/phase model must be specified before running the blind test stage.

## Locked catalog source

- GWOSC Event API (GWTC releases)
- The chosen GWTC release name must be recorded in MANIFEST_C.json.

Phase 1 (implemented): catalog metadata ingest
- Tool: tools/prereg_c_gwosc_catalog.py
- Stages: init -> fetch -> analyze
- Artifacts: MANIFEST_C.json, events.jsonl, DATA_C_INDEX.json, analysis_C.json

## Locked split

- Chronological split:
  - Train: earlier events by GPS time
  - Test: later events
- The split cutoff rule must be deterministic and recorded in MANIFEST_C.json.

## Locked statistic (placeholder)

Choose exactly one statistic before any model evaluation:
- Bayes factor between GR and Δ(µ) model, OR
- Best-fit Δ(µ) parameter constraint interval (must exclude 0 to claim non-GR).

## Deliverables

- PIPELINE_C/ code + environment lockfile
- MANIFEST_C.json + hashes
- REPRO_C.md one-command reproduction
- FIG_C.png summary across held-out events
