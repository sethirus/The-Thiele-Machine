# Thiele Machine experiments package

This package is the staging area for the zero-trust experiment runners
that synthesize μ-ledger proofpacks. Each module is required to:

- emit deterministic CSV logs and ancillary artifacts that can be
  recomputed byte-for-byte;
- avoid dynamic code generation or network dependencies;
- provide CLI entry points so verifiers can re-run with the same
  configuration.

The canonical implementation order matches the experiment prompt:

1. `run_landauer.py`
2. `run_einstein.py`
3. `run_cwd.py`
4. shared utilities (ledger adapters, seeding helpers, plotting)
5. archivist and red-team modules that package and stress proofpacks

The shared utilities now include `ledger_io.py`, which provides deterministic
JSONL helpers used by the builders, auditors, and archivists to move μ-ledger
rows between phases without introducing hidden state.

### Implemented components

| Module | Role | Notes |
| --- | --- | --- |
| `run_landauer.py` | Builder (Phase A1) | Four-state Ising surrogate with deterministic Metropolis kernel, μ-ledger outputs, and CLI entry point. |
| `run_einstein.py` | Builder (Phase A2) | Biased diffusion simulator that records drift/mobility snapshots for the Einstein relation. |
| `run_entropy.py` | Builder (Phase A3) | Entropy-identity extension logging μ/entropy deltas, cumulative series, and monotonicity diagnostics. |
| `run_cwd.py` | Builder (Phase B1) | Multi-module compositional work decomposition runner with sighted/blind/destroyed protocols, penalty logging, and mutual-information diagnostics. |
| `run_cross_domain.py` | Builder (Phase C) | Compression/LDPC microbenchmarks with sighted/blind/destroyed variants that log μ and runtime echoes for cross-domain verification. |
| `ledger_io.py` | Shared | JSONL load/store/digest helpers shared across roles. |
| `proofpack.py` | Archivist | Builds manifests, protocol summaries, and Ed25519-signed receipts for proofpacks. |
| `tools/proofpack_bundler.py` | Archivist | CLI that runs the unified verifier, copies deterministic artefacts, and emits summary, protocol, manifest, and receipt bundles. |
| `red_team.py` | Falsifier | Deterministic perturbations that trigger the verifier failure modes mandated by the prompt. |
| `data_sources/osf.py` | Discovery | OSF API client that lists candidate projects/files matching the optical tweezers & SPT queries mandated by the public-data runbook. |
| `data_sources/figshare.py` | Discovery | Figshare search helper that groups article hits, fetches file metadata once per record, and filters to deterministic raw-data extensions. |
| `data_sources/dryad.py` | Discovery | Dryad HAL client that follows dataset → version → files links to emit per-identifier manifests with download URLs and checksums. |
| `data_sources/zenodo.py` | Discovery | Zenodo query helper that rehydrates creators/DOIs and filters record files to the whitelisted extension set. |
| `data_sources/download.py` | Discovery | Deterministic mirroring of anchored candidates with SHA-256 manifests and preserved provenance for proofpack ingestion. |
| `data_sources/anchors.py` | Discovery | Regex-driven anchor extraction for temperature, pixel scale, and frame interval with provenance capture for protocol documentation. |
| `scripts/run_proofpack_pipeline.py` | Orchestrator | Executes the canonical builder commands, enforces artefact layout, and runs the bundler to generate proofpacks end-to-end. |
| `scripts/discover_public_candidates.py` | Discovery CLI | Unified wrapper that can enumerate OSF, Figshare, Dryad, or Zenodo candidates with consistent query/extension controls. |
| `scripts/filter_public_candidates.py` | Anchoring CLI | Filters discovery outputs to entries with complete fit-free anchors, preserving quoted metadata for protocol.json generation. |
| `scripts/download_public_files.py` | Retrieval CLI | Downloads anchored candidates, writes manifests, and emits dataset summaries for the zero-trust pipeline. |

### Auditor harnesses

| Script | Coverage | Notes |
| --- | --- | --- |
| `verifier/check_landauer.py` | Phase A1 | Recomputes μ/work aggregates from the ledger, enforces the Landauer balance within ε, and validates metadata digests. |
| `verifier/check_einstein.py` | Phase A2 | Recomputes diffusion/mobility/residual metrics directly from step logs and requires `|D - μ k_B T| ≤ δ` per trial. |
| `verifier/check_entropy.py` | Phase A3 | Replays μ/entropy samples to recompute Theil–Sen slopes, intercepts, and Spearman diagnostics while enforcing the identity thresholds. |
| `verifier/check_cwd.py` | Phase B1 | Cross-checks sighted/ blind/ destroyed summaries, validates mutual-information bounds, and confirms penalty equality across protocols. |
| `verifier/check_cross_domain.py` | Phase C | Reconstructs domain-level regressions, verifies sighted flatness, blind exponential advantage (ΔAIC), and structure integrity digests. |
| `tools/thiele_verifier.py` | Unified | Aggregates all phase verifiers, writes `proofpack_verifier.json`, and records a `THIELE_OK`/`THIELE_FAIL` flag for proofpack directories. |

### Unified proofpack verification

Run the aggregated verifier with

```bash
python -m tools.thiele_verifier path/to/proofpack
```

The script scans for Landauer, Einstein, entropy, CWD (sighted/blind/destroyed),
and cross-domain (sighted/blind/destroyed) artefacts, dispatches to the
phase-specific checkers, persists their JSON payloads under
`<proofpack>/verifier/`, and writes a combined
`proofpack_verifier.json`.  Successful runs print `THIELE_OK`, emit a
`verifier/THIELE_OK` marker (removing any stale `THIELE_FAIL` flag), and exit
with code 0; any missing artefacts or threshold violations trigger a non-zero
exit, record a `verifier/THIELE_FAIL` marker, and the aggregated report
highlights the failing phase.

The Landauer runner writes three artefacts into the selected output
directory:

1. `landauer_steps.jsonl` – per-step μ-ledger rows with work, bias, and spin
   snapshots;
2. `landauer_summary.csv` – trial-level aggregates used by auditors;
3. `landauer_metadata.json` – run configuration metadata with the ledger
   digest for archivists.

Each run accepts `--protocol` (`sighted`, `blind`, or `destroyed`) and a
`--synthetic-ledger` flag that can replay fixtures without executing the
simulation.

The Einstein runner mirrors this structure with protocol-sensitive force
schedules and drift-aware logging. It writes:

1. `einstein_steps.jsonl` – per-step μ-ledger rows with applied force,
   displacement, and accumulated work units;
2. `einstein_summary.csv` – trial aggregates including diffusion, mobility,
   and the Einstein residual `D - μ k_B T`;
3. `einstein_metadata.json` – configuration snapshot with ledger digest.

The entropy runner extends the biased diffusion protocol to log per-step
entropy changes alongside μ-answer increments. In addition to the standard
ledger, it emits a cumulative series CSV so auditors can recompute
Theil–Sen slopes, intercepts, and correlation diagnostics.

The CWD runner introduces the Phase B1 multi-module experiments. It
records per-step μ-answer increments, policy actions, success flags, and
penalty bits so auditors can recompute the decomposition equality and the
mutual-information penalty bound across sighted/blind/destroyed
protocols. Each invocation produces:

1. `cwd_steps.jsonl` – the μ-ledger rows with module identifiers,
   policy actions, penalty bits, and cumulative work taps;
2. `cwd_summary.csv` – aggregated metrics including mutual information,
   penalty totals, and average success rates per trial;
3. `cwd_metadata.json` – run configuration snapshot augmented with the
   ledger digest for archivists.

Landauer, Einstein, entropy, and CWD fixtures are stored under `experiments/data/`
so the `--synthetic-ledger` flag can replay deterministic JSONL captures
during testing.

The cross-domain runner covers Phase C. It constructs deterministic
compression and LDPC surrogates whose sighted traces remain flat, blind
variants display exponential runtime growth, and destroyed controls lose
their structural advantage. Artefacts include:

1. `cross_domain_steps.jsonl` – per-step μ-ledger entries with cumulative
   μ and runtime traces and protocol-specific structure scores;
2. `cross_domain_summary.csv` – per-trial aggregates with domain-level
   slope confidence intervals and ΔAIC diagnostics;
3. `cross_domain_metadata.json` – configuration snapshot with the ledger
   digest hash.

Deterministic cross-domain fixtures live under `experiments/data/`,
including `sample_cross_domain.jsonl` for synthetic replay tests.

### External dataset discovery and mirroring

Phase E of the roadmap requires wiring the pipeline to public repositories. The
discovery helpers under `experiments/data_sources/` cover each source in the
runbook:

- `osf.py` (OSF search API),
- `figshare.py` (Figshare v2 articles),
- `dryad.py` (Dryad HAL datasets → versions → files), and
- `zenodo.py` (Zenodo records endpoint).

Use `scripts/run_public_data_workflow.py` to execute the entire loop for a
single source:

```bash
# Discover, filter, mirror, and run the proofpack pipeline for OSF data.
python scripts/run_public_data_workflow.py \
  --source osf \
  --candidates-output osf_candidates.json \
  --selected-output osf_selected.json \
  --mirror-root public_data \
  --local-bundle-root experiments/public_data \
  --output-root artifacts/experiments/public \
  --profile quick
```

When discovery fails to surface complete anchors, the workflow now copies the
curated bundles under `experiments/public_data/` into the mirror root so the
remaining phases (protocol runs, verifier, bundler) can complete deterministically.

The command:

1. Queries the remote API with the runbook search terms and writes
   `<source>_candidates.json` if `--candidates-output` is supplied.
2. Filters the payload to candidates that expose fit-free anchors (temperature,
   pixel scale, and frame interval) and emits `<source>_selected.json` when
   `--selected-output` is provided.
3. Mirrors the anchored datasets into `public_data/<source>/<slug>/`, writing a
   `candidate.json`, `anchors.json`, `raw/` payloads, and a deterministic
   `MANIFEST.json` that is verified immediately after the download completes.
4. Invokes `scripts/run_proofpack_pipeline.py` so the public data ends up under
   `artifacts/experiments/.../proofpacks/public_data/<source>/<slug>/` with
   ledgers, protocol metadata, and verifier output.

The workflow supports `--skip-download` (reuse existing mirrors),
`--max-datasets` (limit the number of anchored selections), and direct
`--candidates` input so auditors can replay previously captured discovery
results offline. All HTTP requests stream through a single `requests.Session`
and honour `--timeout`/`--chunk-size` arguments for deterministic mirrors.

> **Current status:** the repository no longer ships fabricated public-data
> mirrors or proofpacks. Run the workflow for each source to populate the
> directories before invoking the unified auditor. The outstanding steps for
> each source are tracked by `scripts/audit_runbook_progress.py`.

### JHTDB sampling (Phase E optional dataset)

Use `experiments.data_sources.jhtdb` to fetch a small turbulence trajectory budget:

1. Create a minimal request JSON with `dataset`, `field`, `times`, `points`, and optional `extra_payload` keys.
2. Run `python scripts/sample_jhtdb.py --config jhtdb_request.json --output-dir mirrored/jhtdb/<slug>` to materialise
   `jhtdb_samples.json` and a matching `manifest.json` that records the SHA-256 digest.
3. Archive only the manifest; the raw JSON sample remains outside the repository but can be reproduced on demand.
   Tests mock the HTTP calls so the helper stays deterministic offline.

The stored manifest lets downstream agents confirm byte-stability before folding the turbulence sample into a proofpack. Two
mirrored fixtures live under `archive/jhtdb` for quick stress tests:

- `archive/jhtdb/isotropic1024_8pt/` — 5 temporal slices × 8 spatial points.
- `archive/jhtdb/isotropic1024_12pt/` — 6 temporal slices × 12 spatial points.
- `archive/jhtdb/isotropic1024_16pt/` — 7 temporal slices × 16 spatial points (expanded budget).
- `archive/jhtdb/isotropic1024_20pt/` — 7 temporal slices × 20 spatial points (expanded budget).
- `archive/jhtdb/isotropic1024_24pt/` — 8 temporal slices × 24 spatial points (high-budget regression set).

Both bundles include a `jhtdb_samples.json` payload and deterministic `manifest.json` digests so operators can replay the exact
sampling budget that exercises the verifier’s thresholds.

### Turbulence proofpack generator

`experiments.turbulence.protocol` consumes the mirrored `jhtdb_samples.json`, groups spatial points into coarse modules, and emits μ-ledgers, summaries, and SVG diagnostics for the sighted, blind, and destroyed protocols. The companion CLI

```bash
python scripts/run_turbulence_protocol.py mirrored/jhtdb/<slug> --output-dir proofpack/turbulence/<slug> \
    --protocol blind --seed 3
```

produces `ledgers/*.jsonl`, `summaries/*.json`, `protocol.json`, and `turbulence_metadata.json` that record anchor provenance and verifier thresholds. Auditors can replay the dataset via `verifier/check_turbulence.py`, which enforces the runbook tolerances (Spearman ≥ 0.9, blind ΔAIC ≥ 10, and a ≥0.2 drop in destroyed ρ) directly from the ledgers. The orchestration script `scripts/run_proofpack_pipeline.py` now detects mirrored turbulence samples automatically and the unified verifier reports their highlights alongside the existing phases. Default allowlists are sourced from `experiments/data/turbulence/allowlist.json` (covering the 8pt and 12pt smoke mirrors); supply `--turbulence-dataset <slug>` or add a `turbulence_allowlists` stanza to a profile config to include the expanded mirrors during local or scheduled runs. Use `--turbulence-protocol` (repeatable) and `--turbulence-seed` to scope smoke runs without editing profile definitions.

### Automation quickstart

1. **Audit runbook progress:**
   ```bash
   python scripts/audit_runbook_progress.py \
     --candidates-root . \
     --selected-root . \
     --mirror-root public_data \
     --proofpack-dir artifacts/experiments/<latest>/proofpacks \
     --output audit_report.json
   ```
   The JSON report records which runbook steps are complete for every source and
   highlights the remaining actions.

2. **Run public datasets end-to-end (per source):**
   ```bash
   python scripts/run_public_data_workflow.py --source osf --profile quick
   ```
   Repeat for `figshare`, `dryad`, and `zenodo`, adjusting `--mirror-root`,
   `--output-root`, and protocol flags as needed for nightly or high-budget
   profiles.
       --profile-config configs/proofpack_quick.yml
   ```
   The workflow discovers anchored datasets, mirrors files, executes the builders/verifiers, and bundles a proofpack summary. Pass `--turbulence-dataset <slug>` when mirrored JHTDB directories exceed the default allowlist and you want to run specific fixtures.
2. **CI-aligned smoke test:**
   ```bash
   make proofpack-smoke RUN_TAG=local-$(date -u +%Y%m%d%H%M%S)
   ```
   This mirrors the scheduled GitHub Actions job and emits a manifest digest under `artifacts/experiments/<RUN_TAG>/bundle`.
   The digest now appears in `RESULTS.md` so operators can compare CI fingerprints with local reruns.
3. **High-budget turbulence burn-in:**
   ```bash
   make proofpack-turbulence-high RUN_TAG=local-turb-$(date -u +%Y%m%d%H%M%S)
   ```
   Runs the proofpack pipeline against the allowlisted JHTDB mirrors, bundling verifier outputs and human summaries so CI can log runtime and margin observations.

Each run records the executed queries, timestamp, whitelisted extensions, and
candidate count alongside per-record metadata (titles, DOIs, contributors, file
hashes, and download URLs).  The original OSF-specific CLI remains available for
backwards compatibility, but the unified entry point keeps the zero-trust
discovery workflow consistent across repositories.

Anchoring metadata is parsed via `experiments/data_sources/anchors.py`, which
extracts the temperature, pixel scale, and frame interval directly from dataset
descriptions, converts units to Kelvin/µm/pixel/seconds, and records the
verbatim metadata lines for zero-trust provenance. The companion CLI
`scripts/filter_public_candidates.py` consumes a discovery JSON document and
emits `selected_candidates.json` that only includes entries with complete
anchors, quoting the metadata fragments that justify each value. Example usage:

```bash
python scripts/filter_public_candidates.py osf_candidates.json \
  --output osf_selected.json
```

The download stage is automated via `scripts/download_public_files.py`, which
mirrors each anchored candidate into `public_data/<source>/<slug>/`, writes
`candidate.json`/`anchors.json`, downloads all whitelisted files under a `raw/`
subdirectory, and emits a `MANIFEST.json` after recomputing SHA-256 hashes.
Example invocation:

```bash
python scripts/download_public_files.py osf_selected.json \
  --source osf \
  --output-dir public_data/osf \
  --report osf_download_report.json
```

The report summarises mirrored datasets and ensures manifests match the
filesystem. These mirrored directories provide the starting point for running
the sighted/blind/destroyed protocols against real public data.

### Single-particle tracking analysis

`experiments/public_data/spt_analysis.py` implements the first physics-facing
analytics module for public data proofpacks. The helpers

- parse anchored `anchors.json` payloads (`load_anchors`) including bead radius
  and medium viscosity so the diffusion anchor `k_B T / (6 \pi \eta r)` can be
  computed without hand tuning,
- stream raw trajectory CSV files into `TrackSeries` objects via `iter_tracks`,
  normalising coordinates into µm with the anchored pixel scale,
- estimate per-track diffusion constants from MSD slopes
  (`estimate_diffusion`),
- compare measured diffusion to the anchor prediction
  (`predicted_diffusion` / `diffusion_residuals`), and
- compute the held-out median absolute percent error required by the runbook
  (`oos_diffusion_error`).

Fixtures in `tests/data/public/` provide a deterministic micro dataset that
exercises these routines, while `tests/experiments/public_data/test_spt_analysis.py`
verifies the Stokes-based prediction, residual magnitudes, and the out-of-sample
error calculation. These utilities give the Builder and Auditor concrete tools
for checking the OSF/Figshare/Dryad/Zendodo single-particle tracking datasets
once mirrored.

### Public SPT proofpack runner

`experiments/public_data/spt_protocol.py` converts mirrored single-particle
tracking datasets into zero-trust proofpacks. The runner loads anchored
metadata, generates sighted/blind/destroyed ledgers (`ledgers/<protocol>.jsonl`),
records per-protocol summaries (`summaries/<protocol>.json`), emits
`public_spt_metadata.json`, `protocol.json`, and `oos_metrics.json`, renders
deterministic SVG diagnostics under `plots/<protocol>_*.svg`, and
enforces the runbook thresholds (Spearman ≥ 0.9 with p ≤ 1e-6 for sighted/blind,
ΔAIC ≥ 10 for blind, ρ drop and slope CI including 0 for destroyed, and OOS
median absolute percent error ≤ 10%).

The CLI entry point lives in `experiments/public_data/run_spt_protocol.py` and
mirrors the discovery/download tools:

```bash
python -m experiments.public_data.run_spt_protocol public_data/osf/<slug> \
  --output-dir proofpack/public_data/osf/<slug> \
  --seed 7
```

### Proofpack pipeline integration

`scripts/run_proofpack_pipeline.py` includes an optional `--public-data-root`
flag that scans mirrored datasets under `public_data/<source>/<slug>/`, runs the
anchored sighted/blind/destroyed protocols, and drops the resulting ledgers,
summaries, protocol metadata, and verifier payloads into the proofpack
directory. Profiles can now be sourced from a JSON/YAML document via
`--profile-config`, enabling operators to define additional argument grids (seed
lists, temperature schedules, trial counts, etc.) without editing code. The
orchestrator accepts repeated `--public-data-protocol` arguments to restrict
execution (defaults to all three) and `--public-data-seed` to keep the destroyed
shuffle deterministic. Example invocation combining simulation phases with a
mirrored OSF dataset:

```bash
python scripts/run_proofpack_pipeline.py \
  --output-root artifacts/experiments \
  --signing-key kernel_secret.key \
  --run-tag 2025-10-29-osf-demo \
  --profile quick \
  --profile-config configs/profiles.yaml \
  --public-data-root public_data \
  --public-data-seed 0
```

Profiles defined in the external document take precedence over the built-in
`quick`/`standard` presets and can introduce new profile names entirely. Each
entry maps a profile label to per-phase CLI argument sequences, matching the
command-line flags exposed by the experiment runners.

For operators who want to automate the full public-data loop, the repository
also ships `scripts/run_public_data_workflow.py`. The workflow script chains the
discovery helpers, anchoring filter, deterministic mirroring, proofpack
pipeline, and bundler into a single command:

```bash
python -m scripts.run_public_data_workflow --source osf \
  --candidates osf_candidates.json --output-root artifacts/experiments \
  --mirror-root public_data --signing-key kernel_secret.key
```

The script prints a JSON summary containing the manifest digest, run tag, and
bundle directory so CI systems can capture the proofpack fingerprint. It reuses
the same `--profile-config`, tolerance overrides, and public-data protocol
filters exposed by `run_proofpack_pipeline.py`.

When the proofpack is bundled, `tools/proofpack_bundler.py` calls the unified
verifier which now replays the public-data ledgers, enforces the ΔAIC/Spearman
and OOS thresholds, and records the outcomes in
`artefacts/verifier/public_spt_*.json`. The aggregated `summary.json` and
`summary.md` produced by the bundler therefore document both the synthetic
phases and any attached public datasets.

Repeated invocations are deterministic thanks to the seeded destroyed protocol
shuffle. Regression tests under
`tests/experiments/public_data/test_spt_protocol_runner.py` cover both the
programmatic API and the CLI wiring, while
`tests/verifier/test_public_spt.py` ensures the verifier catches threshold
violations.

### Proofpack archival helpers

The Archivist workflow lives in `proofpack.py`.  The module exposes

- `collect_manifest_entries` to gather SHA-256 digests and byte counts for
  selected artefacts,
- `write_manifest` to emit a canonical `manifest.json` with a global digest,
- `build_summary_payload`/`write_summary` to condense the unified verifier
  payload into a human-readable report, and
- `ReceiptSigner` + `write_receipt` to seal the manifest with an Ed25519
  signature compatible with the repository's `tools.receipts` validator.

The accompanying tests (`tests/experiments/test_proofpack.py`) exercise the
round-trip flow so archivists can trust the generated manifests and receipts.

`tools/proofpack_bundler.py` connects these helpers to the unified verifier. It

- recomputes verifier payloads via `verify_proofpack`,
- copies deterministic artefacts (ledgers, summaries, verifier JSON) into a
  bundle directory, and
- emits canonical `summary.json`, `protocol.json`, `manifest.json`, and
  `receipt.json` files with byte-stable ordering.

The bundler CLI runs with

```bash
python -m tools.proofpack_bundler path/to/proofpack \
  --signing-key path/to/ed25519_private.key \
  --output-dir path/to/bundle
```

Repeated invocations with the same inputs yield identical manifest and receipt
bytes, enabling cross-platform byte-stability audits (`tests/tools/test_proofpack_bundler.py`).

The bundler now writes an additional Markdown narrative (`summary.md`) using
`experiments.proofpack.render_human_summary`, folding the aggregated verifier
payload, manifest metadata, and recorded notes into a one-page report. Bundle
destinations must live under `artifacts/experiments/<run_tag>/…`; attempts to
write outside this hierarchy raise an error so the canonical archive layout is
preserved.

The Markdown renderer now promotes quantitative highlights from each verifier
payload (ΔAIC gaps, Landauer balance errors, Spearman correlations, penalty
margins, OOS errors, etc.) so auditors can confirm threshold compliance without
opening the raw JSON. SVG diagnostics emitted by the public-data runner are
pulled into the bundle automatically to accompany the textual summary.

### Runbook progress auditing

Use `scripts/audit_runbook_progress.py` to check the discovery → anchoring →
mirroring → proofpack chain described in the public-data runbook. The auditor
scans `osf_candidates.json`/`osf_selected.json` (and the equivalent files for
Figshare, Dryad, and Zenodo), verifies mirrored dataset manifests, confirms
proofpack artefacts, and asserts that the unified verifier has written a
`THIELE_OK` flag. Outstanding tasks are summarised in the JSON output so
operators can identify which step (e.g. anchoring or mirroring) remains before
declaring the law demonstration complete.

### End-to-end orchestration

The zero-trust pipeline can be executed with

```bash
python -m scripts.run_proofpack_pipeline --profile quick --note "ci smoke"
```

This command uses the quick profile (reduced trial counts) to run every builder
protocol, writes artefacts under
`artifacts/experiments/<timestamp>/proofpack/`, and invokes the bundler to
produce the verified archive in
`artifacts/experiments/<timestamp>/bundle/`. The script accepts
`--signing-key`, `--run-tag`, and verifier tolerance overrides so operators can
match production thresholds. Regression coverage for the orchestrator lives in
`tests/scripts/test_run_proofpack_pipeline.py`.

For CI and nightly smoke checks, `make proofpack-smoke` wraps the quick profile
with a deterministic run tag, and the scheduled `proofpack-smoke` job in
`.github/workflows/ci.yml` runs this target, uploading the bundled artefacts and
manifest digest to the Actions summary.

### Red-team perturbations

`red_team.py` provides deterministic perturbations that satisfy the Phase E
requirements:

- `structure_ablation` inflates sighted runtime slopes and lowers structure
  integrity so the cross-domain verifier rejects the run.
- `scramble_entropy` flips mid-run entropy increments to break the Theil–Sen
  slope and Spearman correlation checks for the entropy identity.
- `worst_order_schedule` collapses blind penalty bits and work so the CWD
  inequality fails.

The regression suite (`tests/experiments/test_red_team.py`) builds clean runs,
applies each adversarial transform, and asserts that the verifiers report the
expected failures.

`tests/tools/test_proofpack_bundler.py` demonstrates the full
falsifier→archivist loop: red-team mutations cause the unified verifier to
return a failure, and the bundler refuses to emit a manifest when any phase
breaks the zero-trust tolerances.

Support files should live under subdirectories:

- `configs/` for deterministic task distributions and fixtures;
- `data/` for small (<1 KB) ledger replay snippets used in tests;
- `plots/` for generated figures (excluded from version control).

See `scripts/agent_experiment_prompt.md` for the full specification and
role responsibilities.
