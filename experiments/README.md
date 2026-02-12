# Thiele Machine experiments package

This package contains experiment runners that synthesize μ-ledger proofpacks.
Each module emits deterministic CSV logs and ancillary artifacts that can be
recomputed byte-for-byte, avoids dynamic code generation or network dependencies,
and provides CLI entry points so verifiers can re-run with the same configuration.

## Implemented Builders

| Module | Role | Description |
| --- | --- | --- |
| `run_landauer.py` | Builder (Phase A1) | Four-state Ising surrogate with deterministic Metropolis kernel, μ-ledger outputs, and CLI entry point. |
| `run_einstein.py` | Builder (Phase A2) | Biased diffusion simulator that records drift/mobility snapshots for the Einstein relation. |
| `run_einstein_refined.py` | Builder (Phase A2+) | Refined Einstein relation runner with extended diagnostics. |
| `run_entropy.py` | Builder (Phase A3) | Entropy-identity extension logging μ/entropy deltas, cumulative series, and monotonicity diagnostics. |
| `run_cwd.py` | Builder (Phase B1) | Multi-module compositional work decomposition runner with sighted/blind/destroyed protocols, penalty logging, and mutual-information diagnostics. |
| `run_cross_domain.py` | Builder (Phase C) | Compression/LDPC microbenchmarks with sighted/blind/destroyed variants that log μ and runtime echoes for cross-domain verification. |

## Shared Utilities

| Module | Role | Description |
| --- | --- | --- |
| `ledger_io.py` | Shared | JSONL load/store/digest helpers shared across roles. |
| `proofpack.py` | Archivist | Builds manifests, protocol summaries, and Ed25519-signed receipts for proofpacks. |
| `red_team.py` | Falsifier | Deterministic perturbations that trigger verifier failure modes. |
| `plot_utils.py` | Shared | Plotting utilities for experiment visualization. |
| `vm_reference.py` | Shared | VM reference implementation for experiments. |
| `vm_instrumentation.py` | Shared | VM instrumentation hooks for measurement. |
| `vm_integration_adapter.py` | Shared | Adapter bridging experiments to the VM. |

## External Dataset Discovery

The `data_sources/` subpackage provides API clients for public data repositories:

| Module | Source | Description |
| --- | --- | --- |
| `data_sources/osf.py` | OSF | OSF search API client for optical tweezers & SPT queries. |
| `data_sources/figshare.py` | Figshare | Figshare v2 article search with per-record file metadata. |
| `data_sources/dryad.py` | Dryad | Dryad HAL client (dataset → version → files). |
| `data_sources/zenodo.py` | Zenodo | Zenodo query helper with creator/DOI rehydration. |
| `data_sources/download.py` | All | Deterministic mirroring with SHA-256 manifests. |
| `data_sources/anchors.py` | All | Regex-driven anchor extraction (temperature, pixel scale, frame interval). |
| `data_sources/jhtdb.py` | JHTDB | Turbulence trajectory sampling from JHTDB. |

## Turbulence Protocol

`experiments/turbulence/protocol.py` consumes mirrored `jhtdb_samples.json`,
groups spatial points into coarse modules, and emits μ-ledgers, summaries, and
SVG diagnostics for the sighted, blind, and destroyed protocols.

## Other Experiment Scripts

| Module | Description |
| --- | --- |
| `mu_audited_bell_test.py` | μ-audited CHSH Bell test experiment. |
| `mu_cost_complete.py` | Complete μ-cost analysis. |
| `complexity_gap.py` | Complexity gap measurement between sighted/blind. |
| `graph_isomorphism_partitions.py` | Graph isomorphism via partition methods. |
| `numbertheory_factoring.py` | Number theory factoring experiments. |
| `logic_only_factoring.py` | Logic-only factoring approach. |
| `revelation_factoring.py` | Revelation-based factoring experiment. |
| `pdiscover_factoring.py` | PDISCOVER-based factoring. |
| `thermodynamic_factoring.py` | Thermodynamic factoring experiment. |
| `empirical_validation.py` | Empirical validation of theoretical predictions. |
| `comprehensive_stress_test.py` | Comprehensive stress testing suite. |
| `derive_G_numerical.py` | Numerical derivation of gravitational constant G. |
| `derive_c_numerical.py` | Numerical derivation of speed of light c. |
| `derive_masses_couplings.py` | Derivation of particle masses and couplings. |
| `quantum_gravity_predictions.py` | Quantum gravity predictions from μ-framework. |
| `qm_divergent_predictions.py` | QM-divergent prediction experiments. |
| `run_all_predictions.py` | Run all prediction experiments. |
| `visualize_predictions.py` | Visualization of prediction results. |
| `observer_effect.py` | Observer effect experiments. |
| `receipt_forgery.py` | Receipt forgery detection tests. |
| `energy_meter.py` | Energy metering for μ-cost validation. |

## Test Fixtures

Deterministic replay fixtures live under `experiments/data/`:

- `sample_ledger.jsonl` — generic μ-ledger fixture
- `sample_einstein.jsonl` — Einstein relation replay data
- `sample_entropy.jsonl` — Entropy identity replay data
- `sample_cwd.jsonl` — CWD protocol replay data
- `sample_cross_domain.jsonl` — Cross-domain replay data
- `turbulence/` — JHTDB turbulence fixtures

## Configuration

Experiment configuration is in `config.json` and `hypotheses.yaml`.

## Running Experiments

```bash
# Run individual builders:
python -m experiments.run_landauer --protocol sighted --output-dir outputs/landauer
python -m experiments.run_einstein --protocol blind --output-dir outputs/einstein
python -m experiments.run_entropy --output-dir outputs/entropy
python -m experiments.run_cwd --output-dir outputs/cwd

# Run all prediction experiments:
python -m experiments.run_all_predictions
```
