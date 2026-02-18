Helper scripts
===============

This folder contains helper scripts for publishing and verifying release artifacts.

Make scripts executable before running:

  chmod +x scripts/*.sh


Available scripts (core):

- `verify_release.sh` — Verifies tarball SHA-256, optionally verifies GPG detached signature and provides pointers to SWH and DOI checks.
- `validate_mu_gravity_calibration.py` — Computes empirical curvature↔Laplacian calibration residuals from VM graph snapshots and can emit Coq hypothesis stubs for `MuGravity` dynamic predicates.
  It also computes semantic gap/delta-window metrics aligned with `calibration_gap`,
  `calibration_gap_delta`, and the one-step strict descent window theorem.
- `analyze_mu_gravity_physics.py` — Physics-facing post-analysis over snapshots:
  estimates coupling scaling `k` from `K ~= k*Δμ` and emits horizon entropy
  deviation predictions (`S_info - S_GR`) for falsifiable dataset checks.

Example:

```bash
python3 scripts/validate_mu_gravity_calibration.py \
  --input artifacts/mu_gravity_snapshots.json \
  --output artifacts/mu_gravity_calibration_report.json \
  --neighborhood adjacent \
  --curvature-coupling 3.141592653589793 \
  --calibration-tol 1e-6 \
  --emit-coq-hypotheses artifacts/mu_gravity_empirical_hypotheses.v

python3 scripts/analyze_mu_gravity_physics.py \
  --input artifacts/mu_gravity_snapshots.json \
  --output artifacts/mu_gravity_physics_report.json \
  --neighborhood adjacent \
  --gravitational-constant 1.0 \
  --derived-h 1.0
```

Expected snapshot formats:

- Single snapshot JSON object with `graph.modules`
- JSON list of snapshot objects
- Object with `snapshots: [...]`

Each module entry should provide `id`, `region`, and optional `axioms`.

Generated reports include:

- Per-module residual deltas and strict-descent flags across adjacent snapshots.
- Per-module semantic gap metrics (`calibration_gap_prev/curr`, `calibration_gap_delta_from_prev`).
- `semantic_delta_window_pos` indicating the theorem window
  $(0 < gap_{prev}) \wedge (-2*gap_{prev} < \Delta gap < 0)$.
- Coverage summaries (`descent_summary`, `prefix_theorem_coverage`, `semantic_delta_coverage`).

When `--emit-coq-hypotheses` is enabled, modules passing the semantic delta window also emit
`empirical_semantic_delta_window_pos_*` axioms over `run_vm` states.
For consecutive fuels (f and f+1), the generated file also emits stitched lemmas
`empirical_semantic_progress_f*_m*` that apply
`calibration_progress_consecutive_run_vm_from_gap_window` directly.

If you plan to run the publishing scripts on a machine or CI runner, ensure the required tokens are present in the environment and never hard-code secrets into the repository.
