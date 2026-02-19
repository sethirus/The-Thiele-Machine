# Heuristic Targeting + Heatmaps

Generated: 2026-02-19T01:17:07.538756+00:00

## Heatmaps

- layer alignment: `artifacts/charts/layer_alignment_heatmap.png`
- heuristic targeting: `artifacts/charts/heuristic_targeting_heatmap.png`
- inquisitor severity: `artifacts/charts/inquisitor_severity_heatmap.png`

## Integrated Signals

- Inquisitor summary: HIGH=0, MEDIUM=0, LOW=0
- Gap report items: 1
- Connection pressure: {'disconnect_pressure': 0.5, 'proof_isolation': 1.0, 'semantic_sprawl': 1.0, 'outside_pressure': 0.4125, 'stale_pressure': 0.4125}
- Alignment summary: {'aligned_elements': 7, 'total_elements': 7}

## Top Heuristic Targets

- 1. `P0-fullwirespec-discharge` (P0) score=0.6909 — Discharge concrete FullWireSpec obligation in Coq
- 2. `P1-receipt-endtoend` (P1) score=0.6669 — Receipt integrity end-to-end closure
- 3. `P1-lockstep-expansion` (P1) score=0.6509 — Expand lockstep corpus and adversarial coverage
- 4. `P2-backend-parity` (P2) score=0.6429 — Dual-simulator parity (iverilog/verilator)

## Programmatic Artifacts

- `artifacts/heuristic_targeting.json`
- `artifacts/isomorphism_implementation_matrix.json`
- `artifacts/isomorphism_gap_report.json`
- `INQUISITOR_REPORT.md`
