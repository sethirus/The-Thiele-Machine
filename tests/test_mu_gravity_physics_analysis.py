from __future__ import annotations

import json
from pathlib import Path

from scripts.analyze_mu_gravity_physics import (
    estimate_coupling,
    horizon_deviation_predictions,
)
from scripts.validate_mu_gravity_calibration import load_snapshots


def test_coupling_and_horizon_predictions(tmp_path: Path) -> None:
    payload = {
        "snapshots": [
            {
                "fuel": 0,
                "graph": {
                    "modules": [
                        {"id": 1, "region": [1], "axioms": ["A"]},
                        {"id": 2, "region": [2], "axioms": ["B", "C"]},
                    ]
                },
            },
            {
                "fuel": 1,
                "graph": {
                    "modules": [
                        {"id": 1, "region": [1], "axioms": ["A", "D"]},
                        {"id": 2, "region": [2], "axioms": ["B", "C"]},
                    ]
                },
            },
        ]
    }

    input_path = tmp_path / "snapshots.json"
    input_path.write_text(json.dumps(payload), encoding="utf-8")

    snapshots = load_snapshots(input_path)

    coupling = estimate_coupling(snapshots, "complete")
    assert coupling["point_count"] == 4
    assert "k_hat" in coupling
    assert "rmse_fit" in coupling
    assert "rmse_pi" in coupling

    horizon = horizon_deviation_predictions(
        snapshots,
        neighborhood_mode="complete",
        gravitational_constant=1.0,
        derived_h=1.0,
    )
    assert horizon["count"] == 2
    assert len(horizon["predictions"]) == 2
    assert "mean_abs_relative_delta" in horizon
    assert "entropy_delta" in horizon["predictions"][0]
