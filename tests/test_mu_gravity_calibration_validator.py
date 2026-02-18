from __future__ import annotations

import json
from pathlib import Path

from scripts.validate_mu_gravity_calibration import (
    build_coq_hypotheses,
    evaluate_snapshots,
    load_snapshots,
)


def test_load_snapshots_single_payload(tmp_path: Path) -> None:
    payload = {
        "fuel": 3,
        "graph": {
            "modules": [
                {"id": 1, "region": [1, 2], "axioms": ["abc", "d"]},
                {"id": 2, "region": [2, 3], "axioms": []},
            ]
        },
    }
    input_path = tmp_path / "single_snapshot.json"
    input_path.write_text(json.dumps(payload), encoding="utf-8")

    snapshots = load_snapshots(input_path)
    assert len(snapshots) == 1
    assert snapshots[0].fuel == 3
    assert [m.module_id for m in snapshots[0].modules] == [1, 2]


def test_evaluate_and_emit_hypotheses(tmp_path: Path) -> None:
    payload = {
        "snapshots": [
            {
                "fuel": 5,
                "graph": {
                    "modules": [
                        {"id": 1, "region": [10], "axioms": ["A"]},
                        {"id": 2, "region": [10, 11], "axioms": ["BC"]},
                    ]
                },
            },
            {
                "fuel": 6,
                "graph": {
                    "modules": [
                        {"id": 1, "region": [10], "axioms": ["A", "D"]},
                        {"id": 2, "region": [10, 11], "axioms": ["BC"]},
                    ]
                },
            },
        ]
    }
    input_path = tmp_path / "snapshot_list.json"
    input_path.write_text(json.dumps(payload), encoding="utf-8")

    snapshots = load_snapshots(input_path)
    report = evaluate_snapshots(
        snapshots=snapshots,
        neighborhood_mode="adjacent",
        calibration_tol=10.0,
        source_tol=1e9,
        gravitational_constant=1.0,
        curvature_coupling=3.141592653589793,
    )

    assert report["snapshot_count"] == 2
    assert report["module_count"] == 4
    assert report["calibrated_modules"] >= 1

    second_modules = report["snapshots"][1]["modules"]
    assert any("residual_delta_from_prev" in m for m in second_modules)
    assert any("strict_descent_from_prev" in m for m in second_modules)
    assert any("prefix_residual_positive_prev" in m for m in second_modules)
    assert any("prefix_policy_premises_proxy" in m for m in second_modules)
    assert any("prefix_theorem_outcome_proxy" in m for m in second_modules)

    second_snapshot = report["snapshots"][1]
    assert "active_transition_from_prev" in second_snapshot
    assert "created_modules_from_prev" in second_snapshot
    assert "removed_modules_from_prev" in second_snapshot
    assert "changed_existing_modules_from_prev" in second_snapshot

    assert "descent_summary" in report
    summary = report["descent_summary"]
    assert "compared_module_pairs" in summary
    assert "strict_descent_pairs" in summary
    assert "nonincreasing_pairs" in summary

    assert "prefix_theorem_coverage" in report
    coverage = report["prefix_theorem_coverage"]
    assert "evaluated_modules" in coverage
    assert "premises_true" in coverage
    assert "outcomes_true" in coverage
    assert "implication_holds_count" in coverage

    assert "semantic_delta_coverage" in report
    sem_cov = report["semantic_delta_coverage"]
    assert "evaluated_modules" in sem_cov
    assert "window_true" in sem_cov
    assert "strict_descent_when_window" in sem_cov

    assert any("calibration_gap_prev" in m for m in second_modules)
    assert any("calibration_gap_curr" in m for m in second_modules)
    assert any("calibration_gap_delta_from_prev" in m for m in second_modules)
    assert any("semantic_delta_window_pos" in m for m in second_modules)

    coq_text = build_coq_hypotheses(report, include_source=True)
    assert "From Kernel Require Import MuGravity." in coq_text
    assert "Axiom empirical_dynamically_self_calibrates_f5_m" in coq_text
    assert "curvature_coupling * mu_laplacian" in coq_text
    assert "empirical_semantic_delta_window_pos" in coq_text
    assert "calibration_progress_consecutive_run_vm_from_gap_window" in coq_text
