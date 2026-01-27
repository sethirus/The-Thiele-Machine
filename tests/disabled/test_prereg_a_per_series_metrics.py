from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


def _write_csv(path: Path, text: str) -> None:
    path.write_text(text.strip() + "\n", encoding="utf-8")


def test_prereg_a_reports_per_series_metrics_and_unit_applicability(tmp_path: Path) -> None:
    repo_root = Path(__file__).resolve().parents[1]
    tool = repo_root / "tools" / "prereg_a_landauer.py"

    data_dir = tmp_path / "DATA_A"
    data_dir.mkdir()

    # One tau-hat point (tightening-applicable) and one seconds point
    # (tightening must be disabled / Landauer-only).
    _write_csv(
        data_dir / "toy.csv",
        """
paper_id,figure_id,dataset_id,value_kind,tau_unit,tau_s,work_over_kT,work_err_over_kT,info_bits_removed
PaperHat,F1,DSH,work_over_kT,D_tau_over_Var,1.0,10.0,,1.0
PaperSec,F1,DSS,work_over_kT,s,1.0,10.0,,1.0
""",
    )

    out_root = tmp_path / "run"
    sources = ["PaperHat", "PaperSec"]

    subprocess.run(
        [
            sys.executable,
            str(tool),
            "--root",
            str(out_root),
            "init",
            "--split-policy",
            "fit_none",
            "--calibration-dataset",
            "DSH",
            "--sources",
            *sources,
        ],
        check=True,
        cwd=str(repo_root),
    )
    subprocess.run(
        [
            sys.executable,
            str(tool),
            "--root",
            str(out_root),
            "ingest",
            "--split-policy",
            "fit_none",
            "--calibration-dataset",
            "DSH",
            "--sources",
            *sources,
            "--data-dir",
            str(data_dir),
        ],
        check=True,
        cwd=str(repo_root),
    )
    subprocess.run(
        [
            sys.executable,
            str(tool),
            "--root",
            str(out_root),
            "analyze",
            "--split-policy",
            "fit_none",
            "--calibration-dataset",
            "DSH",
            "--sources",
            *sources,
            "--data-dir",
            str(data_dir),
        ],
        check=True,
        cwd=str(repo_root),
    )

    analysis = json.loads((out_root / "analysis_A.json").read_text(encoding="utf-8"))

    assert "series_metrics" in analysis
    series_metrics = analysis["series_metrics"]

    # Expect exactly one series per row (curve_id omitted -> NO_CURVE_ID).
    hat_sid = "PaperHat:F1:DSH:NO_CURVE_ID"
    sec_sid = "PaperSec:F1:DSS:NO_CURVE_ID"
    assert hat_sid in series_metrics
    assert sec_sid in series_metrics

    assert series_metrics[hat_sid]["tau_units"] == ["D_tau_over_Var"]
    assert series_metrics[sec_sid]["tau_units"] == ["s"]
    assert series_metrics[hat_sid]["tighten_fraction"] == 1.0
    assert series_metrics[sec_sid]["tighten_fraction"] == 0.0

    # Applicable-units aggregate should be defined and reflect only the tau-hat point.
    applicability = analysis["metrics"]["applicability"]
    assert applicability["tightening_applicable_units"] == ["D_tau_over_Var"]
    assert applicability["n_applicable"] == 1
    assert applicability["n_total"] == 2
    assert applicability["tighten_fraction_applicable_units"] == 1.0
