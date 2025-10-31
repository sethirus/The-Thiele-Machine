from __future__ import annotations

import csv
import json
from pathlib import Path

import pytest

from experiments import ledger_io
from experiments.run_entropy import EntropyConfig, execute, main, run_entropy


def _make_config(tmp_path: Path, **overrides) -> EntropyConfig:
    base = dict(
        output_dir=tmp_path,
        seeds=[0],
        temps=[0.75, 1.25],
        trials_per_condition=3,
        steps=32,
        dt=0.5,
        mobility=0.4,
        force=0.6,
        protocol="sighted",
        entropy_scale=1.0,
        entropy_smoothing=0.05,
    )
    base.update(overrides)
    return EntropyConfig(**base)


def test_execute_entropy_reproducible(tmp_path: Path) -> None:
    config = _make_config(tmp_path)
    result_one = execute(config)
    result_two = execute(config)

    assert result_one.ledger_rows == result_two.ledger_rows
    assert [s.as_row() for s in result_one.summaries] == [s.as_row() for s in result_two.summaries]
    assert result_one.series_rows == result_two.series_rows

    for summary in result_one.summaries:
        assert abs(summary.theil_sen_slope - 1.0) < 0.08
        assert summary.slope_ci_low < 1.0 < summary.slope_ci_high
        assert summary.spearman_rho > 0.9
        assert summary.spearman_pvalue < 0.1
        assert abs(summary.entropy_sum - summary.mu_answer_sum) < 0.08

    assert len(result_one.series_rows) == len(result_one.ledger_rows)
    for ledger_row, series_row in zip(result_one.ledger_rows, result_one.series_rows):
        assert ledger_row["seed"] == series_row["seed"]
        assert ledger_row["trial_id"] == series_row["trial_id"]
        assert ledger_row["step"] == series_row["step"]


def test_main_entropy_outputs(tmp_path: Path) -> None:
    out_dir = tmp_path / "entropy"
    args = [
        "--output-dir",
        str(out_dir),
        "--seeds",
        "0",
        "--temps",
        "0.75",
        "1.25",
        "--trials-per-condition",
        "2",
        "--steps",
        "24",
        "--dt",
        "0.5",
        "--mobility",
        "0.4",
        "--force",
        "0.6",
        "--entropy-smoothing",
        "0.04",
    ]
    main(args)

    ledger_path = out_dir / "entropy_steps.jsonl"
    summary_path = out_dir / "entropy_summary.csv"
    series_path = out_dir / "entropy_series.csv"
    metadata_path = out_dir / "entropy_metadata.json"

    assert ledger_path.exists()
    assert summary_path.exists()
    assert series_path.exists()
    assert metadata_path.exists()

    entries = ledger_io.load_ledger(ledger_path)
    digest = ledger_io.ledger_digest(entries)

    with metadata_path.open("r", encoding="utf-8") as handle:
        metadata = json.load(handle)
    assert metadata["ledger_digest_sha256"] == digest
    assert metadata["protocol"] == "sighted"
    assert metadata["entropy_smoothing"] == pytest.approx(0.04)

    with summary_path.open("r", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    assert rows
    for row in rows:
        mu_sum = float(row["mu_answer_sum"])
        entropy_sum = float(row["entropy_sum"])
        assert abs(entropy_sum - mu_sum) < 0.08
        slope = float(row["theil_sen_slope"])
        assert 0.9 < slope < 1.1

    with series_path.open("r", encoding="utf-8") as handle:
        series_rows = list(csv.DictReader(handle))
    assert series_rows
    assert all("mu_cumulative" in row for row in series_rows)
    assert all("entropy_cumulative" in row for row in series_rows)


def test_synthetic_entropy_replay(tmp_path: Path) -> None:
    fixture = Path("experiments/data/sample_entropy.jsonl")
    config = _make_config(tmp_path, temps=[1.0], trials_per_condition=1, steps=2)

    result = run_entropy(config, synthetic_ledger=fixture)

    assert result.metadata["protocol"] == "synthetic"
    assert len(result.summaries) == 1
    summary = result.summaries[0]
    assert abs(summary.entropy_sum - summary.mu_answer_sum) < 0.01
    assert summary.spearman_rho >= 0.0
    assert result.series_rows[0]["step"] == 0
