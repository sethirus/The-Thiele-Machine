from __future__ import annotations

import csv
import json
from pathlib import Path

import pytest

from experiments import ledger_io
from experiments.run_einstein import (
    K_BOLTZMANN,
    EinsteinConfig,
    execute,
    main,
    run_einstein,
)


def _make_config(tmp_path: Path, **overrides) -> EinsteinConfig:
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
    )
    base.update(overrides)
    return EinsteinConfig(**base)


def test_execute_einstein_reproducible(tmp_path: Path) -> None:
    config = _make_config(tmp_path)
    result_one = execute(config)
    result_two = execute(config)

    assert result_one.ledger_rows == result_two.ledger_rows
    assert [s.as_row() for s in result_one.summaries] == [s.as_row() for s in result_two.summaries]

    for summary in result_one.summaries:
        assert pytest.approx(summary.mu_answer_sum, rel=5e-3, abs=5e-4) == sum(
            row["mu_answer"]
            for row in result_one.ledger_rows
            if row["seed"] == summary.seed
            and row["T"] == summary.temperature
            and row["trial_id"] == summary.trial_id
        )

    by_temp: dict[float, dict[str, float]] = {}
    for summary in result_one.summaries:
        state = by_temp.setdefault(
            summary.temperature,
            {"diffusion": 0.0, "mobility": 0.0, "count": 0.0, "residual": 0.0},
        )
        state["diffusion"] += summary.diffusion
        state["mobility"] += summary.mobility
        state["residual"] += summary.residual
        state["count"] += 1.0

    for temperature, state in by_temp.items():
        mean_diffusion = state["diffusion"] / state["count"]
        mean_mobility = state["mobility"] / state["count"]
        expected = mean_mobility * K_BOLTZMANN * temperature
        assert pytest.approx(mean_diffusion, rel=5e-2, abs=2e-2) == expected
        assert abs(state["residual"] / state["count"]) < 0.25


def test_main_einstein_outputs(tmp_path: Path) -> None:
    out_dir = tmp_path / "einstein"
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
    ]
    main(args)

    ledger_path = out_dir / "einstein_steps.jsonl"
    summary_path = out_dir / "einstein_summary.csv"
    metadata_path = out_dir / "einstein_metadata.json"

    assert ledger_path.exists()
    assert summary_path.exists()
    assert metadata_path.exists()

    entries = ledger_io.load_ledger(ledger_path)
    digest = ledger_io.ledger_digest(entries)

    with metadata_path.open("r", encoding="utf-8") as handle:
        metadata = json.load(handle)
    assert metadata["ledger_digest_sha256"] == digest
    assert metadata["protocol"] == "sighted"

    with summary_path.open("r", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))

    assert rows
    for row in rows:
        diffusion = float(row["diffusion"])
        mobility = float(row["mobility"])
        temperature = float(row["T"])
        expected = mobility * K_BOLTZMANN * temperature
        assert pytest.approx(diffusion, rel=5e-3, abs=5e-4) == expected


def test_synthetic_einstein_replay(tmp_path: Path) -> None:
    fixture = Path("experiments/data/sample_einstein.jsonl")
    config = _make_config(tmp_path, temps=[1.0], trials_per_condition=1, steps=4)

    result = run_einstein(config, synthetic_ledger=fixture)

    assert result.metadata["protocol"] == "synthetic"
    assert len(result.summaries) == 1
    summary = result.summaries[0]
    assert pytest.approx(summary.diffusion, rel=1e-9, abs=1e-7) == summary.mobility * summary.temperature
