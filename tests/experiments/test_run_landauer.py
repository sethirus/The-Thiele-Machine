from __future__ import annotations

import csv
import json
from pathlib import Path

import pytest

from experiments import ledger_io
from experiments.run_landauer import LandauerConfig, execute, main, run_landauer


def _make_config(tmp_path: Path, **overrides) -> LandauerConfig:
    base = dict(
        output_dir=tmp_path,
        seeds=[0],
        temps=[0.5, 1.0],
        trials_per_condition=4,
        steps=24,
        protocol="sighted",
    )
    base.update(overrides)
    return LandauerConfig(**base)


def test_execute_landauer_reproducible(tmp_path: Path) -> None:
    config = _make_config(tmp_path)
    run_one = execute(config)
    run_two = execute(config)

    assert run_one.ledger_rows == run_two.ledger_rows
    assert [s.as_row() for s in run_one.summaries] == [s.as_row() for s in run_two.summaries]

    for summary in run_one.summaries:
        assert 0.0 <= summary.sum_mu_bits <= 1.0
        assert pytest.approx(summary.sum_mu_bits, rel=1e-9, abs=1e-9) == summary.work_over_kTln2


def test_main_writes_summary_and_metadata(tmp_path: Path) -> None:
    out_dir = tmp_path / "landauer"
    args = [
        "--output-dir",
        str(out_dir),
        "--seeds",
        "0",
        "--temps",
        "0.5",
        "1.0",
        "--trials-per-condition",
        "3",
        "--steps",
        "16",
    ]
    main(args)

    ledger_path = out_dir / "landauer_steps.jsonl"
    summary_path = out_dir / "landauer_summary.csv"
    metadata_path = out_dir / "landauer_metadata.json"

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

    assert rows, "summary CSV must contain trial rows"
    for row in rows:
        mu = float(row["sum_mu_bits"])
        ratio = float(row["work_over_kTln2"])
        assert pytest.approx(mu, rel=1e-9, abs=1e-9) == ratio


def test_synthetic_ledger_replay(tmp_path: Path) -> None:
    fixture = Path("experiments/data/sample_ledger.jsonl")
    config = _make_config(tmp_path, temps=[1.0], trials_per_condition=1)

    result = run_landauer(config, synthetic_ledger=fixture)

    assert len(result.ledger_rows) == 2
    assert len(result.summaries) == 1

    summary = result.summaries[0]
    assert pytest.approx(summary.sum_mu_bits, rel=1e-9, abs=1e-9) == summary.work_over_kTln2
    assert summary.protocol == "synthetic"
