from __future__ import annotations

import csv
import json
import math
from pathlib import Path

import pytest

from experiments import ledger_io
from experiments.run_cwd import (
    K_BOLTZMANN,
    LN2,
    CWDConfig,
    execute,
    main,
    run_cwd,
)


def _make_config(tmp_path: Path, **overrides) -> CWDConfig:
    base = dict(
        output_dir=tmp_path,
        seeds=[3],
        temps=[0.8],
        trials_per_condition=2,
        modules=3,
        steps_per_module=5,
        mu_base=0.17,
        mu_jitter=0.03,
        penalty_scale=1.6,
        protocol="sighted",
    )
    base.update(overrides)
    return CWDConfig(**base)


def test_execute_cwd_reproducible(tmp_path: Path) -> None:
    config = _make_config(tmp_path)
    result_one = execute(config)
    result_two = execute(config)

    assert result_one.ledger_rows == result_two.ledger_rows
    assert [s.as_row() for s in result_one.summaries] == [s.as_row() for s in result_two.summaries]

    for summary in result_one.summaries:
        kTln2 = K_BOLTZMANN * summary.temperature * LN2
        assert pytest.approx(summary.work / kTln2, rel=5e-4, abs=5e-4) == summary.mu_total_bits
        assert summary.penalty_bits_total == pytest.approx(0.0, abs=1e-12)
        assert summary.mutual_information_bits == pytest.approx(
            math.log2(config.modules), rel=5e-4, abs=5e-4
        )
        assert summary.success_rate == pytest.approx(1.0, abs=1e-12)


def test_cwd_penalty_bound(tmp_path: Path) -> None:
    sighted = execute(
        _make_config(
            tmp_path,
            protocol="sighted",
            seeds=[4],
            temps=[0.9],
            trials_per_condition=1,
        )
    )
    blind = execute(
        _make_config(
            tmp_path,
            protocol="blind",
            seeds=[4],
            temps=[0.9],
            trials_per_condition=1,
        )
    )

    sighted_map = {
        (s.seed, s.temperature, s.trial_id): s
        for s in sighted.summaries
    }
    blind_map = {
        (s.seed, s.temperature, s.trial_id): s
        for s in blind.summaries
    }

    assert sighted_map.keys() == blind_map.keys()

    for key, sighted_summary in sighted_map.items():
        blind_summary = blind_map[key]
        kTln2 = K_BOLTZMANN * sighted_summary.temperature * LN2
        diff_bits = (blind_summary.work - sighted_summary.work) / kTln2
        assert diff_bits == pytest.approx(blind_summary.penalty_bits_total, rel=1e-6, abs=1e-9)
        assert diff_bits >= sighted_summary.mutual_information_bits * 0.95
        assert blind_summary.mutual_information_bits <= 0.4


def test_main_cwd_outputs(tmp_path: Path) -> None:
    out_dir = tmp_path / "cwd"
    args = [
        "--output-dir",
        str(out_dir),
        "--seeds",
        "0",
        "--temps",
        "0.85",
        "--trials-per-condition",
        "1",
        "--modules",
        "3",
        "--steps-per-module",
        "4",
        "--mu-base",
        "0.18",
        "--mu-jitter",
        "0.02",
        "--penalty-scale",
        "1.5",
        "--protocol",
        "sighted",
    ]
    main(args)

    ledger_path = out_dir / "cwd_steps.jsonl"
    summary_path = out_dir / "cwd_summary.csv"
    metadata_path = out_dir / "cwd_metadata.json"

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
        work_bits = float(row["work_over_kTln2"])
        mu_bits = float(row["mu_total_bits"])
        assert pytest.approx(work_bits, rel=5e-4, abs=5e-4) == mu_bits


def test_cwd_synthetic_replay(tmp_path: Path) -> None:
    fixture = Path("experiments/data/sample_cwd.jsonl")
    result = run_cwd(_make_config(tmp_path), synthetic_ledger=fixture)
    assert result.metadata["protocol"] == "synthetic"
    assert len(result.summaries) == 1
    summary = result.summaries[0]
    kTln2 = K_BOLTZMANN * summary.temperature * LN2
    assert pytest.approx(summary.work / kTln2, rel=5e-6, abs=5e-6) == summary.mu_total_bits
    assert summary.mutual_information_bits == pytest.approx(math.log2(summary.module_count), rel=5e-4)
