from __future__ import annotations

import csv
import json
from pathlib import Path

import pytest

from experiments import ledger_io
from experiments.run_cross_domain import (
    CrossDomainConfig,
    execute,
    main,
    run_cross_domain,
)


def _make_config(tmp_path: Path, **overrides) -> CrossDomainConfig:
    base = dict(
        output_dir=tmp_path,
        seeds=[1, 3],
        trials_per_condition=3,
        modules=5,
        protocol="sighted",
        domains=("compression", "ldpc"),
        mu_base=0.24,
        mu_jitter=0.03,
        runtime_base=1.1,
        runtime_scale=0.75,
    )
    base.update(overrides)
    return CrossDomainConfig(**base)


def test_execute_cross_domain_reproducible(tmp_path: Path) -> None:
    config = _make_config(tmp_path)
    first = execute(config)
    second = execute(config)
    assert first.ledger_rows == second.ledger_rows
    assert [s.as_row() for s in first.summaries] == [s.as_row() for s in second.summaries]

    for summary in first.summaries:
        assert summary.domain_slope_ci_low <= 0.0 <= summary.domain_slope_ci_high
        assert abs(summary.domain_slope) <= 0.08
        assert summary.structure_integrity == pytest.approx(1.0, abs=1e-12)


def test_cross_domain_protocol_behaviour(tmp_path: Path) -> None:
    blind = execute(_make_config(tmp_path, protocol="blind"))
    destroyed = execute(_make_config(tmp_path, protocol="destroyed"))

    for summary in blind.summaries:
        assert summary.domain_delta_aic >= 10.0
        assert summary.structure_integrity == pytest.approx(0.5, abs=1e-12)
        assert summary.domain_slope > 0.25

    for summary in destroyed.summaries:
        assert summary.structure_integrity == pytest.approx(0.0, abs=1e-12)
        assert summary.domain_slope > 0.1


def test_cross_domain_cli_outputs(tmp_path: Path) -> None:
    out_dir = tmp_path / "cross"
    args = [
        "--output-dir",
        str(out_dir),
        "--seeds",
        "0",
        "--trials-per-condition",
        "2",
        "--modules",
        "4",
        "--protocol",
        "blind",
        "--runtime-scale",
        "0.8",
    ]
    main(args)

    ledger_path = out_dir / "cross_domain_steps.jsonl"
    summary_path = out_dir / "cross_domain_summary.csv"
    metadata_path = out_dir / "cross_domain_metadata.json"

    assert ledger_path.exists()
    assert summary_path.exists()
    assert metadata_path.exists()

    entries = ledger_io.load_ledger(ledger_path)
    digest = ledger_io.ledger_digest(entries)

    with metadata_path.open("r", encoding="utf-8") as handle:
        metadata = json.load(handle)
    assert metadata["ledger_digest_sha256"] == digest
    assert metadata["protocol"] == "blind"

    with summary_path.open("r", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    assert rows
    for row in rows:
        assert float(row["domain_aic_exponential"]) <= float(row["domain_aic_polynomial"])


def test_cross_domain_synthetic_replay(tmp_path: Path) -> None:
    fixture = Path("experiments/data/sample_cross_domain.jsonl")
    result = run_cross_domain(_make_config(tmp_path), synthetic_ledger=fixture)
    assert result.metadata["protocol"] == "synthetic"
    assert len(result.summaries) == 1
    summary = result.summaries[0]
    assert summary.domain_slope == pytest.approx(0.0, abs=1e-12)
    assert summary.structure_integrity == pytest.approx(1.0, abs=1e-12)
