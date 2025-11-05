"""Tests for the public SPT proofpack runner."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from experiments import ledger_io
from experiments.public_data import spt_protocol
from experiments.public_data.run_spt_protocol import main as run_cli

DATA_DIR = Path(__file__).resolve().parents[2] / "data" / "public"


def _prepare_dataset(tmp_path: Path) -> Path:
    dataset_dir = tmp_path / "dataset"
    dataset_dir.mkdir()
    (dataset_dir / "raw").mkdir()
    anchors = DATA_DIR / "sample_anchors.json"
    tracks = DATA_DIR / "sample_tracks.csv"
    (dataset_dir / "anchors.json").write_text(anchors.read_text())
    (dataset_dir / "raw" / "tracks.csv").write_text(tracks.read_text())
    return dataset_dir


def test_run_dataset_writes_ledgers_and_summaries(tmp_path: Path) -> None:
    dataset_dir = _prepare_dataset(tmp_path)
    output_dir = tmp_path / "output"
    results = spt_protocol.run_dataset(dataset_dir, output_dir, seed=7)

    assert set(results) == set(spt_protocol.PROTOCOLS)
    for protocol, summary in results.items():
        summary_path = output_dir / "summaries" / f"{protocol}.json"
        assert summary_path.exists()
        ledger_path = output_dir / "ledgers" / f"{protocol}.jsonl"
        entries = ledger_io.load_ledger(ledger_path)
        assert len(entries) == summary.step_count
        plots_dir = output_dir / "plots"
        mu_plot = plots_dir / f"{protocol}_mu_vs_entropy.svg"
        complexity_plot = plots_dir / f"{protocol}_complexity.svg"
        assert mu_plot.exists()
        assert complexity_plot.exists()
        svg_text = mu_plot.read_text(encoding="utf-8")
        assert "1970-01-01T00:00:00Z" in svg_text
        if protocol == "blind":
            assert summary.delta_aic is not None and summary.delta_aic >= 10.0
        if protocol == "destroyed":
            assert summary.spearman_rho < 0.9

    oos_metrics = json.loads((output_dir / "oos_metrics.json").read_text())
    assert oos_metrics["oos_median_abs_pct_error"] < 0.1


def test_cli_entrypoint(tmp_path: Path) -> None:
    dataset_dir = _prepare_dataset(tmp_path)
    output_dir = tmp_path / "artefacts"
    run_cli([
        str(dataset_dir),
        "--output-dir",
        str(output_dir),
        "--seed",
        "3",
    ])
    assert (output_dir / "public_spt_metadata.json").exists()

