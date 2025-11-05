"""Verifier tests for public SPT proofpacks."""

from __future__ import annotations

from pathlib import Path

import pytest

from experiments.public_data import spt_protocol
from verifier.check_public_spt import verify_public_spt

DATA_DIR = Path(__file__).resolve().parents[1] / "data" / "public"


def _prepare_dataset(tmp_path: Path) -> Path:
    dataset_dir = tmp_path / "dataset"
    dataset_dir.mkdir()
    (dataset_dir / "raw").mkdir()
    (dataset_dir / "anchors.json").write_text((DATA_DIR / "sample_anchors.json").read_text())
    (dataset_dir / "raw" / "tracks.csv").write_text((DATA_DIR / "sample_tracks.csv").read_text())
    return dataset_dir


def test_verify_public_spt(tmp_path: Path) -> None:
    dataset_dir = _prepare_dataset(tmp_path)
    output_dir = tmp_path / "artefacts"
    spt_protocol.run_dataset(dataset_dir, output_dir, seed=11)

    out_path, payload = verify_public_spt(output_dir)
    assert out_path.exists()
    assert payload["status"] is True
    assert payload["oos_median_abs_pct_error"] < 0.1
    assert payload["protocols"]["blind"]["delta_aic"] >= 10.0


def test_verify_public_spt_rejects_threshold(tmp_path: Path) -> None:
    dataset_dir = _prepare_dataset(tmp_path)
    output_dir = tmp_path / "artefacts"
    spt_protocol.run_dataset(dataset_dir, output_dir, seed=4)

    _, baseline = verify_public_spt(output_dir)
    delta_aic = baseline["protocols"]["blind"]["delta_aic"]

    _, payload = verify_public_spt(output_dir, delta_aic_threshold=delta_aic + 5.0)
    assert payload["status"] is False

