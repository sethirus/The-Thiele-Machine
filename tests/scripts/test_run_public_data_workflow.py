from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from experiments.data_sources.download import derive_dataset_slug


def _write_key(path: Path) -> None:
    private_key = Ed25519PrivateKey.generate()
    path.write_bytes(
        private_key.private_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PrivateFormat.Raw,
            encryption_algorithm=serialization.NoEncryption(),
        )
    )


@pytest.fixture
def sample_candidates_path() -> Path:
    return Path(__file__).resolve().parents[1] / "data" / "sample_candidates.json"


@pytest.fixture
def sample_tracks_path() -> Path:
    return Path(__file__).resolve().parents[1] / "data" / "public" / "sample_tracks.csv"


@pytest.fixture
def sample_anchors_path() -> Path:
    return Path(__file__).resolve().parents[1] / "data" / "public" / "sample_anchors.json"


def test_run_public_data_workflow(tmp_path: Path, sample_candidates_path: Path, sample_tracks_path: Path, sample_anchors_path: Path) -> None:
    mirror_root = tmp_path / "mirrored"
    key_path = tmp_path / "key.bin"
    _write_key(key_path)

    # Pre-seed the mirrored dataset so the workflow can run with --skip-download.
    candidate_payload = json.loads(sample_candidates_path.read_text(encoding="utf-8"))
    primary_candidate = candidate_payload["candidates"][0]
    slug = derive_dataset_slug("osf", primary_candidate)
    dataset_dir = mirror_root / "osf" / slug
    raw_dir = dataset_dir / "raw"
    raw_dir.mkdir(parents=True, exist_ok=True)
    (dataset_dir / "candidate.json").write_text(json.dumps(primary_candidate, indent=2), encoding="utf-8")
    (dataset_dir / "anchors.json").write_text(sample_anchors_path.read_text(encoding="utf-8"), encoding="utf-8")
    (raw_dir / "tracks.csv").write_text(sample_tracks_path.read_text(encoding="utf-8"), encoding="utf-8")

    turbulence_dir = mirror_root / "jhtdb" / "sample"
    turbulence_dir.mkdir(parents=True, exist_ok=True)
    sample_turbulence = Path(__file__).resolve().parents[1] / "data" / "turbulence" / "sample_jhtdb_samples.json"
    (turbulence_dir / "jhtdb_samples.json").write_text(sample_turbulence.read_text(encoding="utf-8"), encoding="utf-8")

    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "scripts.run_public_data_workflow",
            "--source",
            "osf",
            "--candidates",
            str(sample_candidates_path),
            "--mirror-root",
            str(mirror_root),
            "--output-root",
            str(tmp_path / "artifacts" / "experiments"),
            "--signing-key",
            str(key_path),
            "--run-tag",
            "workflow-test",
            "--skip-download",
            "--turbulence-protocol",
            "blind",
            "--turbulence-seed",
            "9",
            "--turbulence-dataset",
            "sample",
        ],
        check=True,
        text=True,
        capture_output=True,
    )

    output_lines = [line for line in completed.stdout.splitlines() if line.strip()]
    summary = json.loads(output_lines[-1])
    assert summary["run_tag"] == "workflow-test"
    assert summary["selected_count"] >= 1
    assert summary["local_bundles_used"] is False
    bundle_dir = Path(summary["bundle_dir"]).resolve()
    assert (bundle_dir / "manifest.json").exists()
    summary_md = bundle_dir / "summary.md"
    assert summary_md.exists()
    summary_text = summary_md.read_text(encoding="utf-8")
    assert "Public data" in summary_text
    assert "OOS error" in summary_text
    proofpack_dir = Path(summary["proofpack_dir"]).resolve()
    turbulence_dirs = list((proofpack_dir / "turbulence").rglob("turbulence_metadata.json"))
    assert turbulence_dirs
    ledgers_root = turbulence_dirs[0].parent / "ledgers"
    assert (ledgers_root / "blind.jsonl").exists()
    assert not (ledgers_root / "sighted.jsonl").exists()


def test_run_public_data_workflow_uses_local_bundles(
    tmp_path: Path,
    sample_tracks_path: Path,
) -> None:
    mirror_root = tmp_path / "mirror"
    key_path = tmp_path / "key.bin"
    _write_key(key_path)

    local_root = tmp_path / "shelf"
    dataset_dir = local_root / "osf" / "manual_dataset"
    raw_dir = dataset_dir / "raw"
    raw_dir.mkdir(parents=True, exist_ok=True)
    anchors = {
        "temperature_K": 298.15,
        "pixel_size_m": 1.6e-07,
        "time_step_s": 0.01,
        "bead_radius_um": 0.5,
        "viscosity_pa_s": 0.001,
    }
    (dataset_dir / "anchors.json").write_text(json.dumps(anchors), encoding="utf-8")
    (raw_dir / "tracks.csv").write_text(sample_tracks_path.read_text(encoding="utf-8"), encoding="utf-8")

    (mirror_root / "jhtdb" / "sample").mkdir(parents=True, exist_ok=True)
    sample_turbulence = Path(__file__).resolve().parents[1] / "data" / "turbulence" / "sample_jhtdb_samples.json"
    (mirror_root / "jhtdb" / "sample" / "jhtdb_samples.json").write_text(
        sample_turbulence.read_text(encoding="utf-8"),
        encoding="utf-8",
    )

    empty_candidates = tmp_path / "candidates.json"
    empty_candidates.write_text(json.dumps({"candidates": []}), encoding="utf-8")

    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "scripts.run_public_data_workflow",
            "--source",
            "osf",
            "--candidates",
            str(empty_candidates),
            "--mirror-root",
            str(mirror_root),
            "--local-bundle-root",
            str(local_root),
            "--output-root",
            str(tmp_path / "artifacts" / "experiments"),
            "--signing-key",
            str(key_path),
            "--run-tag",
            "fallback-test",
            "--turbulence-dataset",
            "sample",
        ],
        check=True,
        text=True,
        capture_output=True,
    )

    summary = json.loads(completed.stdout.splitlines()[-1])
    assert summary["selected_count"] == 1
    assert summary["local_bundles_used"] is True
    proofpack_dir = Path(summary["proofpack_dir"]).resolve()
    ledgers_dir = proofpack_dir / "public_data" / "osf" / "manual_dataset" / "ledgers"
    assert ledgers_dir.exists(), "Public dataset ledgers were not generated"

