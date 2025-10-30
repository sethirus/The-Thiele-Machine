"""Integration tests for the unified THIELE proofpack verifier."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from experiments.public_data import spt_protocol
from experiments.turbulence import run_dataset as turbulence_run_dataset
from experiments.run_cross_domain import main as cross_domain_main
from experiments.run_cwd import main as cwd_main
from experiments.run_einstein import main as einstein_main
from experiments.run_entropy import main as entropy_main
from experiments.run_landauer import main as landauer_main
from tools.thiele_verifier import verify_proofpack


def _build_phase_runs(base_dir: Path) -> None:
    landauer_dir = base_dir / "landauer"
    landauer_main(
        [
            "--output-dir",
            str(landauer_dir),
            "--seeds",
            "0",
            "--temps",
            "1.0",
            "--trials-per-condition",
            "1",
            "--steps",
            "12",
        ]
    )

    einstein_dir = base_dir / "einstein"
    einstein_main(
        [
            "--output-dir",
            str(einstein_dir),
            "--seeds",
            "0",
            "--temps",
            "1.0",
            "--trials-per-condition",
            "1",
            "--steps",
            "24",
        ]
    )

    entropy_dir = base_dir / "entropy"
    entropy_main(
        [
            "--output-dir",
            str(entropy_dir),
            "--seeds",
            "0",
            "--temps",
            "1.0",
            "--trials-per-condition",
            "1",
            "--steps",
            "32",
        ]
    )

    cwd_root = base_dir / "cwd"
    for protocol in ("sighted", "blind", "destroyed"):
        cwd_main(
            [
                "--output-dir",
                str(cwd_root / protocol),
                "--protocol",
                protocol,
                "--seeds",
                "1",
                "--temps",
                "0.9",
                "--trials-per-condition",
                "1",
                "--modules",
                "3",
                "--steps-per-module",
                "4",
            ]
        )

    cross_root = base_dir / "cross_domain"
    cross_common = [
        "--seeds",
        "0",
        "1",
        "--trials-per-condition",
        "3",
        "--modules",
        "5",
        "--mu-base",
        "0.24",
        "--mu-jitter",
        "0.03",
        "--runtime-base",
        "1.1",
        "--runtime-scale",
        "0.75",
    ]
    cross_domain_main(
        [
            "--output-dir",
            str(cross_root / "sighted"),
            "--protocol",
            "sighted",
            *cross_common,
        ]
    )
    cross_domain_main(
        [
            "--output-dir",
            str(cross_root / "blind"),
            "--protocol",
            "blind",
            *cross_common,
        ]
    )
    cross_domain_main(
        [
            "--output-dir",
            str(cross_root / "destroyed"),
            "--protocol",
            "destroyed",
            *cross_common,
        ]
    )

    turbulence_source = base_dir / "turbulence_source"
    turbulence_source.mkdir()
    sample_src = Path(__file__).resolve().parents[1] / "data" / "turbulence" / "sample_jhtdb_samples.json"
    (turbulence_source / "jhtdb_samples.json").write_text(sample_src.read_text(encoding="utf-8"))
    turbulence_output = base_dir / "turbulence" / "sample"
    turbulence_run_dataset(turbulence_source, turbulence_output, seed=13)


def test_verify_proofpack_success(tmp_path: Path) -> None:
    proofpack_dir = tmp_path / "proofpack"
    proofpack_dir.mkdir()
    _build_phase_runs(proofpack_dir)

    result = verify_proofpack(proofpack_dir)
    assert result["status"] is True
    assert result["verdict"] == "THIELE_OK"
    verifier_dir = proofpack_dir / "verifier"
    aggregate_path = verifier_dir / "proofpack_verifier.json"
    assert aggregate_path.exists()
    verdict_path = verifier_dir / "THIELE_OK"
    assert verdict_path.exists()
    assert not (verifier_dir / "THIELE_FAIL").exists()
    assert result["verdict_path"] == str(verdict_path.relative_to(proofpack_dir))
    payload = json.loads(aggregate_path.read_text())
    assert payload["status"] is True
    assert payload["verdict"] == "THIELE_OK"
    assert set(payload["phases"].keys()) == {
        "landauer",
        "einstein",
        "entropy",
        "cwd",
        "cross_domain",
    }
    landauer_runs = payload["phases"]["landauer"]["runs"]
    assert landauer_runs and landauer_runs[0]["highlights"]
    assert payload["phases"]["landauer"]["highlights"]
    assert payload["public_data"]["status"] is True
    assert payload["public_data"]["datasets"] == []
    turbulence_payload = payload.get("turbulence", {})
    assert turbulence_payload.get("status") is True
    assert turbulence_payload.get("datasets")
    dataset_highlights = turbulence_payload["datasets"][0]["highlights"]
    assert dataset_highlights.get("time_count") == 4
    assert dataset_highlights.get("point_count") == 4
    assert dataset_highlights.get("skipped_protocols") == []


def test_verify_proofpack_with_public_dataset(tmp_path: Path) -> None:
    data_root = tmp_path / "mirrored"
    dataset_dir = data_root / "dataset"
    dataset_dir.mkdir(parents=True)
    (dataset_dir / "raw").mkdir()
    sample_root = Path(__file__).resolve().parents[1] / "data" / "public"
    (dataset_dir / "anchors.json").write_text((sample_root / "sample_anchors.json").read_text())
    (dataset_dir / "raw" / "tracks.csv").write_text((sample_root / "sample_tracks.csv").read_text())

    proofpack_dir = tmp_path / "proofpack"
    proofpack_dir.mkdir()
    _build_phase_runs(proofpack_dir)
    output_dir = proofpack_dir / "public_data" / "osf" / "sample"
    spt_protocol.run_dataset(dataset_dir, output_dir, seed=5)

    result = verify_proofpack(proofpack_dir)
    assert result["public_data"]["status"] is True
    assert result["public_data"]["datasets"]
    assert result["turbulence"]["status"] is True
    assert result["turbulence"]["datasets"]
    assert result["turbulence"]["highlights"].get("max_point_count") == 4
    assert result["turbulence"]["datasets"][0]["highlights"].get("skipped_protocols") == []


def test_verify_proofpack_failure_writes_flag(tmp_path: Path) -> None:
    proofpack_dir = tmp_path / "proofpack"
    proofpack_dir.mkdir()
    _build_phase_runs(proofpack_dir)

    bad_dataset_dir = proofpack_dir / "public_data" / "osf" / "incomplete"
    bad_dataset_dir.mkdir(parents=True)
    (bad_dataset_dir / "public_spt_metadata.json").write_text("{}\n")

    result = verify_proofpack(proofpack_dir, spearman_threshold=0.999999)
    assert result["status"] is False
    assert result["verdict"] == "THIELE_FAIL"
    verifier_dir = proofpack_dir / "verifier"
    fail_flag = verifier_dir / "THIELE_FAIL"
    assert fail_flag.exists()
    assert not (verifier_dir / "THIELE_OK").exists()


def test_cli_prints_thiele_ok(tmp_path: Path) -> None:
    proofpack_dir = tmp_path / "proofpack"
    proofpack_dir.mkdir()
    _build_phase_runs(proofpack_dir)

    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "tools.thiele_verifier",
            str(proofpack_dir),
        ],
        capture_output=True,
        text=True,
        check=True,
    )
    assert completed.stdout.strip() == "THIELE_OK"
    assert completed.returncode == 0

def test_cli_highlights_flag(tmp_path: Path) -> None:
    proofpack_dir = tmp_path / "proofpack"
    proofpack_dir.mkdir()
    _build_phase_runs(proofpack_dir)

    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "tools.thiele_verifier",
            str(proofpack_dir),
            "--highlights",
        ],
        capture_output=True,
        text=True,
        check=True,
    )
    stdout = completed.stdout.strip().splitlines()
    assert any("Landauer highlights" in line for line in stdout)
    assert stdout[-1] == "THIELE_OK"
    assert completed.returncode == 0

