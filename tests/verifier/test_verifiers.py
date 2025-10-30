"""Regression tests for verifier checkers against generated artefacts."""

from __future__ import annotations

from pathlib import Path

from experiments.run_cross_domain import main as cross_domain_main
from experiments.run_cwd import main as cwd_main
from experiments.run_einstein import main as einstein_main
from experiments.run_entropy import main as entropy_main
from experiments.run_landauer import main as landauer_main
from verifier.check_cross_domain import verify_cross_domain
from verifier.check_cwd import verify_cwd
from verifier.check_einstein import verify_einstein
from verifier.check_entropy import verify_entropy
from verifier.check_landauer import verify_landauer


def test_verify_landauer_from_synthetic(tmp_path: Path) -> None:
    run_dir = tmp_path / "landauer"
    landauer_main(
        [
            "--output-dir",
            str(run_dir),
            "--seeds",
            "0",
            "--temps",
            "1.0",
            "--trials-per-condition",
            "1",
            "--steps",
            "12",
            "--synthetic-ledger",
            "experiments/data/sample_ledger.jsonl",
        ]
    )
    _, result = verify_landauer(run_dir, epsilon=0.05, out_path=tmp_path / "landauer_verifier.json")
    assert result["status"] is True
    assert result["trial_count"] > 0


def test_verify_einstein_from_synthetic(tmp_path: Path) -> None:
    run_dir = tmp_path / "einstein"
    einstein_main(
        [
            "--output-dir",
            str(run_dir),
            "--seeds",
            "0",
            "--temps",
            "1.0",
            "--trials-per-condition",
            "1",
            "--steps",
            "16",
            "--synthetic-ledger",
            "experiments/data/sample_einstein.jsonl",
        ]
    )
    _, result = verify_einstein(run_dir, delta=0.1, out_path=tmp_path / "einstein_verifier.json")
    assert result["status"] is True
    assert result["trial_count"] > 0


def test_verify_entropy_real_run(tmp_path: Path) -> None:
    run_dir = tmp_path / "entropy"
    entropy_main(
        [
            "--output-dir",
            str(run_dir),
            "--seeds",
            "0",
            "--temps",
            "1.0",
            "--trials-per-condition",
            "1",
            "--steps",
            "48",
        ]
    )
    _, result = verify_entropy(run_dir, out_path=tmp_path / "entropy_verifier.json")
    assert result["status"] is True
    assert result["trial_count"] > 0


def test_verify_cwd_multi_protocol(tmp_path: Path) -> None:
    sighted_dir = tmp_path / "cwd_sighted"
    blind_dir = tmp_path / "cwd_blind"
    destroyed_dir = tmp_path / "cwd_destroyed"

    common_args = [
        "--seeds",
        "2",
        "--temps",
        "0.9",
        "--trials-per-condition",
        "1",
        "--modules",
        "3",
        "--steps-per-module",
        "4",
    ]

    cwd_main(["--output-dir", str(sighted_dir), "--protocol", "sighted", *common_args])
    cwd_main(["--output-dir", str(blind_dir), "--protocol", "blind", *common_args])
    cwd_main(["--output-dir", str(destroyed_dir), "--protocol", "destroyed", *common_args])

    _, result = verify_cwd(
        sighted_dir=sighted_dir,
        blind_dir=blind_dir,
        destroyed_dir=destroyed_dir,
        epsilon=0.2,
        eta=0.2,
        out_path=tmp_path / "cwd_verifier.json",
    )
    assert result["status"] is True
    assert result["sighted_trials"]
    assert result["penalty_checks"]


def test_verify_cross_domain_protocols(tmp_path: Path) -> None:
    sighted_dir = tmp_path / "cross_sighted"
    blind_dir = tmp_path / "cross_blind"

    cross_domain_main(
        [
            "--output-dir",
            str(sighted_dir),
            "--protocol",
            "sighted",
            "--seeds",
            "0",
            "1",
            "2",
            "--trials-per-condition",
            "3",
        ]
    )
    cross_domain_main(
        [
            "--output-dir",
            str(blind_dir),
            "--protocol",
            "blind",
            "--seeds",
            "0",
            "1",
            "--trials-per-condition",
            "2",
        ]
    )

    _, sighted = verify_cross_domain(
        sighted_dir,
        out_path=tmp_path / "cross_sighted_verifier.json",
    )
    assert sighted["status"] is True

    _, blind = verify_cross_domain(
        blind_dir,
        out_path=tmp_path / "cross_blind_verifier.json",
    )
    assert blind["status"] is True
