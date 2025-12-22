from __future__ import annotations

from pathlib import Path

import pytest


def _has_csv_files(data_dir: Path) -> bool:
    """Check if data directory contains CSV files required for the test."""
    return bool(list(data_dir.glob("*.csv")))


@pytest.mark.parametrize("split_policy", ["fit_none"])
def test_prereg_a_smoke(tmp_path: Path, split_policy: str) -> None:
    repo_root = Path(__file__).resolve().parents[1]
    tool = repo_root / "tools" / "prereg_a_landauer.py"
    data_dir = repo_root / "DATA_A"

    if not _has_csv_files(data_dir):
        pytest.skip("DATA_A directory missing CSV datafiles")

    # Use a fresh output root to avoid coupling to existing runs.
    out_root = tmp_path / "mu_landauer_a"

    import subprocess
    import sys

    subprocess.run(
        [
            sys.executable,
            str(tool),
            "--root",
            str(out_root),
            "init",
            "--split-policy",
            split_policy,
            "--sources",
            "ExamplePaper",
        ],
        check=True,
        cwd=str(repo_root),
    )

    subprocess.run(
        [
            sys.executable,
            str(tool),
            "--root",
            str(out_root),
            "ingest",
            "--split-policy",
            split_policy,
            "--sources",
            "ExamplePaper",
            "--data-dir",
            str(data_dir),
        ],
        check=True,
        cwd=str(repo_root),
    )

    # Default model is conservative, so analyze may fail; it must at least run.
    subprocess.run(
        [
            sys.executable,
            str(tool),
            "--root",
            str(out_root),
            "analyze",
            "--split-policy",
            split_policy,
            "--sources",
            "ExamplePaper",
            "--data-dir",
            str(data_dir),
        ],
        check=False,
        cwd=str(repo_root),
    )

    assert (out_root / "MANIFEST_A.json").exists()
    assert (out_root / "DATA_A_INDEX.json").exists()
    assert (out_root / "analysis_A.json").exists()
