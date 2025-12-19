from __future__ import annotations

from pathlib import Path

import pytest


@pytest.mark.parametrize("release", ["GWTC-1-confident"])
def test_prereg_c_catalog_smoke(tmp_path: Path, release: str) -> None:
    repo_root = Path(__file__).resolve().parents[1]
    tool = repo_root / "tools" / "prereg_c_gwosc_catalog.py"

    out_root = tmp_path / "gwosc_blind_c"

    import subprocess
    import sys

    subprocess.run(
        [
            sys.executable,
            str(tool),
            "--root",
            str(out_root),
            "init",
            "--releases",
            release,
            "--max-events",
            "5",
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
            "fetch",
            "--releases",
            release,
            "--max-events",
            "5",
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
            "analyze",
            "--releases",
            release,
            "--max-events",
            "5",
        ],
        check=True,
        cwd=str(repo_root),
    )

    assert (out_root / "MANIFEST_C.json").exists()
    assert (out_root / "events.jsonl").exists()
    assert (out_root / "DATA_C_INDEX.json").exists()
    assert (out_root / "fetch_receipt.json").exists()
    assert (out_root / "releases").exists()
    assert (out_root / "analysis_C.json").exists()
