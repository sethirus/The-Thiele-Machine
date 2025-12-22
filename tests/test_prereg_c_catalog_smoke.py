from __future__ import annotations

import socket
from pathlib import Path

import pytest


def _can_connect_to_gwosc() -> bool:
    """Check if we can connect to GWOSC API."""
    try:
        socket.create_connection(("gwosc.org", 443), timeout=2)
        return True
    except (socket.timeout, OSError):
        return False


@pytest.mark.parametrize("release", ["GWTC-1-confident"])
def test_prereg_c_catalog_smoke(tmp_path: Path, release: str) -> None:
    if not _can_connect_to_gwosc():
        pytest.skip("Cannot connect to gwosc.org (network access required)")

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
