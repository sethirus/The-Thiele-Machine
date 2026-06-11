"""Keep the front-door artifact honest: minimal/MuCore.v has to stay minimal,
green, and axiom-free, because it's the first thing I ask anyone to compile
before reading a word of prose.

If it ever stops building from a clean checkout, or any theorem quietly stops
being closed under the global context, the whole "don't take my word, run it"
pitch breaks and nobody notices. So this test notices. Same job for
minimal/nofi_demo.py, the clean-room measurement that re-derives the floor
with no Thiele code in the room.
"""

import shutil
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
MUCORE = REPO_ROOT / "minimal" / "MuCore.v"
DEMO = REPO_ROOT / "minimal" / "nofi_demo.py"
EXPECTED_CLOSED = 10


def test_nofi_demo_self_checks():
    proc = subprocess.run(
        [sys.executable, str(DEMO)],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=120,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "all 8 checks passed" in proc.stdout


@pytest.mark.coq
def test_minimal_core_compiles_axiom_free(tmp_path):
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    work = tmp_path / "MuCore.v"
    work.write_text(MUCORE.read_text())
    proc = subprocess.run(
        ["coqc", str(work)],
        cwd=str(tmp_path),
        capture_output=True,
        text=True,
        timeout=300,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    closed = proc.stdout.count("Closed under the global context")
    assert closed == EXPECTED_CLOSED, (
        f"expected {EXPECTED_CLOSED} closed-assumption receipts, saw {closed}\n"
        + proc.stdout
    )
    assert "Axioms:" not in proc.stdout
