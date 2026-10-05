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
EARNED = REPO_ROOT / "minimal" / "EarnedCore.v"
UNIVERSAL = REPO_ROOT / "minimal" / "UniversalThiele.v"
GENERIC = REPO_ROOT / "minimal" / "EarnedGeneric.v"
COMPLETE = REPO_ROOT / "minimal" / "ThieleComplete.v"
DEMO = REPO_ROOT / "minimal" / "nofi_demo.py"
EXPECTED_CLOSED = 10
EARNED_EXPECTED_CLOSED = 33
UNIVERSAL_EXPECTED_CLOSED = 22
GENERIC_EXPECTED_CLOSED = 31
COMPLETE_EXPECTED_CLOSED = 28


def test_nofi_demo_self_checks():
    proc = subprocess.run(
        [sys.executable, str(DEMO)],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=120,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "all 9 checks passed" in proc.stdout
    # The three claims the demo's sections make, visible in its own output:
    # the exhaustive sweep found nothing, the conservation identity held
    # everywhere, and the under-floor strategy paid in errors.
    assert "zero counterexamples" in proc.stdout
    assert "on every instance" in proc.stdout
    assert "discount is paid in errors" in proc.stdout


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


@pytest.mark.coq
def test_earned_core_compiles_axiom_free(tmp_path):
    """minimal/EarnedCore.v, the smallest machine that earns its commitments,
    compiles with plain coqc against the standard library alone, and every
    theorem it prints assumptions for is closed."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    work = tmp_path / "EarnedCore.v"
    work.write_text(EARNED.read_text())
    proc = subprocess.run(
        ["coqc", str(work)],
        cwd=str(tmp_path),
        capture_output=True,
        text=True,
        timeout=600,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    closed = proc.stdout.count("Closed under the global context")
    assert closed == EARNED_EXPECTED_CLOSED, (
        f"expected {EARNED_EXPECTED_CLOSED} closed-assumption receipts, saw {closed}\n"
        + proc.stdout
    )
    assert "Axioms:" not in proc.stdout


@pytest.mark.coq
def test_universal_thiele_compiles_axiom_free(tmp_path):
    """minimal/UniversalThiele.v, the host that runs any small-machine program
    as a guest and enforces the guest's record and toll in its own step,
    compiles with plain coqc against EarnedCore.v and the standard library,
    and every theorem it prints assumptions for is closed."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    lib = tmp_path / "minimal"
    lib.mkdir()
    (lib / "EarnedCore.v").write_text(EARNED.read_text())
    (lib / "UniversalThiele.v").write_text(UNIVERSAL.read_text())
    for name in ("EarnedCore.v", "UniversalThiele.v"):
        proc = subprocess.run(
            ["coqc", "-Q", "minimal", "Minimal", f"minimal/{name}"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=600,
        )
        assert proc.returncode == 0, proc.stdout + proc.stderr
    closed = proc.stdout.count("Closed under the global context")
    assert closed == UNIVERSAL_EXPECTED_CLOSED, (
        f"expected {UNIVERSAL_EXPECTED_CLOSED} closed-assumption receipts, saw {closed}\n"
        + proc.stdout
    )
    assert "Axioms:" not in proc.stdout


@pytest.mark.coq
def test_earned_generic_compiles_axiom_free(tmp_path):
    """minimal/EarnedGeneric.v, the small machine over any property language
    with a checker proved equal to its meaning, including a "sorted" check on
    a list encoded in a counter, compiles with plain coqc against the
    standard library alone, and every theorem it prints assumptions for is
    closed."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    work = tmp_path / "EarnedGeneric.v"
    work.write_text(GENERIC.read_text())
    proc = subprocess.run(
        ["coqc", str(work)],
        cwd=str(tmp_path),
        capture_output=True,
        text=True,
        timeout=600,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    closed = proc.stdout.count("Closed under the global context")
    assert closed == GENERIC_EXPECTED_CLOSED, (
        f"expected {GENERIC_EXPECTED_CLOSED} closed-assumption receipts, saw {closed}\n"
        + proc.stdout
    )
    assert "Axioms:" not in proc.stdout


@pytest.mark.coq
def test_thiele_complete_compiles_axiom_free(tmp_path):
    """minimal/ThieleComplete.v, the strong definition of a Thiele-complete
    machine (universal base, earned record, exact toll, a check that can
    fail), with the small machine proved to meet it and every clock machine
    proved to fail it, compiles with plain coqc against EarnedCore.v,
    EarnedGeneric.v and the standard library, and every theorem it prints
    assumptions for is closed."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    lib = tmp_path / "minimal"
    lib.mkdir()
    (lib / "EarnedCore.v").write_text(EARNED.read_text())
    (lib / "EarnedGeneric.v").write_text(GENERIC.read_text())
    (lib / "ThieleComplete.v").write_text(COMPLETE.read_text())
    for name in ("EarnedCore.v", "EarnedGeneric.v", "ThieleComplete.v"):
        proc = subprocess.run(
            ["coqc", "-Q", "minimal", "Minimal", f"minimal/{name}"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=600,
        )
        assert proc.returncode == 0, proc.stdout + proc.stderr
    closed = proc.stdout.count("Closed under the global context")
    assert closed == COMPLETE_EXPECTED_CLOSED, (
        f"expected {COMPLETE_EXPECTED_CLOSED} closed-assumption receipts, saw {closed}\n"
        + proc.stdout
    )
    assert "Axioms:" not in proc.stdout
