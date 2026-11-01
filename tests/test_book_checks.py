"""The book's own checks pass.

Each chapter of the monograph that counts something has a Python check that
tries every small case, and the shown claims have short formal proofs beside
them. Every check must report zero failures, and every proof must compile with
no assumption beyond the standard library's real numbers where it uses them.
"""
from __future__ import annotations

import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
CHECKS = ROOT / "monograph" / "checks"
PYTHON_CHECKS = sorted(CHECKS.glob("*.py"))
PROOFS = sorted(CHECKS.glob("*.v"))
REAL_NUMBER_AXIOMS = {
    "ClassicalDedekindReals.sig_forall_dec",
    "ClassicalDedekindReals.sig_not_dec",
    "FunctionalExtensionality.functional_extensionality_dep",
    "Classical_Prop.classic",
}


def test_there_are_checks() -> None:
    assert PYTHON_CHECKS and PROOFS


@pytest.mark.slow
@pytest.mark.parametrize("check", PYTHON_CHECKS, ids=lambda p: p.name)
def test_python_check_finds_no_failure(check: Path) -> None:
    out = subprocess.run([sys.executable, check.name], cwd=CHECKS, capture_output=True, text=True, timeout=280)
    assert out.returncode == 0, out.stderr[-2000:]
    counts = [int(n) for n in re.findall(r"failures: (\d+)", out.stdout)]
    assert counts and all(n == 0 for n in counts), out.stdout[-2000:]


@pytest.mark.coq
@pytest.mark.parametrize("proof", PROOFS, ids=lambda p: p.name)
def test_proof_compiles_closed(proof: Path, tmp_path: Path) -> None:
    if shutil.which("coqc") is None:
        pytest.skip("coqc not on PATH")
    minimal = ROOT / "minimal"
    work = tmp_path / proof.name
    work.write_text(proof.read_text(encoding="utf-8"), encoding="utf-8")
    out = subprocess.run(["coqc", "-Q", str(minimal), "Minimal", str(work)],
                         capture_output=True, text=True, timeout=580)
    assert out.returncode == 0, (out.stdout + out.stderr)[-3000:]
    for block in out.stdout.split("Axioms:")[1:]:
        names = set(re.findall(r"^([A-Za-z_][\w.']*) :", block, flags=re.M))
        assert names <= REAL_NUMBER_AXIOMS, sorted(names - REAL_NUMBER_AXIOMS)
