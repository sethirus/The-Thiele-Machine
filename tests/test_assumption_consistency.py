"""Protect the local receipt/probe coherence check.

``scripts/check_assumption_consistency.py`` runs in the pre-commit hook. It does
not re-derive the receipt -- CI's ``make assumption-receipt-check`` owns that --
so these tests pin the properties it *does* guarantee: a stale, partial or
internally inconsistent receipt cannot pass, and a coherent one does.

Every case is built against a temporary copy of the repository layout, so no
test depends on the size of the real corpus.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "assumption_consistency", ROOT / "scripts/check_assumption_consistency.py"
)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

PROBE_REL = MODULE.FULL_ASSUMPTION_PROBE
RECEIPT_REL = MODULE.RECEIPT

PROBE_TEXT = (
    "(** probe *)\n"
    "Require Arith.\n"
    "Print Assumptions Nat.add_0_r.\n"
    "Print Assumptions Nat.add_0_l.\n"
)


def _write_repo(tmp_path: Path, *, theorems: int = 2, raw_text: str = "ok\n",
                **overrides) -> Path:
    """Lay out a minimal repo whose receipt is coherent by default."""
    (tmp_path / PROBE_REL).parent.mkdir(parents=True, exist_ok=True)
    (tmp_path / PROBE_REL).write_text(PROBE_TEXT)

    raw_rel = "artifacts/print_assumptions_all_proofs.txt"
    (tmp_path / raw_rel).parent.mkdir(parents=True, exist_ok=True)
    (tmp_path / raw_rel).write_text(raw_text)

    receipt = {
        "probe_file": PROBE_REL,
        "raw_output_file": raw_rel,
        "raw_output_sha256": hashlib.sha256(raw_text.encode()).hexdigest(),
        "addressable_theorems_probed": theorems,
        "blocks_parsed": theorems,
        "alignment_ok": True,
        "unexpected_lines_in_output": 0,
        "files_probed": 1,
        "summary": {"theorems_probed": theorems},
    }
    receipt.update(overrides)
    (tmp_path / RECEIPT_REL).write_text(json.dumps(receipt))
    return tmp_path


def _run(repo: Path) -> subprocess.CompletedProcess:
    """Run the checker with its module-level ROOT pointed at *repo*."""
    driver = (
        "import importlib.util, sys\n"
        f"spec = importlib.util.spec_from_file_location('m', {str(ROOT / 'scripts/check_assumption_consistency.py')!r})\n"
        "m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)\n"
        f"from pathlib import Path; m.ROOT = Path({str(repo)!r})\n"
        "m.main()\n"
    )
    return subprocess.run([sys.executable, "-c", driver],
                          capture_output=True, text=True, check=False)


def test_coherent_receipt_passes(tmp_path: Path) -> None:
    result = _run(_write_repo(tmp_path))
    assert result.returncode == 0, result.stderr
    assert "coherent snapshot" in result.stdout


def test_stale_receipt_is_rejected(tmp_path: Path) -> None:
    """The probe asks more questions than the receipt covers."""
    result = _run(_write_repo(tmp_path, theorems=1))
    assert result.returncode != 0
    assert "coverage mismatch" in result.stderr


def test_duplicate_queries_are_rejected(tmp_path: Path) -> None:
    repo = _write_repo(tmp_path)
    (repo / PROBE_REL).write_text(
        "(** probe *)\nRequire Arith.\n"
        "Print Assumptions Nat.add_0_r.\nPrint Assumptions Nat.add_0_r.\n"
    )
    result = _run(repo)
    assert result.returncode != 0
    assert "duplicate" in result.stderr


def test_raw_output_hash_mismatch_is_rejected(tmp_path: Path) -> None:
    repo = _write_repo(tmp_path)
    (repo / "artifacts/print_assumptions_all_proofs.txt").write_text("tampered\n")
    result = _run(repo)
    assert result.returncode != 0
    assert "hash mismatch" in result.stderr


@pytest.mark.parametrize("field,value", [
    ("blocks_parsed", 99),
    ("summary", {"theorems_probed": 99}),
    ("alignment_ok", False),
    ("unexpected_lines_in_output", 3),
])
def test_internal_inconsistency_is_rejected(tmp_path: Path, field: str, value) -> None:
    result = _run(_write_repo(tmp_path, **{field: value}))
    assert result.returncode != 0


def test_wrong_probe_name_is_rejected(tmp_path: Path) -> None:
    result = _run(_write_repo(tmp_path, probe_file="coq/Other.v"))
    assert result.returncode != 0
    assert "names probe" in result.stderr


def test_missing_receipt_is_rejected(tmp_path: Path) -> None:
    repo = _write_repo(tmp_path)
    (repo / RECEIPT_REL).unlink()
    result = _run(repo)
    assert result.returncode != 0
    assert "missing receipt" in result.stderr


def test_real_receipt_is_coherent() -> None:
    """The committed receipt must be a coherent snapshot of the committed probe."""
    result = subprocess.run(
        [sys.executable, str(ROOT / "scripts/check_assumption_consistency.py")],
        capture_output=True, text=True, check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
