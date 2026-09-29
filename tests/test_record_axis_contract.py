"""The record-axis conjectures are settled, and their definitions stay fixed.

StructuralCoreRound4.v states the record axis over any base, for one record
and for a pair. Its code is pinned to the commit that introduced it: this contract
compares the comment-stripped code of the file with that commit. It also asks
for a Coq theorem that settles each form, in either direction.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.assumption_receipt_fingerprint import _strip_coq_comments  # noqa: E402

FOUNDATION = ROOT / "coq" / "kernel" / "foundation"
DEFINITIONS = FOUNDATION / "StructuralCoreRound4.v"
RESULT = FOUNDATION / "StructuralRecordAxis.v"


def _code(text: str) -> str:
    return " ".join(_strip_coq_comments(text).split())


def _introducing_commit() -> str:
    return subprocess.run(
        ["git", "log", "--diff-filter=A", "--format=%H", "--",
         "coq/kernel/foundation/StructuralCoreRound4.v"],
        cwd=ROOT, check=True, capture_output=True, text=True,
    ).stdout.split()[-1]


def _settles(source: str, conjecture: str) -> bool:
    proved = rf"Theorem\s+\w+\s*:\s*{conjecture}\s*\."
    refuted = rf"Theorem\s+\w+\s*:\s*~\s*{conjecture}\s*\."
    return bool(re.search(proved, source) or re.search(refuted, source))


def test_definitions_are_unchanged_since_introduced():
    commit = _introducing_commit()
    pinned = subprocess.run(
        ["git", "show", f"{commit}:coq/kernel/foundation/StructuralCoreRound4.v"],
        cwd=ROOT, check=True, capture_output=True, text=True,
    ).stdout
    assert _code(DEFINITIONS.read_text()) == _code(pinned)


def test_result_file_is_built_with_the_project():
    assert RESULT.exists(), "StructuralRecordAxis.v does not exist"
    project = (ROOT / "coq" / "_CoqProject").read_text().splitlines()
    assert "kernel/foundation/StructuralRecordAxis.v" in project
    compiled = RESULT.with_suffix(".vo")
    assert compiled.exists() and compiled.stat().st_mtime >= RESULT.stat().st_mtime


def test_both_forms_are_settled():
    assert RESULT.exists(), "StructuralRecordAxis.v does not exist"
    source = RESULT.read_text()
    assert _settles(source, "uniqueness_round4")
    assert _settles(source, "uniqueness_round4_pair")


def test_result_file_has_no_proof_holes_or_axioms():
    assert RESULT.exists(), "StructuralRecordAxis.v does not exist"
    assert not re.search(r"\b(Admitted|admit|Axiom|Parameter|Hypothesis)\b", RESULT.read_text())
