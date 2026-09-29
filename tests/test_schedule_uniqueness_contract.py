"""The schedule-free uniqueness conjectures are settled, and their definitions stay fixed.

StructuralCoreRound3.v states uniqueness up to the price schedule in two
strengths. Its code is pinned to the commit that introduced it: this contract
compares the comment-stripped code of the file with that commit. It also asks
for a Coq theorem that settles each strength, in either direction.
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
DEFINITIONS = FOUNDATION / "StructuralCoreRound3.v"
RESULT = FOUNDATION / "StructuralScheduleUniqueness.v"


def _code(text: str) -> str:
    return " ".join(_strip_coq_comments(text).split())


def _introducing_commit() -> str:
    return subprocess.run(
        ["git", "log", "--diff-filter=A", "--format=%H", "--",
         "coq/kernel/foundation/StructuralCoreRound3.v"],
        cwd=ROOT, check=True, capture_output=True, text=True,
    ).stdout.split()[-1]


def _settles(source: str, conjecture: str) -> bool:
    proved = rf"Theorem\s+\w+\s*:\s*{conjecture}\s*\."
    refuted = rf"Theorem\s+\w+\s*:\s*~\s*{conjecture}\s*\."
    return bool(re.search(proved, source) or re.search(refuted, source))


def test_definitions_are_unchanged_since_introduced():
    commit = _introducing_commit()
    pinned = subprocess.run(
        ["git", "show", f"{commit}:coq/kernel/foundation/StructuralCoreRound3.v"],
        cwd=ROOT, check=True, capture_output=True, text=True,
    ).stdout
    assert _code(DEFINITIONS.read_text()) == _code(pinned)


def test_result_file_is_built_with_the_project():
    assert RESULT.exists(), "StructuralScheduleUniqueness.v does not exist"
    project = (ROOT / "coq" / "_CoqProject").read_text().splitlines()
    assert "kernel/foundation/StructuralScheduleUniqueness.v" in project
    compiled = RESULT.with_suffix(".vo")
    assert compiled.exists() and compiled.stat().st_mtime >= RESULT.stat().st_mtime


def test_both_strengths_are_settled():
    assert RESULT.exists(), "StructuralScheduleUniqueness.v does not exist"
    source = RESULT.read_text()
    assert _settles(source, "uniqueness_round3a")
    assert _settles(source, "uniqueness_round3b")


def test_result_file_has_no_proof_holes_or_axioms():
    assert RESULT.exists(), "StructuralScheduleUniqueness.v does not exist"
    assert not re.search(r"\b(Admitted|admit|Axiom|Parameter|Hypothesis)\b", RESULT.read_text())
