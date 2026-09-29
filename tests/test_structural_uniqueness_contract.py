"""The uniqueness conjectures are settled, and their definitions stay fixed.

StructuralCore.v and StructuralCoreRound2.v define the weak and strong forms
of the uniqueness question. Their code is pinned to commit 34971852: this
contract compares the comment-stripped code of each file with that commit,
so comments may be edited but no definition can change. It also asks for a
Coq theorem that settles each conjecture, in either direction.
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
RESULT = FOUNDATION / "StructuralUniqueness.v"
PINNED_COMMIT = "34971852cf2e2e5a7892e5fb85b18740ce44af0a"
FROZEN = ["StructuralCore.v", "StructuralCoreRound2.v"]


def _code(text: str) -> str:
    return " ".join(_strip_coq_comments(text).split())


def _settles(source: str, conjecture: str) -> bool:
    proved = rf"Theorem\s+\w+\s*:\s*{conjecture}\s*\."
    refuted = rf"Theorem\s+\w+\s*:\s*~\s*{conjecture}\s*\."
    return bool(re.search(proved, source) or re.search(refuted, source))


def test_frozen_definitions_are_unchanged():
    for name in FROZEN:
        pinned = subprocess.run(
            ["git", "show", f"{PINNED_COMMIT}:coq/kernel/foundation/{name}"],
            cwd=ROOT, check=True, capture_output=True, text=True,
        ).stdout
        current = (FOUNDATION / name).read_text()
        assert _code(current) == _code(pinned), (
            f"the code of {name} differs from commit {PINNED_COMMIT[:8]}"
        )


def test_result_file_is_built_with_the_project():
    assert RESULT.exists(), "StructuralUniqueness.v does not exist"
    project = (ROOT / "coq" / "_CoqProject").read_text().splitlines()
    assert "kernel/foundation/StructuralUniqueness.v" in project
    compiled = RESULT.with_suffix(".vo")
    assert compiled.exists() and compiled.stat().st_mtime >= RESULT.stat().st_mtime


def test_round_one_is_settled():
    assert RESULT.exists(), "StructuralUniqueness.v does not exist"
    assert _settles(RESULT.read_text(), "uniqueness_round1")


def test_round_two_is_settled():
    assert RESULT.exists(), "StructuralUniqueness.v does not exist"
    assert _settles(RESULT.read_text(), "uniqueness_round2")


def test_result_file_has_no_proof_holes_or_axioms():
    assert RESULT.exists(), "StructuralUniqueness.v does not exist"
    source = RESULT.read_text()
    assert not re.search(r"\b(Admitted|admit|Axiom|Parameter|Hypothesis)\b", source)
