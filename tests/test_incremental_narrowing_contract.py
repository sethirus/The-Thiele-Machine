"""The incremental observer questions are settled, and their definitions stay fixed.

KnowledgeNarrowingIncremental.v states the incremental reading of observer
narrowing and the machine size at which free learning first appears. Its code
is pinned to the commit that introduced it: this contract compares the
comment-stripped code of the file with that commit. It also asks for the Coq
theorems that settle each question.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.assumption_receipt_fingerprint import _strip_coq_comments  # noqa: E402

NFI = ROOT / "coq" / "kernel" / "nfi"
DEFINITIONS = NFI / "KnowledgeNarrowingIncremental.v"
RESULT = NFI / "KnowledgeNarrowingMinimal.v"
SETTLING = {
    "demon_refutes_incremental":
        r"~\s*incremental_observer_narrowing_priced\s+dstep\s+dcost\s+display\s+Bool\.bool_dec",
    "free_incremental_narrowing_with_three":
        r"free_incremental_narrowing_with\s+3",
    "no_free_incremental_narrowing_below_three":
        r"forall\s+n\s*,\s*n\s*<=\s*2\s*->\s*~\s*free_incremental_narrowing_with\s+n",
}


def _code(text: str) -> str:
    return " ".join(_strip_coq_comments(text).split())


def test_definitions_are_unchanged_since_introduced():
    commit = subprocess.run(
        ["git", "log", "--diff-filter=A", "--format=%H", "--",
         "coq/kernel/nfi/KnowledgeNarrowingIncremental.v"],
        cwd=ROOT, check=True, capture_output=True, text=True,
    ).stdout.split()[-1]
    pinned = subprocess.run(
        ["git", "show", f"{commit}:coq/kernel/nfi/KnowledgeNarrowingIncremental.v"],
        cwd=ROOT, check=True, capture_output=True, text=True,
    ).stdout
    assert _code(DEFINITIONS.read_text()) == _code(pinned)


def test_result_file_is_built_with_the_project():
    assert RESULT.exists(), "KnowledgeNarrowingMinimal.v does not exist"
    project = (ROOT / "coq" / "_CoqProject").read_text().splitlines()
    assert "kernel/nfi/KnowledgeNarrowingMinimal.v" in project
    compiled = RESULT.with_suffix(".vo")
    assert compiled.exists() and compiled.stat().st_mtime >= RESULT.stat().st_mtime


def test_each_question_is_settled():
    assert RESULT.exists(), "KnowledgeNarrowingMinimal.v does not exist"
    code = _code(RESULT.read_text())
    for name, statement in SETTLING.items():
        assert re.search(rf"Theorem {name}\s*:\s*{statement}\s*\.", code), name


def test_result_file_has_no_proof_holes_or_axioms():
    assert RESULT.exists(), "KnowledgeNarrowingMinimal.v does not exist"
    assert not re.search(r"\b(Admitted|admit|Axiom|Parameter|Hypothesis)\b", RESULT.read_text())
