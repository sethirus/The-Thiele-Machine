"""The record-axis questions are settled, and their statements keep their shape.

StructuralCoreAnyBase.v states the record axis over any base, for one record
and for a pair. This contract checks the comment-stripped code of both
statements. It also asks for a Coq theorem that settles each form, in either
direction.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.assumption_receipt_fingerprint import _strip_coq_comments  # noqa: E402

FOUNDATION = ROOT / "coq" / "kernel" / "foundation"
DEFINITIONS = FOUNDATION / "StructuralCoreAnyBase.v"
RESULT = FOUNDATION / "StructuralRecordAxis.v"


def _code(text: str) -> str:
    return " ".join(_strip_coq_comments(text).split())


def _settles(source: str, conjecture: str) -> bool:
    proved = rf"Theorem\s+\w+\s*:\s*{conjecture}\s*\."
    refuted = rf"Theorem\s+\w+\s*:\s*~\s*{conjecture}\s*\."
    return bool(re.search(proved, source) or re.search(refuted, source))


def test_definitions_keep_their_shape():
    code = _code(DEFINITIONS.read_text())
    assert " ".join('Definition record_axis_is_latch : Prop := forall M B C, HonestBaseExtension M B C -> exists h, latch_factorization M B C h.'.split()) in code
    assert " ".join('Definition record_pair_is_two_latches : Prop := forall M B C c1 c2, HonestBasePairExtension M B C c1 c2 -> exists h1 h2, pair_latch_factorization M B C c1 c2 h1 h2.'.split()) in code
    assert " ".join('Definition HonestBaseExtension (M : RCM) (B : BaseMachine) (C : BaseCover M B) : Prop := computation_driven M B C /\\ ledger_carried M /\\ rc_a2 M /\\ record_permanent M /\\ reachable_record_write M.'.split()) in code


def test_result_file_is_built_with_the_project():
    assert RESULT.exists(), "StructuralRecordAxis.v does not exist"
    project = (ROOT / "coq" / "_CoqProject").read_text().splitlines()
    assert "kernel/foundation/StructuralRecordAxis.v" in project
    compiled = RESULT.with_suffix(".vo")
    assert compiled.exists() and compiled.stat().st_mtime >= RESULT.stat().st_mtime


def test_both_forms_are_settled():
    assert RESULT.exists(), "StructuralRecordAxis.v does not exist"
    source = RESULT.read_text()
    assert _settles(source, "record_axis_is_latch")
    assert _settles(source, "record_pair_is_two_latches")


def test_result_file_has_no_proof_holes_or_axioms():
    assert RESULT.exists(), "StructuralRecordAxis.v does not exist"
    assert not re.search(r"\b(Admitted|admit|Axiom|Parameter|Hypothesis)\b", RESULT.read_text())
