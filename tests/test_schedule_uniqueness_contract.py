"""The schedule uniqueness questions are settled, and their statements keep their shape.

StructuralCoreSchedule.v states uniqueness up to the price schedule in two
strengths. This contract checks the comment-stripped code of both
statements. It also asks for a Coq theorem that settles each strength, in
either direction.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.assumption_receipt_fingerprint import _strip_coq_comments  # noqa: E402

FOUNDATION = ROOT / "coq" / "kernel" / "foundation"
DEFINITIONS = FOUNDATION / "StructuralCoreSchedule.v"
RESULT = FOUNDATION / "StructuralScheduleUniqueness.v"


def _code(text: str) -> str:
    return " ".join(_strip_coq_comments(text).split())


def _settles(source: str, conjecture: str) -> bool:
    proved = rf"Theorem\s+\w+\s*:\s*{conjecture}\s*\."
    refuted = rf"Theorem\s+\w+\s*:\s*~\s*{conjecture}\s*\."
    return bool(re.search(proved, source) or re.search(refuted, source))


def test_definitions_keep_their_shape():
    code = _code(DEFINITIONS.read_text())
    assert " ".join('Definition tied_record_schedule_uniqueness : Prop := forall M C, HonestTiedExtension M C -> equiv_mod_schedule_via M C.'.split()) in code
    assert " ".join('Definition cert_record_schedule_uniqueness : Prop := forall M C, HonestCertExtension M C -> equiv_mod_schedule_via M C.'.split()) in code


def test_result_file_is_built_with_the_project():
    assert RESULT.exists(), "StructuralScheduleUniqueness.v does not exist"
    project = (ROOT / "coq" / "_CoqProject").read_text().splitlines()
    assert "kernel/foundation/StructuralScheduleUniqueness.v" in project
    compiled = RESULT.with_suffix(".vo")
    assert compiled.exists() and compiled.stat().st_mtime >= RESULT.stat().st_mtime


def test_both_strengths_are_settled():
    assert RESULT.exists(), "StructuralScheduleUniqueness.v does not exist"
    source = RESULT.read_text()
    assert _settles(source, "tied_record_schedule_uniqueness")
    assert _settles(source, "cert_record_schedule_uniqueness")


def test_result_file_has_no_proof_holes_or_axioms():
    assert RESULT.exists(), "StructuralScheduleUniqueness.v does not exist"
    assert not re.search(r"\b(Admitted|admit|Axiom|Parameter|Hypothesis)\b", RESULT.read_text())
