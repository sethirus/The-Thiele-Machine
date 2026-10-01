"""The uniqueness questions are settled, and their statements keep their shape.

StructuralCore.v and StructuralCoreCover.v define the weak and strong forms
of the uniqueness question. This contract checks the comment-stripped code of
each definition, so comments may be edited but neither statement can change
shape. It also asks for a Coq theorem that settles each question, in either
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
RESULT = FOUNDATION / "StructuralUniqueness.v"
DEFINITIONS = {
    "StructuralCore.v":
        "Definition adequate_core_uniqueness : Prop := "
        "forall M, Adequate M -> core_equiv M ThieleCore.",
    "StructuralCoreCover.v":
        "Definition honest_vm_extension_uniqueness : Prop := "
        "forall M, HonestVMExtension M -> observed_core_equiv M ThieleCore.",
}


def _code(text: str) -> str:
    return " ".join(_strip_coq_comments(text).split())


def _settles(source: str, conjecture: str) -> bool:
    proved = rf"Theorem\s+\w+\s*:\s*{conjecture}\s*\."
    refuted = rf"Theorem\s+\w+\s*:\s*~\s*{conjecture}\s*\."
    return bool(re.search(proved, source) or re.search(refuted, source))


def test_definitions_keep_their_shape():
    for name, definition in DEFINITIONS.items():
        code = _code((FOUNDATION / name).read_text())
        assert " ".join(definition.split()) in code, name


def test_result_file_is_built_with_the_project():
    assert RESULT.exists(), "StructuralUniqueness.v does not exist"
    project = (ROOT / "coq" / "_CoqProject").read_text().splitlines()
    assert "kernel/foundation/StructuralUniqueness.v" in project
    compiled = RESULT.with_suffix(".vo")
    assert compiled.exists() and compiled.stat().st_mtime >= RESULT.stat().st_mtime


def test_weak_form_is_settled():
    assert RESULT.exists(), "StructuralUniqueness.v does not exist"
    assert _settles(RESULT.read_text(), "adequate_core_uniqueness")


def test_strong_form_is_settled():
    assert RESULT.exists(), "StructuralUniqueness.v does not exist"
    assert _settles(RESULT.read_text(), "honest_vm_extension_uniqueness")


def test_result_file_has_no_proof_holes_or_axioms():
    assert RESULT.exists(), "StructuralUniqueness.v does not exist"
    source = RESULT.read_text()
    assert not re.search(r"\b(Admitted|admit|Axiom|Parameter|Hypothesis)\b", source)
