"""The incremental observer questions are settled, and their statements keep their shape.

KnowledgeNarrowingIncremental.v states the incremental reading of observer
narrowing and the machine size at which free learning first appears. This
contract checks the comment-stripped code of both statements. It also asks
for the Coq theorems that settle each question.
"""

from __future__ import annotations

import re
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


SHAPES = [
    r"Definition incremental_observer_narrowing_priced {S I : Type} (step : S -> I -> S) "
    r"(cost : I -> nat) {O : Type} (obs : S -> O) "
    r"(obs_eq_dec : forall a b : O, {a = b} + {a <> b}) : Prop := "
    r"forall Omega t s0, NoDup Omega -> In s0 Omega -> "
    r"Nat.log2_up (length (knowledge step obs obs_eq_dec Omega [] s0)) - "
    r"Nat.log2_up (length (knowledge step obs obs_eq_dec Omega t s0)) "
    r"<= trace_cost cost t.",
    r"Definition free_incremental_narrowing_with (n : nat) : Prop := "
    r"exists (S I O : Type) (all : list S) (step : S -> I -> S) (cost : I -> nat) "
    r"(eq_dec : forall a b : S, {a = b} + {a <> b}) "
    r"(obs : S -> O) (obs_eq_dec : forall a b : O, {a = b} + {a <> b}) "
    r"(Omega : list S) (t : list I) (s0 : S), "
    r"finite_states all /\ length all = n /\ "
    r"compression_priced step cost eq_dec /\ "
    r"NoDup Omega /\ In s0 Omega /\ "
    r"trace_cost cost t = 0 /\ "
    r"length (knowledge step obs obs_eq_dec Omega t s0) < "
    r"length (knowledge step obs obs_eq_dec Omega [] s0).",
]


def test_definitions_keep_their_shape():
    code = _code(DEFINITIONS.read_text())
    for shape in SHAPES:
        assert " ".join(shape.split()) in code, shape[:60]


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
