"""Rule helpers for `scripts/inquisitor.py`.

This module centralizes heuristics for detecting vacuous/trivial constructs in
Coq source files. Keep these rules conservative-but-useful: the goal is to rank
"obviously unfinished" artifacts first, not to perfectly judge mathematical
content.
"""

from __future__ import annotations

from dataclasses import dataclass
import re
from typing import Iterable


@dataclass(frozen=True)
class Scored:
    score: int
    tags: tuple[str, ...]


# ---------------------------------------------------------------------------
# Regexes (comment-stripped text)
# ---------------------------------------------------------------------------

# `Definition foo : Prop := True.`
PROP_TRUE_DEF_RE = re.compile(
    r"(?m)^[ \t]*Definition\s+([A-Za-z0-9_']+)\s*:\s*Prop\s*:=\s*True\s*\."
)

# `Definition foo := fun _ => 0.` or `fun _ => True` etc.
CONST_FUN_RE = re.compile(
    r"(?m)^[ \t]*Definition\s+([A-Za-z0-9_']+)\b[^.]*:=\s*fun\s+_\s*=>\s*(True|False|0|1)\b[^.]*\."
)

# NOTE: Avoid multi-line "dot-all" regexes over large Coq files. They can be
# extremely slow due to backtracking. We instead parse theorem statements in a
# bounded way in `count_theorem_conclusions`.

THEOREM_START_RE = re.compile(r"^[ \t]*(Theorem|Lemma|Corollary)\s+([A-Za-z0-9_']+)\b")

# Placeholder markers.
PLACEHOLDER_RE = re.compile(r"(?i)\b(placeholder|stub|TODO|FIXME|XXX)\b")

MODULE_TYPE_RE = re.compile(r"(?m)^[ \t]*Module\s+Type\b")


def score_vacuity_tags(
    *,
    prop_true_defs: int,
    theorem_true: int,
    theorem_impl_true: int,
    theorem_let_in_true: int,
    theorem_exists_true: int,
    const_funs: int,
    placeholders: int,
    module_types: int,
) -> Scored:
    """Compute a severity score + tags for a file.

    The score is designed to push "obviously unfinished" modules to the top.
    """

    score = 0
    tags: list[str] = []

    # Module Type signatures are allowed; do not score.
    _ = module_types

    if placeholders:
        score += 160 + 10 * placeholders
        tags.append("placeholder")

    if prop_true_defs:
        score += 150 + 25 * prop_true_defs
        tags.append("prop:=True")

    if theorem_true:
        score += 140 + 20 * theorem_true
        tags.append("theorem:True")

    if theorem_impl_true:
        score += 110 + 10 * theorem_impl_true
        tags.append("...->True")

    if theorem_let_in_true:
        score += 120 + 15 * theorem_let_in_true
        tags.append("let-in-True")

    if theorem_exists_true:
        score += 120 + 15 * theorem_exists_true
        tags.append("exists-True")

    if const_funs:
        score += 60 + 5 * const_funs
        tags.append("const-fun")

    return Scored(score=score, tags=tuple(tags))


def count_matches(text: str, regex: re.Pattern[str]) -> int:
    return len(list(regex.finditer(text)))


def count_theorem_conclusions(text: str) -> tuple[int, int, int, int]:
    """Return (theorem_true, theorem_impl_true, theorem_let_in_true, theorem_exists_true) counts.

    This is a fast heuristic: it accumulates the statement text from the header
    until the first `.` (or a size cap) and then checks whether the statement
    ends in `: True.` or `-> True.`.
    """

    lines = text.splitlines()
    theorem_true = 0
    theorem_impl_true = 0

    theorem_let_in_true = 0
    theorem_exists_true = 0

    i = 0
    max_stmt_lines = 200
    stmt_line_end = re.compile(r"\.[ \t]*$")
    while i < len(lines):
        if not THEOREM_START_RE.match(lines[i]):
            i += 1
            continue

        stmt_parts: list[str] = [lines[i].strip()]
        j = i + 1
        while j < len(lines) and len(stmt_parts) < max_stmt_lines and not stmt_line_end.search(stmt_parts[-1]):
            part = lines[j].strip()
            if part:
                stmt_parts.append(part)
            j += 1

        stmt = re.sub(r"\s+", " ", " ".join(stmt_parts)).strip()

        if re.search(r":\s*True\s*\.\s*$", stmt):
            theorem_true += 1
        if re.search(r"->\s*True\s*\.\s*$", stmt):
            theorem_impl_true += 1
        if " let " in f" {stmt} " and re.search(r"\bin\s*True\s*\.\s*$", stmt):
            theorem_let_in_true += 1
        if re.search(r"\bexists\b[^.]*,\s*True\s*\.\s*$", stmt):
            theorem_exists_true += 1

        i = j + 1

    return theorem_true, theorem_impl_true, theorem_let_in_true, theorem_exists_true


def summarize_text(text: str) -> Scored:
    """Summarize a comment-stripped file by vacuity indicators."""

    theorem_true, theorem_impl_true, theorem_let_in_true, theorem_exists_true = count_theorem_conclusions(text)

    return score_vacuity_tags(
        prop_true_defs=count_matches(text, PROP_TRUE_DEF_RE),
        theorem_true=theorem_true,
        theorem_impl_true=theorem_impl_true,
        theorem_let_in_true=theorem_let_in_true,
        theorem_exists_true=theorem_exists_true,
        const_funs=count_matches(text, CONST_FUN_RE),
        placeholders=count_matches(text, PLACEHOLDER_RE),
        module_types=count_matches(text, MODULE_TYPE_RE),
    )
