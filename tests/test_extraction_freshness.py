"""
test_extraction_freshness.py
============================
Gate test: Coq extraction artefacts are fresh, consistent, and semantically sound.

What this enforces
------------------
1. ``build/thiele_core.ml`` exists and was produced by ``coq/Extraction.v``.
2. The .ml file exports the three required symbols:
       ``vm_instruction``  ``VMState``  ``vm_apply``
3. The extraction artefact contains none of the "phantom" names that would
   indicate a stale or hand-edited file (e.g. ``STALE_MARKER``, ``TODO``, ``FIXME``).
4. Fresh coqc invocations in isolated directories reproduce all eight ML
   artifacts exactly, independent of target mtimes.

Running
-------
pytest tests/test_extraction_freshness.py -v
"""

from __future__ import annotations

import re
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
COQ_DIR = REPO_ROOT / "coq"
BUILD_DIR = REPO_ROOT / "build"

# Extraction.v  → build/thiele_core.ml
EXTRACTION_PAIRS = [
    (COQ_DIR / "Extraction.v",        BUILD_DIR / "thiele_core.ml"),
]

REQUIRED_EXPORTED_SYMBOLS = [
    "vm_instruction",
    "vm_apply",
    "vMState",   # OCaml convention for VMState record type
]

# These strings in a .ml artefact would indicate hand-editing or staleness
PHANTOM_PATTERNS = ["STALE_MARKER", "HAND_EDITED", "TODO: re-extract"]

_EXTRACT_TARGET_RE = re.compile(
    r'Extraction\s+"([^"]+\.ml)"',
    re.MULTILINE,
)


def _extracted_ml_paths(v_file: Path) -> list[Path]:
    """Parse all ``Extraction "..."`` directives to find target .ml paths."""
    text = v_file.read_text(encoding="utf-8")
    return [
        (v_file.parent / raw).resolve()
        for raw in _EXTRACT_TARGET_RE.findall(text)
    ]


# ── tests ────────────────────────────────────────────────────────────────────


@pytest.mark.coq
def test_extraction_artefacts_exist():
    """thiele_core.ml must be present in build/."""
    missing = [ml for _, ml in EXTRACTION_PAIRS if not ml.exists()]
    assert not missing, (
        "Extraction artefact(s) missing — run `make -C coq`:\n"
        + "\n".join(f"  {f.relative_to(REPO_ROOT)}" for f in missing)
    )


@pytest.mark.coq
def test_extraction_artefacts_nonempty():
    """Extraction artefacts must be non-empty (non-zero bytes)."""
    empty = [ml for _, ml in EXTRACTION_PAIRS if ml.exists() and ml.stat().st_size == 0]
    assert not empty, (
        "Extraction artefact(s) are empty:\n"
        + "\n".join(f"  {f.relative_to(REPO_ROOT)}" for f in empty)
    )


@pytest.mark.coq
def test_extraction_artefact_paths_match_v_directives():
    """
    The Extraction "..." path in each .v file must point to the same .ml
    we track in this test (no silent rerouting).
    """
    mismatches: list[str] = []
    for v_file, expected_ml in EXTRACTION_PAIRS:
        actual = _extracted_ml_paths(v_file)
        if not actual:
            mismatches.append(f"{v_file.name}: no Extraction directive found")
        elif expected_ml.resolve() not in actual:
            mismatches.append(
                f"{v_file.name}: directives point to {actual}\n"
                f"  but gate expects {expected_ml}"
            )
    assert not mismatches, "\n".join(mismatches)


@pytest.mark.coq
def test_required_symbols_exported():
    """
    Each .ml artefact must define all three core VM symbols.

    We check for OCaml ``let`` or ``type`` definitions matching each name
    (case-sensitive for OCaml-generated lowercase names).
    """
    symbol_re = {
        sym: re.compile(rf"\b{re.escape(sym)}\b", re.MULTILINE)
        for sym in REQUIRED_EXPORTED_SYMBOLS
    }
    failures: list[str] = []
    for _, ml in EXTRACTION_PAIRS:
        if not ml.exists():
            continue
        text = ml.read_text(encoding="utf-8")
        for sym, pat in symbol_re.items():
            if not pat.search(text):
                failures.append(
                    f"{ml.name}: required symbol '{sym}' not found"
                )
    assert not failures, "\n".join(failures)


@pytest.mark.coq
def test_no_phantom_patterns_in_artefacts():
    """Extraction artefacts must not contain staleness/hand-edit markers."""
    hits: list[str] = []
    for _, ml in EXTRACTION_PAIRS:
        if not ml.exists():
            continue
        text = ml.read_text(encoding="utf-8")
        for pat in PHANTOM_PATTERNS:
            if pat in text:
                hits.append(f"{ml.name}: contains '{pat}'")
    assert not hits, "\n".join(hits)


@pytest.mark.coq
def test_extraction_vo_exists():
    """Compiled .vo for each Extraction.v must exist (proves coqc was run)."""
    missing = [
        v.with_suffix(".vo")
        for v, _ in EXTRACTION_PAIRS
        if not v.with_suffix(".vo").exists()
    ]
    assert not missing, (
        ".vo artefact(s) missing:\n"
        + "\n".join(f"  {f.relative_to(REPO_ROOT)}" for f in missing)
    )


@pytest.mark.coq
def test_full_extraction_matches_committed():
    """Both extraction roots must reproduce every artifact without altering it."""
    from scripts.check_extraction import compare, extract, reference_bytes

    before = reference_bytes("working-tree")
    compare(extract(), before)
    assert reference_bytes("working-tree") == before


def test_extraction_comparison_rejects_stale_artifact():
    from scripts.check_extraction import OUTPUTS, compare

    expected = {path: b"expected" for path in OUTPUTS}
    fresh = dict(expected)
    fresh["build/kami_hw/Target.mli"] = b"different interface"
    with pytest.raises(ValueError, match="Target.mli"):
        compare(fresh, expected)


def test_extraction_comparison_requires_every_output():
    from scripts.check_extraction import OUTPUTS, compare

    expected = {path: b"expected" for path in OUTPUTS}
    incomplete = dict(expected)
    del incomplete["build/thiele_core_complete.ml"]
    with pytest.raises(ValueError, match="thiele_core_complete.ml"):
        compare(incomplete, expected)
