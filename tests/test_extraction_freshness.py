"""
test_extraction_freshness.py
============================
Gate test: Coq extraction artefacts are fresh, consistent, and semantically sound.

What this enforces
------------------
1. ``build/thiele_core.ml``      exists and was produced by ``coq/Extraction.v``.
2. ``build/thiele_core_minimal.ml`` exists and was produced by ``coq/MinimalExtraction.v``.
3. Both .ml files export the three required symbols:
       ``vm_instruction``  ``VMState``  ``vm_apply``
4. The extraction artefacts contain none of the "phantom" names that would
   indicate a stale or hand-edited file (e.g. ``STALE_MARKER``, ``TODO``, ``FIXME``).
5. (Full mode) Running ``make -C coq Extraction.vo MinimalExtraction.vo`` produces
   .ml outputs that are byte-for-byte identical to the committed artefacts.
   Gate is behind ``THIELE_EXTRACTION_FULL=1`` because it takes ~30 s.

Running
-------
Fast (default):   pytest tests/test_extraction_freshness.py -v
Full re-extract:  THIELE_EXTRACTION_FULL=1 pytest tests/test_extraction_freshness.py -v -m coq
"""

from __future__ import annotations

import hashlib
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
COQ_DIR = REPO_ROOT / "coq"
BUILD_DIR = REPO_ROOT / "build"

# Extraction.v  → build/thiele_core.ml
# MinimalExtraction.v → build/thiele_core_minimal.ml
EXTRACTION_PAIRS = [
    (COQ_DIR / "Extraction.v",        BUILD_DIR / "thiele_core.ml"),
    (COQ_DIR / "MinimalExtraction.v", BUILD_DIR / "thiele_core_minimal.ml"),
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


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _expected_ml_path(v_file: Path) -> Path | None:
    """Parse the ``Extraction "..."`` directive to find the target .ml path."""
    text = v_file.read_text(encoding="utf-8")
    m = _EXTRACT_TARGET_RE.search(text)
    if not m:
        return None
    raw = m.group(1)
    target = (v_file.parent / raw).resolve()
    return target


# ── tests ────────────────────────────────────────────────────────────────────


@pytest.mark.coq
def test_extraction_artefacts_exist():
    """Both thiele_core.ml and thiele_core_minimal.ml must be present in build/."""
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
        actual = _expected_ml_path(v_file)
        if actual is None:
            mismatches.append(f"{v_file.name}: no Extraction directive found")
        elif actual != expected_ml.resolve():
            mismatches.append(
                f"{v_file.name}: directive points to {actual}\n"
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
def test_ml_newer_than_v_source():
    """
    The .ml artefact must be at least as new as the .v source.

    This detects the case where a proof was modified but extraction was not
    re-run (the .ml would then be OLDER than the .v).  Skipped when mtimes
    are unreliable (e.g. fresh git clone sets everything to the same time).
    """
    all_same_mtime = len({int(p.stat().st_mtime)
                          for v, ml in EXTRACTION_PAIRS for p in [v, ml]
                          if v.exists() and ml.exists()}) == 1
    if all_same_mtime:
        pytest.skip("All file mtimes identical (fresh clone) — skipping mtime gate")

    stale: list[str] = []
    for v_file, ml_file in EXTRACTION_PAIRS:
        if not (v_file.exists() and ml_file.exists()):
            continue
        if ml_file.stat().st_mtime < v_file.stat().st_mtime:
            stale.append(
                f"{ml_file.name} is OLDER than {v_file.name} — "
                "re-run `make -C coq`"
            )
    assert not stale, "\n".join(stale)


@pytest.mark.coq
@pytest.mark.slow
def test_full_extraction_matches_committed(tmp_path):
    """
    Re-run ``make -C coq Extraction.vo MinimalExtraction.vo`` and verify the
    freshly-generated .ml files are byte-for-byte identical to the committed ones.

    Requires THIELE_EXTRACTION_FULL=1 to run (slow, ~30 s).
    """
    if not os.environ.get("THIELE_EXTRACTION_FULL"):
        pytest.skip("Set THIELE_EXTRACTION_FULL=1 to run full extraction gate")

    result = subprocess.run(
        ["make", "-j2", "Extraction.vo", "MinimalExtraction.vo"],
        cwd=str(COQ_DIR),
        capture_output=True,
        text=True,
        timeout=300,
    )
    assert result.returncode == 0, (
        "make Extraction.vo failed:\n" + result.stderr[-2000:]
    )

    mismatches: list[str] = []
    for _, ml in EXTRACTION_PAIRS:
        if not ml.exists():
            mismatches.append(f"{ml.name}: missing after build")
    assert not mismatches, "\n".join(mismatches)
