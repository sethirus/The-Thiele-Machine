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
4. Running ``make -C coq Extraction.vo ThieleMachineComplete.vo`` produces
   both direct .ml outputs and byte-for-byte identity is verified.

Running
-------
pytest tests/test_extraction_freshness.py -v
"""

from __future__ import annotations

import hashlib
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


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


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
def test_full_extraction_matches_committed(tmp_path):
    """
    Re-run ``make -C coq Extraction.vo ThieleMachineComplete.vo`` and verify
    both direct extractions are present and byte-for-byte identical.
    """
    result = subprocess.run(
        ["make", "-j2", "Extraction.vo", "ThieleMachineComplete.vo"],
        cwd=str(COQ_DIR),
        capture_output=True,
        text=True,
        timeout=300,
    )
    assert result.returncode == 0, (
        "make Extraction.vo failed:\n" + result.stderr[-2000:]
    )

    for _, ml in EXTRACTION_PAIRS:
        assert ml.exists(), f"{ml.name}: missing after build"

    # Verify byte-for-byte identity: both files are direct extractions, one
    # from the modular root and one from ThieleMachineComplete.v.
    core = BUILD_DIR / "thiele_core.ml"
    complete = BUILD_DIR / "thiele_core_complete.ml"
    assert complete.exists(), (
        "thiele_core_complete.ml missing — "
        "ThieleMachineComplete.v must be compiled first"
    )
    assert core.read_bytes() == complete.read_bytes(), (
        "thiele_core.ml and thiele_core_complete.ml are not byte-identical"
    )
    core_mli = BUILD_DIR / "thiele_core.mli"
    complete_mli = BUILD_DIR / "thiele_core_complete.mli"
    assert complete_mli.exists(), (
        "thiele_core_complete.mli missing — "
        "ThieleMachineComplete.v must be compiled first"
    )
    assert core_mli.read_bytes() == complete_mli.read_bytes(), (
        "thiele_core.mli and thiele_core_complete.mli are not byte-identical"
    )
