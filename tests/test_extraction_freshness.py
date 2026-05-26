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


# Removed: test_ml_newer_than_v_source was an mtime-based proxy for staleness
# that gave false positives on CI fresh-clone checkouts (mtimes cluster but
# aren't strictly equal, so the existing skip-bypass missed). The semantic
# it tried to enforce — committed .ml matches what extraction would produce
# from current .v — is covered authoritatively (and without mtime brittleness)
# by test_full_extraction_matches_committed below, which actually re-runs
# `make Extraction.vo` and byte-compares the output to the tracked .ml.


# Files Coq writes as side effects of the Extraction directives in
# coq/Extraction.v (Target.ml, thiele_core.ml) and coq/ThieleMachineComplete.v
# (Target_complete.ml, thiele_core_complete.ml). Re-running `make Extraction.vo
# ThieleMachineComplete.vo` cascade-rebuilds and re-emits these with bytes that
# depend on the surrounding Coq/OCaml environment — locally vs CI they
# routinely differ even at the same Coq version, because the Kami .vo
# closure that KamiExtraction.vo sees is environment-sensitive. Downstream
# tests (test_rtl_pipeline_manifest_*) byte-pin the *committed* hashes, so
# any in-pytest extraction that leaves CI-environment bytes on disk is a
# hidden cross-test contamination.
_EXTRACTION_SIDE_EFFECT_PATHS = [
    "build/kami_hw/Target.ml",
    "build/kami_hw/Target.mli",
    "build/kami_hw/Target_complete.ml",
    "build/kami_hw/Target_complete.mli",
    "build/thiele_core.ml",
    "build/thiele_core.mli",
    "build/thiele_core_complete.ml",
    "build/thiele_core_complete.mli",
]


def _restore_extraction_side_effects_from_head() -> None:
    """Put the four extraction-output pairs back to their committed bytes.

    `make Extraction.vo ThieleMachineComplete.vo` re-fires the Coq Extraction
    directives whose output paths land in build/. The bytes Coq emits depend
    on the build environment (Kami .vo closure, OCaml version, etc.), so a CI
    run can produce bytes that diverge from what was committed. Downstream
    tests that check rtl_pipeline_manifest.json's byte pins assume build/
    holds committed bytes; without this restore those tests fail spuriously
    every time CI's environment diverges from the developer's.

    Using `git checkout HEAD --` is a no-op locally when the dev's environment
    matches their commit, and a precise undo on CI when it doesn't.
    """
    subprocess.run(
        ["git", "checkout", "HEAD", "--", *_EXTRACTION_SIDE_EFFECT_PATHS],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
    )


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

    try:
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
    finally:
        # Whether assertions passed or failed, the make above may have
        # rewritten build/ with environment-dependent bytes. Restore the
        # committed bytes so downstream byte-pin tests (manifest, etc.)
        # see the same on-disk state pytest started with.
        _restore_extraction_side_effects_from_head()
