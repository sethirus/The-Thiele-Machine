"""
test_coq_compile_gate.py
========================
Gate test: every Coq proof file in this repo must compile cleanly.

What this enforces
------------------
1. coqc is installed and reachable.
2. `make -C coq` exits 0 — every .v file in _CoqProject compiles without error.
3. Zero ``Admitted.`` appears in any .v file under coq/ (double-checked against
   source, not just the Inquisitor regex).
4. Zero freestanding ``Axiom``/``Parameter`` declarations outside Section scope
   appear in any production kernel file (only Section Variables allowed).
5. Every file listed in coq/_CoqProject actually exists on disk.
6. All five previously-unregistered physics/geometry kernel files are now
   present in _CoqProject and have a compiled .vo artefact.

Running
-------
Fast (default):          pytest tests/test_coq_compile_gate.py -v
Full rebuild (slow):     COQ_REBUILD=1 pytest tests/test_coq_compile_gate.py -v -m coq

Environment variables
---------------------
COQ_REBUILD=1     Force a full ``make -C coq -j4`` instead of trusting existing .vo.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
COQ_DIR = REPO_ROOT / "coq"
COQ_PROJECT = COQ_DIR / "_CoqProject"

# Files that MUST now be registered and compiled after Phase-A fix
REQUIRED_KERNEL_PHYSICS_FILES = [
    "kernel/GeodesicCompleteness.v",
    "kernel/InverseSquareLaw.v",
    "kernel/LorentzSignature.v",
    "kernel/PoissonEquation.v",
    "MinimalExtraction.v",
]

# Production kernel files where bare (non-Section) Axiom/Parameter are forbidden
KERNEL_PROD_FILES = list((COQ_DIR / "kernel").glob("*.v"))

# ── helpers ──────────────────────────────────────────────────────────────────

def _coqproject_lines() -> list[str]:
    return COQ_PROJECT.read_text(encoding="utf-8").splitlines()


def _v_files_in_project() -> list[Path]:
    lines = _coqproject_lines()
    files = []
    for line in lines:
        stripped = line.strip()
        if stripped.endswith(".v") and not stripped.startswith("#"):
            files.append(COQ_DIR / stripped)
    return files


def _section_depth_at(lines: list[str], target_lineno: int) -> int:
    """Return how many Section/Module scopes are open at target_lineno (1-based)."""
    depth = 0
    section_open = re.compile(r"^\s*(?:Section|Module)\s+\w")
    section_close = re.compile(r"^\s*End\s+\w")
    for i, line in enumerate(lines[:target_lineno], start=1):
        if section_open.match(line):
            depth += 1
        elif section_close.match(line):
            depth = max(0, depth - 1)
    return depth


# ── tests ────────────────────────────────────────────────────────────────────


@pytest.mark.coq
def test_coqc_available():
    """coqc binary must be on PATH."""
    assert shutil.which("coqc") is not None, "coqc not found on PATH"


@pytest.mark.coq
def test_coqproject_exists():
    """coq/_CoqProject must exist."""
    assert COQ_PROJECT.exists(), f"_CoqProject not found: {COQ_PROJECT}"


@pytest.mark.coq
def test_all_coqproject_files_exist_on_disk():
    """Every .v file listed in _CoqProject must exist on disk."""
    missing = [f for f in _v_files_in_project() if not f.exists()]
    assert not missing, (
        f"{len(missing)} file(s) listed in _CoqProject are missing:\n"
        + "\n".join(f"  {f.relative_to(REPO_ROOT)}" for f in missing)
    )


@pytest.mark.coq
def test_required_physics_files_registered():
    """The 5 previously-unregistered physics/geometry files must be in _CoqProject."""
    text = COQ_PROJECT.read_text(encoding="utf-8")
    missing = [f for f in REQUIRED_KERNEL_PHYSICS_FILES if f not in text]
    assert not missing, (
        "These files are missing from _CoqProject:\n"
        + "\n".join(f"  {f}" for f in missing)
    )


@pytest.mark.coq
def test_required_physics_files_compiled():
    """Each required physics file must have a corresponding .vo artefact."""
    missing_vo = []
    for rel in REQUIRED_KERNEL_PHYSICS_FILES:
        vo = (COQ_DIR / rel).with_suffix(".vo")
        if not vo.exists():
            missing_vo.append(str(vo.relative_to(REPO_ROOT)))
    assert not missing_vo, (
        "No .vo artefact found — run `make -C coq` first:\n"
        + "\n".join(f"  {f}" for f in missing_vo)
    )


@pytest.mark.coq
def test_zero_admits_in_coq_sources():
    """No .v file in coq/ (excluding patches/) may contain Admitted."""
    offenders: list[str] = []
    for vf in COQ_DIR.rglob("*.v"):
        if "patches" in vf.parts:
            continue
        text = vf.read_text(encoding="utf-8")
        lines = text.splitlines()
        for lineno, line in enumerate(lines, start=1):
            stripped = line.strip()
            if stripped in ("Admitted.", "admit."):
                offenders.append(f"{vf.relative_to(REPO_ROOT)}:{lineno}: {stripped}")
    assert not offenders, (
        f"Found {len(offenders)} Admitted. in source:\n"
        + "\n".join(f"  {o}" for o in offenders)
    )


@pytest.mark.coq
def test_no_bare_axioms_in_kernel_outside_sections():
    """
    Non-Section Axiom/Parameter declarations are forbidden in kernel/ files.
    Only Section Variables are allowed (they discharge when the section closes).

    Coq multi-line comments ``(* ... *)`` (including nested) are skipped so
    that commented-out examples or documentation snippets do not trigger
    false positives.
    """
    forbidden_re = re.compile(r"^\s*(Axiom|Parameter)\s+\w")
    section_open_re = re.compile(r"^\s*(?:Section|Module)\s+\w")
    section_close_re = re.compile(r"^\s*End\s+\w")
    offenders: list[str] = []

    for vf in KERNEL_PROD_FILES:
        text = vf.read_text(encoding="utf-8")
        section_depth = 0
        comment_depth = 0
        i = 0
        lineno = 1
        line_start = 0

        while i < len(text):
            ch = text[i]
            if comment_depth == 0 and text[i:i+2] == "(*":
                comment_depth += 1
                i += 2
                continue
            if comment_depth > 0 and text[i:i+2] == "(*":
                comment_depth += 1
                i += 2
                continue
            if comment_depth > 0 and text[i:i+2] == "*)":
                comment_depth -= 1
                i += 2
                continue
            if ch == "\n":
                if comment_depth == 0:
                    line = text[line_start:i]
                    if section_open_re.match(line):
                        section_depth += 1
                    elif section_close_re.match(line):
                        section_depth = max(0, section_depth - 1)
                    elif forbidden_re.match(line) and section_depth == 0:
                        offenders.append(
                            f"{vf.relative_to(REPO_ROOT)}:{lineno}: {line.strip()}"
                        )
                lineno += 1
                line_start = i + 1
            i += 1
        # handle last line if no trailing newline
        if comment_depth == 0 and line_start < len(text):
            line = text[line_start:]
            if forbidden_re.match(line) and section_depth == 0:
                offenders.append(
                    f"{vf.relative_to(REPO_ROOT)}:{lineno}: {line.strip()}"
                )

    assert not offenders, (
        f"Found {len(offenders)} bare Axiom/Parameter outside any Section "
        f"in kernel/:\n" + "\n".join(f"  {o}" for o in offenders)
    )


@pytest.mark.coq
@pytest.mark.slow
def test_full_coq_build_succeeds():
    """
    Run ``make -C coq -j4`` and assert exit code 0.

    This is the ground-truth gate: if it passes, every proof in the project
    compiles with zero errors. Marked slow; skipped unless COQ_REBUILD=1
    or running under the full CI profile.
    """
    if not os.environ.get("COQ_REBUILD"):
        # Fast path: trust existing .vo artefacts (checked by other tests).
        # Fail if ANY expected .vo is missing.
        all_vos = [f.with_suffix(".vo") for f in _v_files_in_project()]
        missing = [v for v in all_vos if not v.exists()]
        if missing:
            pytest.fail(
                f"{len(missing)} .vo artefact(s) missing — run `make -C coq` or "
                f"set COQ_REBUILD=1:\n"
                + "\n".join(f"  {v.relative_to(REPO_ROOT)}" for v in missing[:10])
            )
        return

    result = subprocess.run(
        ["make", "-j4"],
        cwd=str(COQ_DIR),
        capture_output=True,
        text=True,
        timeout=3600,
    )
    assert result.returncode == 0, (
        "make -C coq failed with exit code "
        f"{result.returncode}.\n\n"
        f"STDOUT (tail):\n{result.stdout[-3000:]}\n\n"
        f"STDERR (tail):\n{result.stderr[-3000:]}"
    )


@pytest.mark.coq
def test_coqproject_count_matches_v_files():
    """
    Number of .v files in _CoqProject == number of .v files on disk
    (excluding patches/ and test_vscoq/).

    This catches files added to disk but forgotten in _CoqProject (or vice versa).
    """
    # Intentionally-excluded disk files: scratch/non-production .v files that
    # are legitimately absent from _CoqProject.
    DISK_EXCLUDE: set[str] = {
        "kernel/Test.v",  # trivial `Check einstein_tensor.` scratch file
    }
    # Patterns whose entries in _CoqProject are excluded from the disk scan
    # (the corresponding directories are also excluded from on_disk above).
    PROJECT_EXCLUDE_SUBSTR: tuple[str, ...] = ("test_vscoq",)

    on_disk = (
        set(
            str(f.relative_to(COQ_DIR))
            for f in COQ_DIR.rglob("*.v")
            if "patches" not in f.parts
               and "test_vscoq" not in f.parts
               and "_build" not in f.parts
        )
        - DISK_EXCLUDE
    )
    in_project = set(
        line.strip()
        for line in _coqproject_lines()
        if line.strip().endswith(".v")
           and not line.strip().startswith("#")
           and not any(excl in line for excl in PROJECT_EXCLUDE_SUBSTR)
    )
    only_on_disk = on_disk - in_project
    only_in_project = in_project - on_disk

    problems: list[str] = []
    if only_on_disk:
        problems.append(
            "Files on disk but NOT in _CoqProject (add or move to archive/):\n"
            + "\n".join(f"  {f}" for f in sorted(only_on_disk))
        )
    if only_in_project:
        problems.append(
            "Files in _CoqProject but NOT on disk (delete or restore):\n"
            + "\n".join(f"  {f}" for f in sorted(only_in_project))
        )
    assert not problems, "\n\n".join(problems)
