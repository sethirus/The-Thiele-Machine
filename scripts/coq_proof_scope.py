"""Canonical scope of the Coq proof corpus.

Single source of truth for "which .v files are inside the proof-bearing
corpus (must compile and produce a .vo) versus outside it (probes,
generated audit artifacts, scratch)".

Every gate that needs to make this distinction MUST import from this
module. Do not re-encode the list anywhere else.

Consumers
---------
- scripts/inquisitor.py
    Compilation-coverage gate that fails if a .v file is in scope but its
    .vo is missing after build, or if an out-of-scope file leaked into
    the canonical _CoqProject.
- tests/test_coq_compile_gate.py
    Reconciles _CoqProject against disk; the disk side excludes the
    out-of-scope set.
- tests/test_coq_proof_scope.py
    Drift gate: enforces the structural invariants documented below.
- build/probe/build_full_probe.py
    Skips out-of-scope files when generating the comprehensive
    Print Assumptions probe (otherwise the probe would chase its own tail).

Structural invariants (enforced by tests/test_coq_proof_scope.py)
-----------------------------------------------------------------
INV-1  Every file in NON_PROOF_BEARING_FILES exists on disk.
INV-2  No file in NON_PROOF_BEARING_FILES is listed in coq/_CoqProject.
INV-3  Every active disk .v file (after stripping ARCHIVE_OR_VENDOR
       prefixes and the patches/test_vscoq/_build sentinels used by the
       compile-gate test) is either in coq/_CoqProject or in
       NON_PROOF_BEARING_FILES — never neither, never both.

Together these invariants make scope drift between gates structurally
impossible. The cause of the prior CI/local divergence (a stale local
.vo masking a coverage gap that only surfaced on a clean checkout) is
eliminated because the inquisitor's coverage check now derives its
"in-scope" set from _CoqProject ∩ NON_PROOF_BEARING_FILES, not from the
presence of stray .vo files on disk.
"""

from __future__ import annotations

from pathlib import Path
from typing import FrozenSet, Iterable

REPO_ROOT = Path(__file__).resolve().parents[1]
COQ_DIR = REPO_ROOT / "coq"
COQ_PROJECT = COQ_DIR / "_CoqProject"


# ---------------------------------------------------------------------------
# Canonical out-of-scope set.
#
# Repo-relative POSIX paths. Each entry MUST be accompanied by a one-line
# rationale immediately above it. Adding a file here is a deliberate act:
# it exempts the file from the compilation-coverage gate forever, so the
# rationale must justify why the file is not a proof obligation.
# ---------------------------------------------------------------------------

NON_PROOF_BEARING_FILES: FrozenSet[str] = frozenset({
    # Print Assumptions probe over Kernel.MasterSummary. Header explicitly
    # marks it as a probe, not a proof obligation; excluded from _CoqProject.
    "coq/AssumptionsProbe.v",

    # Auto-generated comprehensive Print Assumptions probe across every
    # addressable proof-bearing declaration; produced by
    # build/probe/build_full_probe.py. Not a proof obligation.
    "coq/AssumptionsProbeAll.v",
})


# ---------------------------------------------------------------------------
# Disk-scan exclusions used by the compile-gate test.
#
# These mirror the directories the canonical Coq build never touches.
# Centralised here so the test and any future gate share one definition.
# ---------------------------------------------------------------------------

DISK_SCAN_EXCLUDED_DIRS: FrozenSet[str] = frozenset({
    "patches",     # Kami patch tree, applied to vendor/ at build time.
    "test_vscoq",  # IDE smoke files, not part of the canonical build.
    "_build",      # transient Coq build artefacts.
    "archive",     # archived/old proofs, kept for posterity only.
})


# ---------------------------------------------------------------------------
# Helpers (pure: no side effects, no caching, safe to call from tests).
# ---------------------------------------------------------------------------


def coqproject_v_files(project_path: Path = COQ_PROJECT) -> FrozenSet[str]:
    """Parse coq/_CoqProject and return the set of .v entries as
    repo-relative POSIX paths (e.g. ``coq/kernel/Foo.v``).

    Lines beginning with ``-`` (path mappings, flags) and comments
    (``#``) are ignored. Trailing whitespace is stripped.
    """
    if not project_path.exists():
        return frozenset()
    out: set[str] = set()
    for raw in project_path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or line.startswith("-"):
            continue
        if not line.endswith(".v"):
            continue
        # _CoqProject entries are relative to coq/.
        out.add(f"coq/{line}")
    return frozenset(out)


def disk_v_files(coq_dir: Path = COQ_DIR) -> FrozenSet[str]:
    """Return the set of active .v files on disk as repo-relative POSIX
    paths, excluding directories listed in DISK_SCAN_EXCLUDED_DIRS.
    """
    if not coq_dir.exists():
        return frozenset()
    out: set[str] = set()
    for vf in coq_dir.rglob("*.v"):
        if not vf.is_file():
            continue
        parts = set(vf.relative_to(coq_dir).parts)
        if parts & DISK_SCAN_EXCLUDED_DIRS:
            continue
        out.add(vf.relative_to(REPO_ROOT).as_posix())
    return frozenset(out)


def in_scope_v_files() -> FrozenSet[str]:
    """The proof corpus: disk .v files that are in _CoqProject and not
    in NON_PROOF_BEARING_FILES. This is the set the inquisitor's
    compilation-coverage gate iterates."""
    return coqproject_v_files() - NON_PROOF_BEARING_FILES


def validate_alignment() -> list[str]:
    """Return a list of human-readable problem strings if any structural
    invariant is violated. Empty list means scope is fully aligned.

    Used by tests/test_coq_proof_scope.py and the pre-commit hook.
    """
    problems: list[str] = []
    project = coqproject_v_files()
    disk = disk_v_files()

    # INV-1: every excluded file exists on disk.
    missing = sorted(p for p in NON_PROOF_BEARING_FILES if not (REPO_ROOT / p).is_file())
    if missing:
        problems.append(
            "NON_PROOF_BEARING_FILES references files that do not exist on disk "
            "(rename or delete the entry):\n"
            + "\n".join(f"  {p}" for p in missing)
        )

    # INV-2: no excluded file is in _CoqProject.
    leaked = sorted(NON_PROOF_BEARING_FILES & project)
    if leaked:
        problems.append(
            "NON_PROOF_BEARING_FILES leaked into _CoqProject (an out-of-scope "
            "file cannot also be a canonical compile target):\n"
            + "\n".join(f"  {p}" for p in leaked)
        )

    # INV-3a: every disk .v is accounted for.
    orphans = sorted(disk - project - NON_PROOF_BEARING_FILES)
    if orphans:
        problems.append(
            "Disk .v files that are neither in _CoqProject nor in "
            "NON_PROOF_BEARING_FILES (add to one or the other, or delete):\n"
            + "\n".join(f"  {p}" for p in orphans)
        )

    # INV-3b: every _CoqProject entry exists on disk.
    phantom = sorted(project - disk)
    if phantom:
        problems.append(
            "_CoqProject lists files not present on disk (remove or restore):\n"
            + "\n".join(f"  {p}" for p in phantom)
        )

    return problems


__all__ = [
    "NON_PROOF_BEARING_FILES",
    "DISK_SCAN_EXCLUDED_DIRS",
    "REPO_ROOT",
    "COQ_DIR",
    "COQ_PROJECT",
    "coqproject_v_files",
    "disk_v_files",
    "in_scope_v_files",
    "validate_alignment",
]
