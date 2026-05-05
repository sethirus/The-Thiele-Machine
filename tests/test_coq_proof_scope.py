"""Structural drift gate for the Coq proof-corpus scope.

Single test that, if green, makes it impossible for the gates that
classify .v files as in-corpus vs out-of-corpus to silently disagree.

Backed by scripts/coq_proof_scope.py — the canonical scope module —
which encodes the invariants. This file just exposes them to pytest so
they run on every commit and on every CI run.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from coq_proof_scope import (  # type: ignore
    NON_PROOF_BEARING_FILES,
    coqproject_v_files,
    disk_v_files,
    validate_alignment,
)


def test_proof_scope_alignment():
    """All structural invariants in coq_proof_scope hold simultaneously."""
    problems = validate_alignment()
    assert not problems, (
        "Coq proof scope drift detected. Fix one of the following, then\n"
        "re-run: pytest tests/test_coq_proof_scope.py\n\n"
        + "\n\n".join(problems)
    )


def test_proof_scope_consumers_use_canonical_module():
    """Every consumer that classifies .v files imports from
    scripts/coq_proof_scope.py rather than re-encoding the list.

    If you legitimately need a new consumer, add it to the list below
    after wiring it through scripts/coq_proof_scope.py.
    """
    expected_consumers = {
        REPO_ROOT / "scripts" / "inquisitor.py",
        REPO_ROOT / "tests" / "test_coq_compile_gate.py",
        REPO_ROOT / "build" / "probe" / "build_full_probe.py",
    }
    missing: list[str] = []
    for path in sorted(expected_consumers):
        text = path.read_text(encoding="utf-8")
        if "coq_proof_scope" not in text:
            missing.append(str(path.relative_to(REPO_ROOT)))
    assert not missing, (
        "These files are expected to import from scripts/coq_proof_scope.py\n"
        "but do not — they may be re-encoding the proof-scope list:\n"
        + "\n".join(f"  {m}" for m in missing)
    )


def test_proof_scope_no_hardcoded_probe_paths():
    """No file outside scripts/coq_proof_scope.py may hard-code the probe
    file names. Forces every consumer through the canonical module so
    rename/remove operations propagate cleanly.
    """
    probe_strings = (
        '"coq/AssumptionsProbe.v"',
        "'coq/AssumptionsProbe.v'",
        '"coq/AssumptionsProbeAll.v"',
        "'coq/AssumptionsProbeAll.v'",
    )
    allowed = {
        REPO_ROOT / "scripts" / "coq_proof_scope.py",
        # Aggregator stores the probe target file as data, not as a scope decision.
        REPO_ROOT / "build" / "probe" / "aggregate_full_probe.py",
        # Probe builder names its output file by literal path.
        REPO_ROOT / "build" / "probe" / "build_full_probe.py",
        # This test itself encodes the strings to grep for.
        Path(__file__).resolve(),
    }
    offenders: list[str] = []
    for path in REPO_ROOT.rglob("*.py"):
        # Skip vendored / virtualenv / build trees.
        parts = set(path.parts)
        if parts & {".venv", "venv", "node_modules", "_build", ".git", "vendor"}:
            continue
        if path in allowed:
            continue
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        if any(s in text for s in probe_strings):
            offenders.append(str(path.relative_to(REPO_ROOT)))
    assert not offenders, (
        "These files hard-code probe paths; route them through "
        "scripts/coq_proof_scope.py:NON_PROOF_BEARING_FILES instead:\n"
        + "\n".join(f"  {o}" for o in offenders)
    )


@pytest.mark.parametrize("rel", sorted(NON_PROOF_BEARING_FILES))
def test_non_proof_bearing_file_exists(rel: str):
    """Sanity: every NON_PROOF_BEARING entry points to a real file."""
    assert (REPO_ROOT / rel).is_file(), (
        f"NON_PROOF_BEARING_FILES references {rel}, but it does not exist on disk. "
        f"Remove the entry or restore the file."
    )
