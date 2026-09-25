"""Check that the SHA-256 recorded by MasterSummary.v matches its artifact.

The Coq lemma records a string equality and does not read the filesystem.

This test reads the artifact named by the Coq source, computes its SHA-256, and
compares that value with every hash literal recorded in the source.

It therefore catches a stale pin after the named artifact changes, including when
the Coq lemma itself would still compile by reflexivity.
"""

from __future__ import annotations

import hashlib
import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
MASTER_SUMMARY = REPO_ROOT / "coq" / "kernel" / "aggregators" / "MasterSummary.v"

# Matches:  artifact_path master_inquisitor_assumption_artifact = "<path>"
_PATH_RE = re.compile(
    r"artifact_path\s+master_inquisitor_assumption_artifact\s*=\s*\"([^\"]+)\""
)
# Matches:  artifact_sha256 master_inquisitor_assumption_artifact = "<hex>"
_SHA_RE = re.compile(
    r"artifact_sha256\s+master_inquisitor_assumption_artifact\s*=\s*\n?\s*\"([0-9a-f]{64})\""
)


def _pinned_path_and_hashes() -> tuple[str, set[str]]:
    text = MASTER_SUMMARY.read_text(encoding="utf-8")
    paths = set(_PATH_RE.findall(text))
    hashes = set(_SHA_RE.findall(text))
    assert paths, f"No pinned artifact_path found in {MASTER_SUMMARY}"
    assert hashes, f"No pinned artifact_sha256 found in {MASTER_SUMMARY}"
    assert len(paths) == 1, f"Conflicting pinned paths in MasterSummary.v: {sorted(paths)}"
    return paths.pop(), hashes


def test_pinned_artifact_path_exists() -> None:
    rel, _ = _pinned_path_and_hashes()
    target = REPO_ROOT / rel
    assert target.is_file(), (
        f"MasterSummary.v pins the artifact {rel!r}, but that file does not "
        f"exist at {target}."
    )


def test_pinned_sha256_is_internally_consistent() -> None:
    """Every pinned hex string in the file must be the same hash.

    The hash appears in the Prop, the Lemma, and the Theorem's `change`. If a
    repin updates only some of them the file still compiles (each occurrence
    is independently reflexive), so check they agree.
    """
    _, hashes = _pinned_path_and_hashes()
    assert len(hashes) == 1, (
        "MasterSummary.v pins more than one distinct SHA-256 for the same "
        f"artifact: {sorted(hashes)}. A partial repin leaves the file "
        "compiling but self-inconsistent."
    )


def test_pinned_sha256_matches_actual_file() -> None:
    rel, hashes = _pinned_path_and_hashes()
    target = REPO_ROOT / rel
    actual = hashlib.sha256(target.read_bytes()).hexdigest()
    pinned = next(iter(hashes))
    assert actual == pinned, (
        f"Pinned SHA-256 in MasterSummary.v is stale for {rel}.\n"
        f"  pinned: {pinned}\n"
        f"  actual: {actual}\n\n"
        "The Coq lemma `master_assumption_artifact_sha256_pinned` proves a "
        "string equals itself and cannot detect this. Update the hex string "
        "in coq/kernel/aggregators/MasterSummary.v (it appears in the Prop, "
        "the Lemma, and the Theorem's `change` -- update all of them)."
    )
