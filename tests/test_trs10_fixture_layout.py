from __future__ import annotations

import json
from pathlib import Path

import pytest

pytestmark = pytest.mark.trs


PROJECT_ROOT = Path(__file__).resolve().parent.parent
FIXTURE_ROOT = PROJECT_ROOT / "tests" / "fixtures" / "trs10"
MANIFEST = FIXTURE_ROOT / "manifest.json"


def test_trs10_fixture_manifest_exists() -> None:
    assert MANIFEST.exists(), "TRS-1.0 fixture manifest is missing"


def test_trs10_fixture_layout_matches_manifest() -> None:
    payload = json.loads(MANIFEST.read_text(encoding="utf-8"))
    required_layout = payload["required_layout"]
    for relative in required_layout:
        path = FIXTURE_ROOT / relative
        assert path.exists(), f"Required TRS-1.0 fixture path missing: {relative}"
        assert path.is_dir(), f"Required TRS-1.0 fixture path is not a directory: {relative}"


def test_trs10_fixture_directories_have_readmes() -> None:
    for directory in [
        FIXTURE_ROOT / "fileset" / "valid",
        FIXTURE_ROOT / "fileset" / "invalid" / "signature",
        FIXTURE_ROOT / "fileset" / "invalid" / "digest",
        FIXTURE_ROOT / "fileset" / "invalid" / "payload_tamper",
        FIXTURE_ROOT / "fileset" / "invalid" / "schema",
        FIXTURE_ROOT / "fileset" / "invalid" / "kind_confusion",
        FIXTURE_ROOT / "fileset" / "invalid" / "path_traversal",
        FIXTURE_ROOT / "fileset" / "invalid" / "metadata",
        FIXTURE_ROOT / "fileset" / "invalid" / "json_edge",
        FIXTURE_ROOT / "fileset" / "invalid" / "content",
        FIXTURE_ROOT / "fileset" / "invalid" / "size",
        FIXTURE_ROOT / "fileset" / "input" / "basename_collision",
        FIXTURE_ROOT / "execution" / "valid",
        FIXTURE_ROOT / "execution" / "invalid" / "signature",
        FIXTURE_ROOT / "execution" / "invalid" / "digest",
        FIXTURE_ROOT / "execution" / "invalid" / "schema",
        FIXTURE_ROOT / "execution" / "invalid" / "source_tamper",
        FIXTURE_ROOT / "execution" / "invalid" / "fuel",
        FIXTURE_ROOT / "execution" / "invalid" / "pre_state",
        FIXTURE_ROOT / "execution" / "invalid" / "replay",
        FIXTURE_ROOT / "execution" / "invalid" / "mu",
        FIXTURE_ROOT / "execution" / "invalid" / "nondeterminism",
        FIXTURE_ROOT / "execution" / "canonicalization" / "equivalent",
        FIXTURE_ROOT / "execution" / "canonicalization" / "distinct",
        FIXTURE_ROOT / "stress" / "large",
        FIXTURE_ROOT / "compat" / "v1" / "golden",
    ]:
        assert (directory / "README.md").exists(), f"Fixture directory missing README: {directory}"