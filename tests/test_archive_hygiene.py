"""Archive hygiene gate.

Checks:
  1. Root markdown surface — no stale working-doc or handoff files that
     should have been deleted or integrated before closeout.
  2. Required root files exist for the current closeout surface.
  3. Key build artefacts exist (verification_receipt.json, isomorphism_map.json).
  4. If a local INQUISITOR report exists, it must not record a fail verdict.
"""
from __future__ import annotations

import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]

# Patterns in root-level filenames that indicate stale working docs.
# These should be cleaned up before closeout.
STALE_PATTERNS = [
    "*_HANDOFF.md",
    "*_WORKING_PLAN.md",
    "*_WORKING_DOC.md",
    "*_FIRST_PRINCIPLES_AUDIT.md",
    "*_WORKING_NOTES.md",
]

# Root markdown files that must be present.
REQUIRED_ROOT_FILES = [
    "README.md",
    "STYLE_GUIDE.md",
]

# Build artefacts that must be present.
REQUIRED_ARTEFACTS = [
    "artifacts/verification_receipt.json",
    "build/isomorphism_map.json",
]


class TestRootMarkdownSurface:
    def test_no_stale_working_docs(self):
        """Root must not contain stale handoff or working-plan files."""
        found = []
        for pattern in STALE_PATTERNS:
            found.extend(ROOT.glob(pattern))
        assert not found, (
            "Stale working docs found at repo root — delete or integrate before closeout:\n"
            + "\n".join(f"  {p.name}" for p in found)
        )

    def test_required_root_files_exist(self):
        """Core documentation files must be present at repo root."""
        missing = [f for f in REQUIRED_ROOT_FILES if not (ROOT / f).exists()]
        assert not missing, f"Required root files missing: {missing}"


class TestBuildManifest:
    def test_required_artefacts_exist(self):
        """Key build and verification artefacts must be present."""
        missing = [f for f in REQUIRED_ARTEFACTS if not (ROOT / f).exists()]
        assert not missing, f"Required build artefacts missing: {missing}"

    def test_verification_receipt_is_pass(self):
        """verification_receipt.json must carry a PASS verdict."""
        receipt_path = ROOT / "artifacts" / "verification_receipt.json"
        if not receipt_path.exists():
            pytest.skip("verification_receipt.json not present")
        receipt = json.loads(receipt_path.read_text())
        verdict = receipt.get("verdict", "")
        assert "VERIFIED" in verdict or verdict == "PASS", (
            f"verification_receipt.json verdict is not PASS/VERIFIED: {verdict!r}"
        )


class TestInquisitorReport:
    def test_inquisitor_report_has_no_high_findings(self):
        """A locally generated INQUISITOR report must not record a FAIL verdict."""
        report_path = ROOT / "INQUISITOR_REPORT.md"
        if not report_path.exists():
            pytest.skip("INQUISITOR_REPORT.md not present")
        text = report_path.read_text()
        # The report contains HIGH findings only when the inquisitor fails.
        # A passing run overwrites the report with an OK summary.
        assert "INQUISITOR: FAIL" not in text, (
            "INQUISITOR_REPORT.md records a FAIL verdict — re-run inquisitor."
        )
