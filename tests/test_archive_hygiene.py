"""Archive hygiene gate.

Checks:
  1. Root markdown surface — no working-doc or handoff files.
  2. Required root files exist.
  3. Key proof artefacts exist (the assumption receipt, the proof
     dependency DAG and the vacuity audit).
  4. If a local INQUISITOR report exists, it must not record a fail verdict.
"""
from __future__ import annotations

import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]

# Patterns in root-level filenames that indicate working docs.
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
]

# Proof artefacts that must be present.
REQUIRED_ARTEFACTS = [
    "artifacts/print_assumptions_all_proofs.json",
    "artifacts/proof_dependency_dag.json",
    "artifacts/vacuity_audit.json",
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
        """Key proof artefacts must be present."""
        missing = [f for f in REQUIRED_ARTEFACTS if not (ROOT / f).exists()]
        assert not missing, f"Required build artefacts missing: {missing}"


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


def test_tracked_tree_excludes_build_products_and_work_sessions():
    """The commit contains source/deliverables, not local authoring machinery."""
    import subprocess

    tracked = subprocess.check_output(
        ['git', 'ls-files', '-z'], cwd=ROOT
    ).decode().split('\0')
    forbidden_roots = ('build/', '.claude/', '.codex/', 'docs/integration/',
                       'monograph/page-composition/', 'monograph/companion/')
    generated = {'.vo', '.vos', '.vok', '.glob', '.aux', '.toc', '.out', '.pyc'}
    working_names = {'AGENTS.md', 'CLAUDE.md', 'STYLE_GUIDE.md'}
    bad = [name for name in tracked if name and (
        name.startswith(forbidden_roots) or Path(name).suffix in generated
        or Path(name).name in working_names or '__pycache__' in Path(name).parts
        or name.startswith('vendor/') and Path(name).name in
        {'Makefile.coq', 'Makefile.coq.conf', '.Makefile.coq.d'}
    )]
    allowed_records = {
        'print_assumptions_all_proofs.json', 'print_assumptions_all_proofs.txt',
        'PROOF_FOUNDATION_AUDIT.md', 'proof_dependency_connectivity.json',
        'proof_dependency_dag.json', 'proof_dependency_file_graph.mmd',
        'vacuity_audit.json', 'assumptions/probe_inventory.json',
        'assumptions/probe_all_output.txt', 'assumptions/probe_all_err.txt',
        'assumptions/probe_batches.json',
    }
    bad += [name for name in tracked if name.startswith('artifacts/')
            and name.removeprefix('artifacts/') not in allowed_records]
    assert not bad, 'Working material in the tracked tree:\n' + '\n'.join(bad)
