"""Smoke + correctness tests for the kernel-conversion vacuity gate.

The gate runs ``coqc`` against synthesised probes. ``coqc`` is heavy
(~1–2s per probe), so this test is marked ``slow`` and contained to a
single fixture file with both positive and negative cases.

The fixture ``coq/test_fixtures/VacuitySmoke.v`` carries inline annotations
declaring the expected verdict for each theorem; this test reads those
annotations and asserts the gate matches. The fixture lives under
``coq/test_fixtures/`` (excluded from the inquisitor's per-file audit)
because its theorems are deliberately vacuous by design — the gate exists
to detect such patterns, so the fixture must contain them.
"""
from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
SMOKE_FIXTURE = REPO_ROOT / "coq" / "test_fixtures" / "VacuitySmoke.v"
GATE_SCRIPT = REPO_ROOT / "scripts" / "vacuity_gate.py"


pytestmark = pytest.mark.skipif(
    shutil.which("coqc") is None,
    reason="coqc not available in this environment; vacuity gate requires it.",
)


_ANNOT_RE = re.compile(
    r"\(\*\s*(EXPECT_VACUOUS_TRUE|EXPECT_VACUOUS_HYP|EXPECT_CLEAR)\s*\*\)\s*\n"
    r"(?:Theorem|Lemma|Corollary)\s+([A-Za-z0-9_']+)"
)


def _read_expectations() -> dict[str, str]:
    """Map theorem-name → expected gate status, parsed from the fixture."""
    text = SMOKE_FIXTURE.read_text(encoding="utf-8")
    mapping = {
        "EXPECT_VACUOUS_TRUE": "vacuous-true",
        "EXPECT_VACUOUS_HYP": "vacuous-hyp",
        "EXPECT_CLEAR": "ok",
    }
    out: dict[str, str] = {}
    for m in _ANNOT_RE.finditer(text):
        tag, name = m.group(1), m.group(2)
        out[name] = mapping[tag]
    return out


def test_inquisitor_consumes_vacuity_audit(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """`_scan_kernel_convertibility_vacuity` must emit one HIGH per vacuous entry
    in the audit JSON, and zero findings for an `ok` entry.

    The function reads `<repo_root>/artifacts/vacuity_audit.json` directly; we
    point it at a temporary repo_root containing only an artifacts/ subdir.
    """
    sys.path.insert(0, str(REPO_ROOT / "scripts"))
    try:
        import inquisitor  # type: ignore[import-not-found]
    finally:
        sys.path.pop(0)

    fake_root = tmp_path / "repo"
    (fake_root / "artifacts").mkdir(parents=True)
    audit_payload = {
        "schema": "vacuity_audit.v1",
        "verdicts": [
            {
                "name": "fake_vacuous_true",
                "file": "coq/fake.v",
                "line": 5,
                "kind": "Theorem",
                "statement": "True",
                "status": "vacuous-true",
                "probe_a": {"probe_path": "build/vacuity_probes/probe_a.v"},
                "probe_b": None,
            },
            {
                "name": "fake_vacuous_hyp",
                "file": "coq/fake.v",
                "line": 7,
                "kind": "Theorem",
                "statement": "forall (P : Prop), P -> P",
                "status": "vacuous-hyp",
                "probe_a": None,
                "probe_b": {"probe_path": "build/vacuity_probes/probe_b.v"},
            },
            {
                "name": "fake_genuine",
                "file": "coq/fake.v",
                "line": 11,
                "kind": "Theorem",
                "statement": "forall n m : nat, S n + m = S (n + m)",
                "status": "ok",
                "probe_a": None,
                "probe_b": None,
            },
        ],
        "summary": {"total": 3, "ok": 1, "vacuous_true": 1, "vacuous_hyp": 1, "error": 0},
    }
    (fake_root / "artifacts" / "vacuity_audit.json").write_text(
        json.dumps(audit_payload), encoding="utf-8"
    )

    findings = inquisitor._scan_kernel_convertibility_vacuity(fake_root)
    assert len(findings) == 2, (
        f"Expected 2 HIGH findings (one per vacuous entry); got {len(findings)}: "
        f"{[(f.rule_id, f.severity, f.snippet) for f in findings]}"
    )
    names = {f.snippet for f in findings}
    assert names == {"fake_vacuous_true", "fake_vacuous_hyp"}
    assert all(f.severity == "HIGH" for f in findings)
    assert all(f.rule_id == "KERNEL_CONVERTIBILITY_VACUITY" for f in findings)


@pytest.mark.slow
def test_gate_matches_smoke_expectations(tmp_path: Path) -> None:
    expectations = _read_expectations()
    assert expectations, (
        f"No EXPECT_* annotations found in {SMOKE_FIXTURE}; the fixture is "
        "supposed to carry an annotation before every Theorem."
    )

    report_path = tmp_path / "vacuity_smoke_report.json"
    cmd = [
        sys.executable,
        str(GATE_SCRIPT),
        "--target",
        str(SMOKE_FIXTURE.relative_to(REPO_ROOT)),
        "--logical",
        "TestFixtures.VacuitySmoke",
        "--output",
        str(report_path),
    ]
    proc = subprocess.run(cmd, cwd=str(REPO_ROOT), capture_output=True, text=True)
    assert proc.returncode == 0, (
        f"vacuity_gate exited non-zero: rc={proc.returncode}\n"
        f"stdout={proc.stdout}\nstderr={proc.stderr}"
    )

    report = json.loads(report_path.read_text(encoding="utf-8"))
    verdict_map = {v["name"]: v["status"] for v in report["verdicts"]}

    missing = [n for n in expectations if n not in verdict_map]
    assert not missing, (
        f"Gate did not produce a verdict for theorems present in fixture: {missing}"
    )

    mismatches: list[str] = []
    for name, expected in expectations.items():
        actual = verdict_map[name]
        if actual != expected:
            mismatches.append(f"  {name}: expected {expected!r}, got {actual!r}")

    if mismatches:
        msg = "\n".join(["Gate verdicts diverged from fixture expectations:"] + mismatches)
        msg += "\n\nFull report:\n" + json.dumps(report["verdicts"], indent=2)
        pytest.fail(msg)
