# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.bughunter import BugHunter, DEFAULT_RULES


def test_bug_hunter_detects_critical_patterns(tmp_path):
    repo = Path(__file__).parent / "data" / "vulnerable_repo"
    hunter = BugHunter(repo)
    report = hunter.run()

    assert report.scanned_files == 1
    assert {rule for rule in report.executed_rules} == {r.name for r in DEFAULT_RULES}

    finding_rules = {finding.rule for finding in report.findings}
    assert {"subprocess-shell", "eval-exec", "yaml-unsafe-load"}.issubset(finding_rules)

    # os.system should also trigger the subprocess rule (duplicate severity check)
    shell_findings = [f for f in report.findings if f.rule == "subprocess-shell"]
    assert any("shell=True" in f.message or "os.system" in f.message for f in shell_findings)
    assert any("os.system" in f.message for f in shell_findings)
    assert any("os.popen" in f.message for f in shell_findings)
    assert any("subprocess.check_output" in f.message for f in shell_findings)
    assert any("subprocess.Popen" in f.message for f in shell_findings)

    for finding in report.findings:
        assert finding.remediation, "Each finding must include a remediation hint"
        assert finding.line > 0

    # Ensure report can be serialised to JSON and written to disk
    output_path = tmp_path / "bughunter_report.json"
    hunter.save_report(output_path)
    saved = output_path.read_text()
    assert "subprocess-shell" in saved
    assert "eval-exec" in saved
