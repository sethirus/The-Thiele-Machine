#!/usr/bin/env python3
"""Assumption/axiom regression gate for critical Coq kernel files.

This gate fails when foundational files introduce local trust escapes such as
`Axiom`, `Parameter`, `Hypothesis`, `Variable`, `Context`, or `Admitted.`.

Run:
  python3 scripts/inquisitor_assumption_gate.py
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]

# Critical files that must remain free of local assumptions and admitted proofs.
ZERO_ASSUMPTION_FILES = [
    "coq/kernel/VMState.v",
    "coq/kernel/VMStep.v",
    "coq/kernel/MuInitiality.v",
    "coq/kernel/MuCostModel.v",
    "coq/kernel/MuLedgerConservation.v",
]

AXIOM_PATTERN = re.compile(r"\bAxiom\b")
TOPLEVEL_ASSUMPTION_PATTERN = re.compile(
    r"\b(Parameter|Hypothesis|Variable|Variables|Context)\b"
)
ADMITTED_PATTERN = re.compile(r"\bAdmitted\s*\.")


def strip_coq_comments(text: str) -> str:
    """Remove nested Coq comments while preserving line breaks."""
    out = []
    depth = 0
    i = 0
    while i < len(text):
        pair = text[i : i + 2]
        if pair == "(*":
            depth += 1
            i += 2
            continue
        if pair == "*)" and depth > 0:
            depth -= 1
            i += 2
            continue
        ch = text[i]
        if depth == 0:
            out.append(ch)
        elif ch == "\n":
            # Keep newlines from commented blocks so line numbers remain stable.
            out.append("\n")
        i += 1
    return "".join(out)


def scan_file_for_trust_escapes(file_path: Path) -> list[dict[str, str | int]]:
    """Return all trust-escape findings in a Coq file."""
    raw = file_path.read_text(encoding="utf-8", errors="ignore")
    text = strip_coq_comments(raw)
    findings: list[dict[str, str | int]] = []

    section_depth = 0
    for lineno, line in enumerate(text.splitlines(), start=1):
        stripped = line.strip()
        if not stripped:
            continue

        # Track section nesting to distinguish scoped variables from global ones.
        if re.match(r"^Section\b", stripped):
            section_depth += 1
        elif re.match(r"^End\b", stripped):
            section_depth = max(0, section_depth - 1)

        if AXIOM_PATTERN.search(stripped):
            findings.append(
                {
                    "line": lineno,
                    "kind": "axiom-declaration",
                    "text": stripped,
                }
            )
        if section_depth == 0 and TOPLEVEL_ASSUMPTION_PATTERN.search(stripped):
            findings.append(
                {
                    "line": lineno,
                    "kind": "toplevel-assumption-declaration",
                    "text": stripped,
                }
            )
        if ADMITTED_PATTERN.search(stripped):
            findings.append(
                {
                    "line": lineno,
                    "kind": "admitted-proof",
                    "text": stripped,
                }
            )

    return findings


def write_report(report: dict) -> None:
    report_dir = REPO_ROOT / "artifacts" / "proof_gate"
    report_dir.mkdir(parents=True, exist_ok=True)
    report_path = report_dir / "assumption_gate_report.json"
    report_path.write_text(json.dumps(report, indent=2), encoding="utf-8")


def audit_assumptions() -> int:
    print("\n" + "=" * 80)
    print("INQUISITOR ASSUMPTION GATE")
    print("=" * 80 + "\n")

    all_clean = True
    file_findings: dict[str, list[dict[str, str | int]]] = {}

    for file_rel in ZERO_ASSUMPTION_FILES:
        file_path = REPO_ROOT / file_rel
        if not file_path.exists():
            all_clean = False
            file_findings[file_rel] = [
                {"line": 0, "kind": "missing-file", "text": "File not found"}
            ]
            print(f"[scanning] {file_rel}")
            print("  ❌ FAILED: File not found")
            continue

        print(f"[scanning] {file_rel}")
        findings = scan_file_for_trust_escapes(file_path)

        if findings:
            all_clean = False
            file_findings[file_rel] = findings
            print(f"  ❌ FAILED: {len(findings)} trust-escape finding(s)")
            for finding in findings:
                print(
                    f"     - line {finding['line']}: "
                    f"{finding['kind']} :: {finding['text']}"
                )
        else:
            print("  ✓ PASS: No local assumptions or admitted proofs")

    report = {
        "repo_root": str(REPO_ROOT),
        "scanned_files": ZERO_ASSUMPTION_FILES,
        "passed": all_clean,
        "findings": file_findings,
    }
    write_report(report)

    print("\n" + "=" * 80)
    print("GATE RESULT")
    print("=" * 80 + "\n")
    if all_clean:
        print("✓ PASS: Critical kernel files are assumption-free")
        print("Report: artifacts/proof_gate/assumption_gate_report.json")
        return 0

    print("❌ FAIL: Trust escapes detected in critical kernel files")
    print("Report: artifacts/proof_gate/assumption_gate_report.json")
    return 1


if __name__ == "__main__":
    raise SystemExit(audit_assumptions())
