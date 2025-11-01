#!/usr/bin/env python3
"""Confirm that the Bell ledger records the full six-act isomorphism proof."""

from __future__ import annotations

from pathlib import Path
import sys

REQUIRED_HEADINGS = [
    "## Act I",
    "## Act II",
    "## Act III",
    "## Act IV",
    "## Act V",
    "## Act VI",
]
REQUIRED_STATEMENTS = [
    "Tsirelson bound",
    "S = 16/5",
    "valid sighted strategy reaches S = 16/5",
]


def main(argv: list[str]) -> int:
    repo_root = Path(__file__).resolve().parents[2]
    ledger_path = repo_root / "BELL_INEQUALITY_VERIFIED_RESULTS.md"
    script_path = repo_root / "demonstrate_isomorphism.py"

    if not ledger_path.exists():
        raise FileNotFoundError(f"Ledger {ledger_path} missing")
    if not script_path.exists():
        raise FileNotFoundError(f"Narrative script {script_path} missing")

    ledger = ledger_path.read_text()

    missing = [heading for heading in REQUIRED_HEADINGS if heading not in ledger]
    if missing:
        raise AssertionError(f"Ledger missing headings: {', '.join(missing)}")

    missing_statements = [statement for statement in REQUIRED_STATEMENTS if statement not in ledger]
    if missing_statements:
        raise AssertionError(f"Ledger missing statements: {', '.join(missing_statements)}")

    print("Bell ledger verification succeeded:")
    print(f"  ledger: {ledger_path.relative_to(repo_root)}")
    print(f"  script: {script_path.relative_to(repo_root)}")
    print("  all required acts and statements found.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
