# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env python3
"""Command line entry point for the Thiele bug hunter."""

from __future__ import annotations

import argparse
from pathlib import Path

from tools.bughunter import BugHunter, DEFAULT_RULES


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run the Thiele Machine bug hunting framework")
    parser.add_argument(
        "repo",
        type=Path,
        help="Path to the repository to analyse",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("results/bughunter_report.json"),
        help="Where to write the JSON report (default: results/bughunter_report.json)",
    )
    parser.add_argument(
        "--rules",
        nargs="*",
        default=None,
        help="Subset of rule names to run; defaults to all",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    repo = args.repo
    if args.rules:
        selected = [rule for rule in DEFAULT_RULES if rule.name in set(args.rules)]
        if not selected:
            raise SystemExit("No matching rules selected")
    else:
        selected = DEFAULT_RULES

    hunter = BugHunter(repo, rules=selected)
    report = hunter.run()
    output_path = hunter.save_report(args.output)
    print(f"Analysed {report.scanned_files} files; findings: {len(report.findings)}")
    print(f"Report written to {output_path}")


if __name__ == "__main__":
    main()
