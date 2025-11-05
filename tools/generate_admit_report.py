"""Generate a comprehensive admit/axiom inventory for the repository.

This script scans every Coq source file (``*.v``) beneath the repository root,
collects any admitted proofs and axiom declarations, and writes a canonical
report.  The resulting document is intended to be committed at the project root
as ``ADMIT_REPORT.txt`` so that developers and auditors share a single source of
truth about the current trust perimeter.

Usage
-----
    python tools/generate_admit_report.py [--output ADMIT_REPORT.txt]

The script is deterministic: entries are sorted alphabetically by path and then
by line number so that re-running it after unrelated edits keeps the report
stable.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import re
from typing import Iterable, List


REPO_ROOT = Path(__file__).resolve().parents[1]
COQ_EXT = ".v"


ADMITTED_RE = re.compile(r"\b(?:Admitted|admit)\.")
AXIOM_RE = re.compile(r"^\s*Axiom\b")


@dataclass(frozen=True)
class Finding:
    kind: str  # "Admitted" or "Axiom"
    path: Path
    line_no: int
    line: str

    @property
    def category(self) -> str:
        """Return a coarse bucket used in the final report."""

        relative = self.path.relative_to(REPO_ROOT)
        parts = relative.parts
        if parts and parts[0] == "coq":
            if len(parts) > 1 and parts[1] == "sandboxes":
                return "Sandboxes"
            return "Active Coq tree"
        if parts and parts[0] == "archive":
            return "Archive"
        return "Other"


def iter_coq_files(root: Path) -> Iterable[Path]:
    for path in root.rglob(f"*{COQ_EXT}"):
        # Skip build artefacts if they exist.
        if any(part in {"_build", "_opam"} for part in path.parts):
            continue
        yield path


def scan_file(path: Path) -> List[Finding]:
    findings: List[Finding] = []
    with path.open("r", encoding="utf-8") as handle:
        for idx, line in enumerate(handle, start=1):
            if ADMITTED_RE.search(line):
                findings.append(
                    Finding("Admitted", path, idx, line.rstrip())
                )
            elif AXIOM_RE.search(line):
                findings.append(
                    Finding("Axiom", path, idx, line.rstrip())
                )
    return findings


def generate_findings(root: Path) -> List[Finding]:
    findings: List[Finding] = []
    for file_path in iter_coq_files(root):
        findings.extend(scan_file(file_path))
    # Sort using POSIX-style relative paths so the output is stable across OSes
    findings.sort(key=lambda f: (f.path.relative_to(root).as_posix(), f.line_no))
    return findings


def render_report(findings: List[Finding]) -> str:
    sections: List[str] = ["Admit and axiom inventory", ""]

    categories = {
        "Active Coq tree": [],
        "Sandboxes": [],
        "Archive": [],
        "Other": [],
    }

    for finding in findings:
        categories.setdefault(finding.category, []).append(finding)

    totals = {"Admitted": 0, "Axiom": 0}

    for bucket in categories:
        bucket_findings = categories[bucket]
        if not bucket_findings:
            continue
        sections.append(bucket)
        sections.append("-" * len(bucket))
        for finding in bucket_findings:
            rel = finding.path.relative_to(REPO_ROOT)
            # Render relative paths with forward slashes for platform-independent
            # canonical reports (ADMIT_REPORT.txt uses POSIX-style separators).
            rel_text = rel.as_posix()
            sections.append(
                f"{finding.kind:8} {rel_text}:{finding.line_no}: {finding.line}"
            )
            totals[finding.kind] += 1
        sections.append("")

    sections.append("Summary")
    sections.append("-------")
    sections.append(f"Total admitted: {totals['Admitted']}")
    sections.append(f"Total axioms:  {totals['Axiom']}")

    return "\n".join(sections) + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=REPO_ROOT / "ADMIT_REPORT.txt",
        help="Where to write the report (default: ADMIT_REPORT.txt).",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    findings = generate_findings(REPO_ROOT)
    report = render_report(findings)
    args.output.write_text(report, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
