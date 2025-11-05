"""Ensure Coq files cited in the README remain admit-free."""

from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import Set

README_PATH = Path("README.md")


_CITATION_PATTERN = re.compile(r"coq/[A-Za-z0-9_./]+\.v")


def _extract_coq_paths(readme: Path) -> Set[Path]:
    text = readme.read_text(encoding="utf-8")
    matches = set(Path(match) for match in _CITATION_PATTERN.findall(text))
    return {path for path in matches if path.exists()}


def _scan_file(path: Path) -> int:
    count = 0
    for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        if "Admitted" in line or "admit." in line:
            count += 1
    return count


def main(argv: list[str]) -> int:
    readme = Path(argv[1]) if len(argv) > 1 else README_PATH
    coq_paths = _extract_coq_paths(readme)
    if not coq_paths:
        print("No Coq references found in README; nothing to validate.")
        return 0

    offending: list[str] = []
    for path in sorted(coq_paths):
        admit_count = _scan_file(path)
        if admit_count:
            offending.append(f"{path}: {admit_count} Admitted statements")

    if offending:
        for line in offending:
            print(f"ERROR: {line}")
        return 1

    print("Coq README references are admit-free.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
