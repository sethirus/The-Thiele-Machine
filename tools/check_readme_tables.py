"""Validate numerical consistency of the README scaling table."""

from __future__ import annotations

import re
import sys
from pathlib import Path


TABLE_HEADER = "| Problem Size (n) | Blind μ_conflict"


def _parse_first_float(cell: str) -> float:
    match = re.search(r"[-+]?(?:\d+\.?\d*|\.\d+)(?:[eE][-+]?\d+)?", cell)
    if not match:
        raise ValueError(f"Could not parse numeric value from cell: {cell!r}")
    return float(match.group())


def check_readme(readme_path: Path) -> list[str]:
    text = readme_path.read_text(encoding="utf-8")
    lines = text.splitlines()
    errors: list[str] = []

    try:
        header_index = next(i for i, line in enumerate(lines) if line.startswith(TABLE_HEADER))
    except StopIteration:
        errors.append("Partition summary table not found in README.")
        return errors

    data_lines = []
    for line in lines[header_index + 2 :]:
        if not line.strip():
            break
        if line.startswith("|"):
            data_lines.append(line)

    if not data_lines:
        errors.append("No data rows found under partition summary table.")
        return errors

    for row in data_lines:
        cells = [cell.strip() for cell in row.strip().strip("|").split("|")]
        if len(cells) < 4:
            errors.append(f"Row has insufficient columns: {row}")
            continue
        try:
            blind = _parse_first_float(cells[1])
            sighted = _parse_first_float(cells[2])
            ratio_reported = _parse_first_float(cells[3])
        except ValueError as exc:
            errors.append(str(exc))
            continue
        if sighted == 0:
            errors.append(f"Sighted value is zero in row: {row}")
            continue
        computed = blind / sighted
        if abs(computed - ratio_reported) > 5e-3:
            errors.append(
                f"Mismatch in row {row!r}: reported ratio {ratio_reported:.3f}"
                f" vs computed {computed:.3f}"
            )
    return errors


def main(argv: list[str]) -> int:
    readme_path = Path(argv[1]) if len(argv) > 1 else Path("README.md")
    errors = check_readme(readme_path)
    if errors:
        for err in errors:
            print(f"ERROR: {err}")
        return 1
    print(f"README table validation passed for {readme_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
