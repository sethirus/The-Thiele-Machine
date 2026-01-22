#!/usr/bin/env python3
"""Check that disallowed packages are not present in main requirements but are listed in requirements-optional.txt"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REQ = ROOT / "config" / "requirements.txt"
OPT = ROOT / "config" / "requirements-optional.txt"
OUT = ROOT / "artifacts" / "requirements_check.json"

BANNED = ["biopython", "ecdsa", "nbconvert"]


def parse_reqs(path: Path, include_commented=False):
    if not path.exists():
        return []
    lines = []
    for l in path.read_text().splitlines():
        s = l.strip()
        if not s:
            continue
        # token is package name possibly with extras and version spec
        # when scanning main requirements we ignore commented lines; for optional we allow them
        if s.startswith("#") and not include_commented:
            continue
        s_norm = s.lstrip("# ")
        token = s_norm.split("==")[0].split("<=")[0].split(">=")[0].split("[")[0].strip().lower()
        lines.append(token)
    return lines


def main():
    main_reqs = parse_reqs(REQ)
    opt_reqs = parse_reqs(OPT, include_commented=True)
    results = {"main_reqs": main_reqs, "optional_reqs": opt_reqs}

    errors = []
    for b in BANNED:
        if b.lower() in main_reqs:
            errors.append(f"Disallowed package {b} found in requirements.txt")
        if b.lower() not in opt_reqs:
            errors.append(f"Package {b} not listed in requirements-optional.txt")

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(results, indent=2))

    if errors:
        print("ERROR: Requirements check failed:\n" + "\n".join(errors))
        sys.exit(1)
    print("Requirements check OK: banned packages quarantined to requirements-optional.txt")


if __name__ == '__main__':
    main()
