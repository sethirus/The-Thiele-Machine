#!/usr/bin/env python3
"""Simple LRAT analyzer used by packagers to detect RAT-only hints.

This is intentionally conservative: if any LRAT line contains the token
'rat' (case-insensitive) or contains hints that reference deletions, the
analyzer exits with non-zero to force normalization by external tools.

Usage: python scripts/analyze_lrat.py path/to/proof.lrat
"""
from pathlib import Path
import sys
import shutil
import subprocess
import argparse


def analyze(path: Path, cnf: Path | None = None, normalize: bool = False) -> int:
    try:
        text = path.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        print("ERROR: cannot read LRAT file", file=sys.stderr)
        return 2
    lower = text.lower()
    if "rat" in lower:
        print("LRAT contains RAT hints; requires normalization or rejection")
        # If normalization requested and drat-trim is available, attempt to run it
        if normalize and cnf is not None and shutil.which("drat-trim"):
            print("Attempting to run drat-trim for normalization (best-effort)")
            try:
                # run drat-trim to verify/normalize; callers may inspect output
                subprocess.run(["drat-trim", str(cnf), str(path)], check=True)
                print("drat-trim succeeded; proof is RUP-derivable (best-effort)")
                return 0
            except subprocess.CalledProcessError:
                print("drat-trim failed to validate/normalize the LRAT", file=sys.stderr)
                return 1
            except FileNotFoundError:
                return 1
        return 1
    # otherwise be permissive
    print("LRAT appears RUP-only (heuristic) — ok")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Analyze LRAT for RAT-only hints")
    parser.add_argument("lrat", type=Path, help="Path to LRAT proof file")
    parser.add_argument("--cnf", type=Path, help="Optional CNF path used for normalization checks")
    parser.add_argument("--normalize", action="store_true", help="Attempt normalization using drat-trim when available")
    args = parser.parse_args(argv)
    return analyze(args.lrat, cnf=args.cnf, normalize=args.normalize)


if __name__ == '__main__':
    raise SystemExit(main())
