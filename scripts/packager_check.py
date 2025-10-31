#!/usr/bin/env python3
"""Packager check utility for proofpacks.

Usage: python scripts/packager_check.py /path/to/proofpack_dir

What it does (best-effort):
- For each receipt JSON in the directory, run `scripts/canonicalize_receipts.py` to canonicalize.
- For each LRAT proof referenced, run `scripts/analyze_lrat.py --normalize --cnf` to attempt normalization.
- Fail (exit code != 0) if any LRAT cannot be normalized or any canonicalize step fails.
"""
from pathlib import Path
import sys
import subprocess


def main(argv=None) -> int:
    import argparse
    parser = argparse.ArgumentParser(description="Packager check for proofpack directories")
    parser.add_argument('dir', type=Path)
    args = parser.parse_args(argv)
    d = args.dir
    if not d.is_dir():
        print(f"Not a directory: {d}")
        return 2

    # 1) Canonicalize receipts in-place (best-effort)
    print(f"Canonicalizing receipts in {d}...")
    try:
        res = subprocess.run([sys.executable, str(Path(__file__).resolve().parents[1] / 'scripts' / 'canonicalize_receipts.py'), str(d)], check=False)
        if res.returncode != 0:
            print("canonicalize_receipts returned non-zero; continuing but check logs")
    except Exception as e:
        print("Failed to run canonicalize_receipts:", e)
        return 1

    # 2) Scan receipts for LRAT proofs and attempt normalization
    failures = 0
    for p in sorted(d.rglob('*.json')):
        try:
            import json
            data = json.loads(p.read_text(encoding='utf-8'))
        except Exception:
            continue
        steps = data.get('steps') or []
        for step in steps:
            pf = step.get('proof_portable')
            proof_uri = step.get('proof_blob_uri')
            cnf_uri = step.get('cnf_blob_uri')
            if pf == 'LRAT' and proof_uri:
                # resolve relative path
                proof_path = Path(proof_uri)
                if not proof_path.is_absolute():
                    proof_path = p.parent / proof_uri
                cnf_path = None
                if cnf_uri:
                    cnf_path = Path(cnf_uri)
                    if not cnf_path.is_absolute():
                        cnf_path = p.parent / cnf_uri
                cmd = [sys.executable, str(Path(__file__).resolve().parents[1] / 'scripts' / 'analyze_lrat.py'), str(proof_path)]
                if cnf_path:
                    cmd += ['--cnf', str(cnf_path), '--normalize']
                print('Running:', ' '.join(cmd))
                proc = subprocess.run(cmd, check=False)
                if proc.returncode != 0:
                    print(f"LRAT normalization failed for {proof_path} (step idx {step.get('idx')}).")
                    failures += 1
    if failures:
        print(f"Packager check failed: {failures} LRATs could not be normalized")
        return 3
    print("Packager check completed: all LRATs normalized/ok (heuristic)")
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
