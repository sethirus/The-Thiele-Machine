#!/usr/bin/env python3
"""
Run SAT benchmarks on all test instances.

This script runs the SAT benchmark tool on all .cnf files in benchmarks/sat_instances/
and aggregates the results.
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description="Run SAT benchmarks on all instances")
    parser.add_argument("--limit", type=int, help="Limit number of instances")
    parser.add_argument("--timeout", type=int, default=60, help="Timeout per instance")
    args = parser.parse_args()

    root = Path(__file__).parent.parent
    instances_dir = root / "benchmarks/sat_instances"

    if not instances_dir.exists():
        print(f"Error: {instances_dir} does not exist", file=sys.stderr)
        return 1

    cnf_files = sorted(instances_dir.glob("*.cnf"))

    if args.limit:
        cnf_files = cnf_files[:args.limit]

    if not cnf_files:
        print(f"Error: No .cnf files found in {instances_dir}", file=sys.stderr)
        return 1

    print(f"Running SAT benchmarks on {len(cnf_files)} instances...")

    successes = 0
    failures = 0

    for cnf_file in cnf_files:
        output_json = f"/tmp/{cnf_file.stem}_result.json"

        cmd = [
            "python3", str(root / "tools/sat_benchmark.py"),
            str(cnf_file),
            "--output", output_json,
            "--timeout", str(args.timeout)
        ]

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=args.timeout + 30,
                cwd=root
            )

            if result.returncode == 0:
                successes += 1
                print(f"✓ {cnf_file.name}")
            else:
                failures += 1
                print(f"✗ {cnf_file.name}: exit code {result.returncode}")
                if result.stderr:
                    print(f"  {result.stderr[:200]}")
        except subprocess.TimeoutExpired:
            failures += 1
            print(f"✗ {cnf_file.name}: timeout")
        except Exception as e:
            failures += 1
            print(f"✗ {cnf_file.name}: {str(e)[:100]}")

    print(f"\nResults: {successes} successes, {failures} failures")

    if failures > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
