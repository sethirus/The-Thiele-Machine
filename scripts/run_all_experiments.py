# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env python3
"""Run Thiele Machine experiments and record receipts.

This script executes the two small experiments used throughout the
repository:

1. The Engine of Discovery and the Law of NUSD.
2. Structured Tseitin instances solved by both blind and sighted solvers.

Outputs are written to the ``results`` directory.  A SHA256 hash of each
receipt is printed for reproducibility.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
from contextlib import redirect_stdout

# Make repository root importable
import sys
sys.path.append(str(Path(__file__).resolve().parent.parent))

# Import experiment entry points
import attempt
from scripts.generate_tseitin_data import run_single_experiment

RESULTS_DIR = Path("results")
RESULTS_DIR.mkdir(exist_ok=True)

def _hash_file(path: Path) -> str:
    """Return the SHA256 hash of a file's bytes."""
    return hashlib.sha256(path.read_bytes()).hexdigest()

def run_engine_of_discovery() -> str:
    """Run the Engine of Discovery experiment and return output hash."""
    out_file = RESULTS_DIR / "engine_output.txt"
    with out_file.open("w", encoding="utf-8") as f, redirect_stdout(f):
        attempt.run_engine_and_law()
    return _hash_file(out_file)

def run_tseitin_instances(ns: list[int]) -> dict[int, str]:
    """Run multiple structured Tseitin instances and return output hashes.

    ``ns`` is a list of problem sizes (number of vertices) to generate.  For
    each ``n`` we keep the seed and solver budgets fixed so that the resulting
    receipts are deterministic.  The outputs are written to
    ``results/tseitin_output_n{n}.json`` and a mapping from ``n`` to the
    file's SHA256 hash is returned.
    """
    hashes: dict[int, str] = {}
    for n in ns:
        params = (n, 0, 100_000, 5_000_000, 123456789)
        result = run_single_experiment(params)
        out_file = RESULTS_DIR / f"tseitin_output_n{n}.json"
        out_file.write_text(json.dumps(result, indent=2, default=int))
        hashes[n] = _hash_file(out_file)
    return hashes

def main() -> None:
    engine_hash = run_engine_of_discovery()
    # Run a small range of structured Tseitin instances to observe trends
    tseitin_hashes = run_tseitin_instances([8, 10, 12])
    print(f"engine_output.txt SHA256: {engine_hash}")
    for n, h in sorted(tseitin_hashes.items()):
        print(f"tseitin_output_n{n}.json SHA256: {h}")

if __name__ == "__main__":
    main()
