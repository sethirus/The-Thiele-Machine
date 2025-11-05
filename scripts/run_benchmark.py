# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env python3
import argparse
import time
import json
import hashlib
import platform
import sys
from datetime import datetime

import os
import sys
# Ensure the parent directory is in sys.path for module import
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
# Import the core experiment harness from the repository
from generate_tseitin_data import run_single_experiment

def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(8192), b""):
            h.update(chunk)
    return h.hexdigest()

def iso_now():
    return datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ")

def main():
    parser = argparse.ArgumentParser(description="Run single benchmark and emit canonical JSON receipt.")
    parser.add_argument("--benchmark", choices=["tseitin"], default="tseitin")
    parser.add_argument("--n", type=int, required=True, help="Tseitin instance size (number of vertices, even).")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--conf-budget", type=int, default=100_000)
    parser.add_argument("--prop-budget", type=int, default=5_000_000)
    parser.add_argument("--global-seed", type=int, default=123456789)
    parser.add_argument("--out", type=str, default=None, help="Output receipt path (JSON).")
    args = parser.parse_args()

    start = time.time()
    started_at = iso_now()

    if args.benchmark == "tseitin":
        params = (args.n, args.seed, args.conf_budget, args.prop_budget, args.global_seed)
        result = run_single_experiment(params)
        if result is None:
            print(f"[ERROR] run_single_experiment returned None for params={params}")
            sys.exit(1)
    else:
        raise RuntimeError("Unsupported benchmark")

    end = time.time()
    ended_at = iso_now()
    wall_s = round(end - start, 6)

    blind = result.get("blind_results", {})
    sighted = result.get("sighted_results", {})

    # μ-bit ledger heuristic:
    # - sighted μ-bits: use rank_gap (small)
    # - blind μ-bits: use conflicts (proxy for information debt)
    try:
        blind_mu = int(blind.get("conflicts", 0)) if blind else None
    except Exception:
        blind_mu = None
    try:
        sighted_mu = int(sighted.get("rank_gap", 0)) if sighted else None
    except Exception:
        sighted_mu = None

    receipt = {
        "benchmark": args.benchmark,
        "n": args.n,
        "seed": args.seed,
        "started_at": started_at,
        "ended_at": ended_at,
        "wall_time_s": wall_s,
        "result": result,
        "mu_bits_ledger": {
            "blind": blind_mu,
            "sighted": sighted_mu
        },
        "environment": {
            "python_version": sys.version,
            "platform": platform.platform(),
        }
    }

    out_path = args.out or f"run_benchmark_receipt_n{args.n}_seed{args.seed}.json"

    def convert_np(obj):
        if isinstance(obj, dict):
            return {k: convert_np(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [convert_np(x) for x in obj]
        # numpy scalar types expose .item()
        elif hasattr(obj, "item") and not isinstance(obj, (str, bytes)):
            try:
                return obj.item()
            except Exception:
                return obj
        elif isinstance(obj, (int, float, str)) or obj is None:
            return obj
        else:
            # Fallback: try to coerce to int/float/string for JSON safety
            try:
                return int(obj)
            except Exception:
                try:
                    return float(obj)
                except Exception:
                    return str(obj)

    with open(out_path, "w") as f:
        json.dump(convert_np(receipt), f, indent=2, separators=(",", ": "))

    sha = sha256_file(out_path)
    print(f"[INFO] Receipt written: {out_path}")
    print(f"[INFO] SHA256: {sha}")
    # Also write a canonical single-line summary for quick parsing
    summary_path = out_path + ".summary.txt"
    with open(summary_path, "w") as f:
        f.write(json.dumps({
            "receipt": out_path,
            "sha256": sha,
            "benchmark": args.benchmark,
            "n": args.n,
            "seed": args.seed,
            "wall_time_s": wall_s
        }))
    print(f"[INFO] Summary: {summary_path}")

if __name__ == "__main__":
    main()