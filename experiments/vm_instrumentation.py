#!/usr/bin/env python3
# experiments/vm_instrumentation.py
# Thin CLI wrapper that produces per-step ledger CSVs using the reference VM.
#
# Usage:
#  python3 experiments/vm_instrumentation.py --seed 0 --fuel 20 --trace_len 50 --out logs/run0.csv
#
import argparse
import os
from experiments.vm_reference import run_reference

def ensure_dir(path):
    d = os.path.dirname(path) or "."
    os.makedirs(d, exist_ok=True)

def main():
    parser = argparse.ArgumentParser(description="VM instrumentation wrapper: emit per-step ledger CSVs.")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--fuel", type=int, default=20)
    parser.add_argument("--trace_len", type=int, default=50)
    parser.add_argument("--out", type=str, default="logs/run0.csv")
    parser.add_argument("--initial_mu", type=float, default=0.0)
    parser.add_argument("--max_cost_bits", type=int, default=3)
    args = parser.parse_args()

    ensure_dir(args.out)
    out = run_reference(args.seed, args.fuel, args.trace_len, args.out, args.initial_mu, args.max_cost_bits)
    print("Wrote VM ledger CSV:", out)

if __name__ == "__main__":
    main()