#!/usr/bin/env python3
# experiments/use_ledger_landauer.py
# Consume a vm ledger CSV (step,vm_mu,delta) and emit Landauer-style summaries
# compatible with the verifier CSV layout used by experiments/run_landauer.py.
#
# Usage:
#  python3 experiments/use_ledger_landauer.py --ledger path/to/trace.csv --T 1.0 --out results/landauer_from_ledger
#
# Output CSV rows: seed,T,trial_id,sum_mu_bits,work,work_over_kTln2,protocol

import os
import csv
import math
import argparse

K_B = 1.0
LN2 = math.log(2.0)

def ensure_dir(path):
    os.makedirs(path, exist_ok=True)

def read_ledger_csv(path):
    """
    Expect CSV with header containing at least: step,vm_mu,delta
    delta may be empty for first row; vm_mu should be numeric.
    Returns list of records as dicts.
    """
    records = []
    with open(path, newline='') as f:
        r = csv.DictReader(f)
        for row in r:
            # Normalise keys
            vm_mu = None
            delta = None
            if "vm_mu" in row and row["vm_mu"] != "":
                vm_mu = float(row["vm_mu"])
            elif "mu" in row and row["mu"] != "":
                vm_mu = float(row["mu"])
            if "delta" in row and row["delta"] != "":
                try:
                    delta = float(row["delta"])
                except Exception:
                    delta = None
            records.append({"vm_mu": vm_mu, "delta": delta})
    return records

def ledger_summary(records):
    """
    Compute sum_mu_bits := sum of delta entries (interpreted as bits).
    Compute work := final_vm_mu - initial_vm_mu (use vm_mu fields if present).
    If vm_mu fields missing, fall back to sum of deltas for work proxy.
    """
    deltas = [r["delta"] for r in records if r["delta"] is not None]
    sum_mu_bits = float(sum(deltas)) if deltas else 0.0
    vm_mus = [r["vm_mu"] for r in records if r["vm_mu"] is not None]
    if len(vm_mus) >= 2:
        work = float(vm_mus[-1] - vm_mus[0])
    else:
        # fallback: treat work as kT ln2 * sum_mu_bits (proxy)
        work = K_B * 1.0 * LN2 * sum_mu_bits
    return sum_mu_bits, work

def emit_summary_csv(ledger_path, T, seed, trial_id, out_dir, protocol="sighted"):
    records = read_ledger_csv(ledger_path)
    sum_mu_bits, work = ledger_summary(records)
    work_over_kTln2 = work / (K_B * T * LN2)
    ensure_dir(out_dir)
    out_path = os.path.join(out_dir, f"seed={seed}.csv")
    header = ["seed","T","trial_id","sum_mu_bits","work","work_over_kTln2","protocol"]
    # append single row or create file
    exists = os.path.exists(out_path)
    with open(out_path, "a", newline="") as f:
        w = csv.DictWriter(f, fieldnames=header)
        if not exists:
            w.writeheader()
        w.writerow({
            "seed": seed,
            "T": T,
            "trial_id": trial_id,
            "sum_mu_bits": float(sum_mu_bits),
            "work": float(work),
            "work_over_kTln2": float(work_over_kTln2),
            "protocol": protocol
        })
    return out_path

def main():
    parser = argparse.ArgumentParser(description="Use vm ledger CSV to produce Landauer summaries")
    parser.add_argument("--ledger", required=True, help="Path to ledger CSV (step,vm_mu,delta)")
    parser.add_argument("--T", type=float, default=1.0, help="Temperature")
    parser.add_argument("--seed", type=int, default=0, help="Seed id for output filename")
    parser.add_argument("--trial", type=int, default=0, help="Trial id")
    parser.add_argument("--out", default="results/landauer_from_ledger", help="Output base directory")
    parser.add_argument("--protocol", choices=["sighted","blind"], default="sighted")
    args = parser.parse_args()

    out_subdir = os.path.join(args.out, f"T={args.T}")
    out_file = emit_summary_csv(args.ledger, args.T, args.seed, args.trial, out_subdir, protocol=args.protocol)
    print("Wrote summary CSV:", out_file)

if __name__ == "__main__":
    main()