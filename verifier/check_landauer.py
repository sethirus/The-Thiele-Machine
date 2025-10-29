#!/usr/bin/env python3
# verifier/check_landauer.py
# Aggregates Landauer CSVs and applies verifier checks.

import os
import csv
import math
import glob
import json
import numpy as np

K_B = 1.0
LN2 = math.log(2.0)

def aggregate_results(base_dir="results/landauer"):
    rows = []
    for csv_path in glob.glob(os.path.join(base_dir, "T=*","seed=*.csv")):
        with open(csv_path, newline="") as f:
            r = csv.DictReader(f)
            for row in r:
                rows.append({
                    "seed": int(row["seed"]),
                    "T": float(row["T"]),
                    "trial_id": int(row["trial_id"]),
                    "sum_mu_bits": float(row["sum_mu_bits"]),
                    "work": float(row["work"]),
                    "work_over_kTln2": float(row["work_over_kTln2"]),
                    "protocol": row["protocol"]
                })
    return rows

def check_landauer(base_dir="results/landauer", eps=0.05):
    rows = aggregate_results(base_dir)
    by_protocol = {}
    for r in rows:
        key = (r["protocol"], r["T"])
        by_protocol.setdefault(key, []).append(r)
    verdicts = {}
    diagnostics = {}
    for (protocol, T), recs in by_protocol.items():
        diffs = [abs(r["work_over_kTln2"] - r["sum_mu_bits"]) for r in recs]
        mean_diff = float(np.mean(diffs))
        std_diff = float(np.std(diffs))
        passed = mean_diff <= eps
        verdicts[f"{protocol}@T={T}"] = passed
        diagnostics[f"{protocol}@T={T}"] = {"mean_diff": mean_diff, "std_diff": std_diff, "n": len(diffs)}
    out = {"verdicts": verdicts, "diagnostics": diagnostics}
    out_path = os.path.join("verifier", "landauer_verifier.json")
    os.makedirs("verifier", exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(out, f, indent=2)
    return out_path, out

if __name__ == "__main__":
    path, out = check_landauer()
    print("Wrote verifier:", path)
    print(out)