#!/usr/bin/env python3
# verifier/check_einstein.py
# Aggregate Einstein experiment CSVs and perform basic verifier checks.
#
# Expects CSV rows: seed,T,F,D_est,mu_mech_est,D_minus_mu_kT (D_minus_mu_kT optional)

import os
import glob
import csv
import json
import statistics

K_B = 1.0

def aggregate_results(base_dir="results/einstein"):
    rows = []
    for csv_path in glob.glob(os.path.join(base_dir, "T=*","seed=*.csv")):
        with open(csv_path, newline='') as f:
            r = csv.DictReader(f)
            for row in r:
                try:
                    D_est = float(row.get("D_est", 0.0))
                    mu_mech = float(row.get("mu_mech_est", 0.0))
                    T = float(row.get("T", 1.0))
                    # If D_minus_mu_kT provided, use it; otherwise compute D - mu*kT
                    if row.get("D_minus_mu_kT") is not None and row.get("D_minus_mu_kT") != "":
                        diff = float(row.get("D_minus_mu_kT"))
                    else:
                        diff = D_est - (mu_mech * T)
                    rows.append({
                        "seed": int(row.get("seed", 0)),
                        "T": T,
                        "F": float(row.get("F", 0.0)),
                        "D_est": D_est,
                        "mu_mech_est": mu_mech,
                        "D_minus_mu_kT": diff
                    })
                except Exception:
                    # skip malformed rows
                    continue
    return rows

def check_einstein(base_dir="results/einstein", delta=0.05):
    rows = aggregate_results(base_dir)
    by_T = {}
    for r in rows:
        by_T.setdefault(r["T"], []).append(r)
    verdicts = {}
    diagnostics = {}
    for T, recs in by_T.items():
        diffs = [abs(r["D_minus_mu_kT"]) for r in recs]
        mean_diff = statistics.mean(diffs) if diffs else 0.0
        std_diff = statistics.pstdev(diffs) if len(diffs) > 1 else 0.0
        passed = mean_diff <= delta
        verdicts[f"einstein@T={T}"] = passed
        diagnostics[f"einstein@T={T}"] = {"mean_diff": mean_diff, "std_diff": std_diff, "n": len(diffs)}
    out = {"verdicts": verdicts, "diagnostics": diagnostics}
    out_path = os.path.join("verifier", "einstein_verifier.json")
    os.makedirs("verifier", exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(out, f, indent=2)
    return out_path, out

if __name__ == "__main__":
    path, out = check_einstein()
    print("Wrote verifier:", path)
    print(out)