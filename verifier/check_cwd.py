#!/usr/bin/env python3
# verifier/check_cwd.py
# Verifier for Compositional Work Decomposition (CWD) experiment outputs.
#
# Usage:
#   python verifier/check_cwd.py results/cwd --eps 0.05 --eta 0.05
#
# Writes JSON verdict to verifier/cwd_verifier.json by default.
#
# The verifier reads CSVs produced by experiments/run_cwd.py with header:
#   K,seed,T,sum_mu_sighted,W_sighted,W_blind,I_est,penalty
#
# For each row it checks:
#   |W_sighted/(kT ln2) - sum_mu_sighted| <= eps
#   W_blind - W_sighted >= kT ln2 * I_est - eta
#
# and records per-row verdicts and diagnostics.

import argparse
import csv
import glob
import json
import math
import os
from typing import List, Dict

K_B = 1.0
LN2 = math.log(2.0)


def _find_csvs(results_dir: str) -> List[str]:
    pattern = os.path.join(results_dir, "**", "*.csv")
    return sorted(glob.glob(pattern, recursive=True))


def _safe_float(d: Dict[str, str], keys: List[str], default: float = 0.0) -> float:
    for k in keys:
        if k in d and d[k] not in (None, ""):
            try:
                return float(d[k])
            except Exception:
                continue
    return default


def check_cwd(results_dir: str, eps: float = 0.05, eta: float = 0.05, out_json: str = "verifier/cwd_verifier.json"):
    """
    Scan CSVs under results_dir and check CWD verifier conditions.

    Produces a JSON file at out_json with structure:
    {
      "verdicts": [ { per-row verdict dicts ... } ],
      "diagnostics": { summary counts and list of failures ... }
    }
    """
    csv_files = _find_csvs(results_dir)
    os.makedirs(os.path.dirname(out_json) or ".", exist_ok=True)

    verdicts = []
    failures = []
    total_rows = 0

    for csv_path in csv_files:
        try:
            with open(csv_path, "r", encoding="utf-8", newline="") as f:
                reader = csv.DictReader(f)
                for row in reader:
                    if not row:
                        continue
                    total_rows += 1
                    # Extract fields with tolerant fallback names
                    K = int(_safe_float(row, ["K", "k"], default=0))
                    seed = int(_safe_float(row, ["seed"], default=0))
                    T = _safe_float(row, ["T", "temperature"], default=1.0)
                    sum_mu = _safe_float(row, ["sum_mu_sighted", "sum_mu", "sum_mu_bits"], default=0.0)
                    W_s = _safe_float(row, ["W_sighted", "W_s"], default=0.0)
                    W_b = _safe_float(row, ["W_blind", "W_b"], default=0.0)
                    I_est = _safe_float(row, ["I_est", "I", "I_module_policy_est"], default=0.0)

                    lhs = W_s / (K_B * T * LN2) if (K_B * T * LN2) != 0 else float("inf")
                    pass_sighted = abs(lhs - sum_mu) <= eps
                    pass_blind = (W_b - W_s) >= (K_B * T * LN2 * I_est) - eta

                    verdict = {
                        "file": csv_path,
                        "K": K,
                        "seed": seed,
                        "T": T,
                        "sum_mu_sighted": sum_mu,
                        "W_sighted": W_s,
                        "W_blind": W_b,
                        "I_est": I_est,
                        "lhs_Ws_over_kTln2": lhs,
                        "pass_sighted": bool(pass_sighted),
                        "pass_blind": bool(pass_blind),
                    }
                    verdicts.append(verdict)
                    if not (pass_sighted and pass_blind):
                        reason = []
                        if not pass_sighted:
                            reason.append(f"sighted_violation: |{lhs:.4f} - {sum_mu:.4f}| > eps({eps})")
                        if not pass_blind:
                            reason.append(f"blind_violation: W_blind - W_sighted = {W_b - W_s:.4f} < kTln2*I_est - eta = {(K_B * T * LN2 * I_est - eta):.4f}")
                        failures.append({"verdict": verdict, "reason": " ; ".join(reason)})
        except Exception as e:
            failures.append({"file": csv_path, "error": str(e)})

    diagnostics = {
        "results_dir": results_dir,
        "n_csv_files": len(csv_files),
        "total_rows": total_rows,
        "n_failures": len(failures),
    }

    out = {"verdicts": verdicts, "diagnostics": diagnostics, "failures": failures}
    with open(out_json, "w", encoding="utf-8") as jf:
        json.dump(out, jf, indent=2)

    return out_json, out


def _write_example_summary(results_dir: str):
    """Write a tiny example CWD summary CSV for smoke checks."""
    out_subdir = os.path.join(results_dir, "K=4")
    os.makedirs(out_subdir, exist_ok=True)
    csv_path = os.path.join(out_subdir, "seed=0.csv")
    header = ["K", "seed", "T", "sum_mu_sighted", "W_sighted", "W_blind", "I_est", "penalty"]
    # Build a self-consistent toy row: sum_mu = 2.0, W_sighted = kT ln2 * 2.0, W_blind = W_sighted + kT ln2 * 0.1
    T = 1.0
    sum_mu = 2.0
    W_s = K_B * T * LN2 * sum_mu
    I_est = 0.1
    W_b = W_s + K_B * T * LN2 * I_est
    penalty = (W_b - W_s) / (K_B * T * LN2)
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=header)
        w.writeheader()
        w.writerow({
            "K": 4,
            "seed": 0,
            "T": T,
            "sum_mu_sighted": float(sum_mu),
            "W_sighted": float(W_s),
            "W_blind": float(W_b),
            "I_est": float(I_est),
            "penalty": float(penalty)
        })
    return csv_path


def main():
    parser = argparse.ArgumentParser(description="CWD verifier: check summaries produced by experiments/run_cwd.py")
    parser.add_argument("results_dir", help="Directory containing CWD CSV summaries (e.g. results/cwd)")
    parser.add_argument("--eps", type=float, default=0.05, help="Tolerance for sighted work check")
    parser.add_argument("--eta", type=float, default=0.05, help="Tolerance for blind penalty check")
    parser.add_argument("--out", type=str, default="verifier/cwd_verifier.json", help="Path to write verifier JSON")
    parser.add_argument("--dry-run", action="store_true", help="Create a tiny example summary in results_dir and run the verifier")
    args = parser.parse_args()

    if args.dry_run:
        example = _write_example_summary(args.results_dir)
        print("Wrote example CWD summary for smoke check:", example)

    out_json_path, _ = check_cwd(args.results_dir, eps=args.eps, eta=args.eta, out_json=args.out)
    print("Wrote verifier JSON:", out_json_path)


if __name__ == "__main__":
    main()