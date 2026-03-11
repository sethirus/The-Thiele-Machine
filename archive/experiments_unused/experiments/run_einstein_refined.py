#!/usr/bin/env python3
# experiments/run_einstein_refined.py
# Refined Einstein runner with median-of-means estimators for robustness.

import os
import csv
import math
import argparse
import numpy as np

def ensure_dir(path):
    os.makedirs(path, exist_ok=True)

def median_of_means_slope(t, y, k=5):
    """
    Split (t,y) into k contiguous blocks, fit slope in each block via least-squares,
    and return median slope and median intercept.
    """
    t = np.array(t, dtype=float)
    y = np.array(y, dtype=float)
    n = t.size
    if n < 2:
        return 0.0, 0.0
    k = max(1, min(k, n))
    block_size = n // k
    slopes = []
    intercepts = []
    for i in range(k):
        start = i * block_size
        end = (i + 1) * block_size if i < k - 1 else n
        if end - start < 2:
            continue
        t_blk = t[start:end]
        y_blk = y[start:end]
        A = np.vstack([t_blk, np.ones_like(t_blk)]).T
        a, b = np.linalg.lstsq(A, y_blk, rcond=None)[0]
        slopes.append(a)
        intercepts.append(b)
    if len(slopes) == 0:
        return 0.0, 0.0
    a_med = float(np.median(np.array(slopes)))
    b_med = float(np.median(np.array(intercepts)))
    return a_med, b_med
 
def robust_huber_slope(t, y, max_iter=50, tol=1e-6, delta=1.0):
    """
    Compute slope and intercept using Huber-weighted least squares solved by IRLS.
    Returns (slope, intercept).
    """
    t = np.array(t, dtype=float)
    y = np.array(y, dtype=float)
    n = t.size
    if n < 2:
        return 0.0, 0.0
    A = np.vstack([t, np.ones_like(t)]).T
    # initial LS solution
    sol = np.linalg.lstsq(A, y, rcond=None)[0]
    slope, intercept = float(sol[0]), float(sol[1])
    for _ in range(max_iter):
        pred = slope * t + intercept
        resid = y - pred
        # Huber weights
        w = np.ones_like(resid)
        absr = np.abs(resid)
        mask = absr > delta
        w[mask] = delta / absr[mask]
        W = np.diag(w)
        # weighted LS
        try:
            sol_w = np.linalg.lstsq(W.dot(A), W.dot(y), rcond=None)[0]
        except Exception:
            break
        new_slope, new_intercept = float(sol_w[0]), float(sol_w[1])
        if abs(new_slope - slope) < tol and abs(new_intercept - intercept) < tol:
            slope, intercept = new_slope, new_intercept
            break
        slope, intercept = new_slope, new_intercept
    return slope, intercept
 
def combined_robust_slope(t, y, k_blocks=5):
    """
    Combine median-of-means and Huber: prefer Huber result if stable, else median-of-means.
    """
    # try huber
    try:
        s_h, b_h = robust_huber_slope(t, y, max_iter=30, delta=1.0)
        # quick stability check: compute residual_std
        pred = s_h * np.array(t, dtype=float) + b_h
        resid = np.array(y, dtype=float) - pred
        if np.std(resid) < 1e6:  # trivial sanity
            return float(s_h), float(b_h)
    except Exception:
        pass
    # fallback to median-of-means
    return median_of_means_slope(t, y, k=k_blocks)
 
def simulate_walkers(seed, T, F, n_walkers=1000, steps=1000, dt=1.0, rng=None):
    if rng is None:
        rng = np.random.default_rng(seed)
    D = 1.0 * T
    sigma = math.sqrt(2.0 * D * dt)
    mu = F * dt
    positions = np.zeros((n_walkers,), dtype=float)
    msd = []
    mean_disp = []
    times = []
    for t in range(1, steps + 1):
        steps_dx = rng.normal(loc=mu, scale=sigma, size=n_walkers)
        positions += steps_dx
        if t % max(1, steps // 100) == 0 or t == steps:
            times.append(t*dt)
            diffs = positions
            msd.append(float(np.mean(diffs*diffs)))
            mean_disp.append(float(np.mean(diffs)))
    return times, msd, mean_disp
 
def estimate_D_from_msd_mom(times, msd, k=5):
    s, b = combined_robust_slope(times, msd, k_blocks=k)
    D_est = float(s / 2.0)
    return D_est, s, b
 
def estimate_mu_from_drift_mom(times, mean_disp, F, k=5):
    if abs(F) < 1e-12:
        return 0.0, 0.0
    s, b = combined_robust_slope(times, mean_disp, k_blocks=k)
    mu = float(s / float(F))
    return mu, b

def read_ledger_and_sum_mu(path_or_stream):
    import csv as _csv
    close_file = False
    if isinstance(path_or_stream, str):
        f = open(path_or_stream, "r", encoding="utf-8", newline="")
        close_file = True
    else:
        f = path_or_stream
    total = 0.0
    try:
        reader = _csv.DictReader(f)
        for row in reader:
            if not row:
                continue
            for key in ("vm_mu_bits", "mu_bits", "vm_mu", "mu"):
                if key in row and row[key] not in (None, ""):
                    try:
                        total += float(row[key])
                    except Exception:
                        pass
                    break
    except Exception:
        if hasattr(f, "__iter__"):
            for line in f:
                parts = line.strip().split()
                if len(parts) >= 3:
                    try:
                        total += float(parts[2])
                    except Exception:
                        pass
    if close_file:
        f.close()
    return total

def run_trials_refined(seed, T, F, trials, n_walkers=1000, steps=1000, out_dir="results/einstein_refined", use_ledger=False, ledger_path=None, k_blocks=5):
    rng = np.random.default_rng(seed)
    out_subdir = os.path.join(out_dir, f"T={T}")
    ensure_dir(out_subdir)
    csv_path = os.path.join(out_subdir, f"seed={seed}.csv")
    summary = {"seed": seed, "T": T, "F": F, "n_trials": trials, "n_walkers": n_walkers, "steps": steps}
    D_vals = []
    mu_vals = []
    Dminus_vals = []
    with open(csv_path, "w", newline="") as f:
        fieldnames = ["seed","T","F","trial_id","sum_mu_bits","D_est","mu_mech_est","D_minus_mu_kT"]
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        if use_ledger:
            if not ledger_path:
                raise SystemExit("When use_ledger is True you must provide ledger_path")
            sum_mu_bits = read_ledger_and_sum_mu(ledger_path)
        else:
            sum_mu_bits = 0.0
        for t in range(trials):
            times, msd, mean_disp = simulate_walkers(seed + t, T, F, n_walkers=n_walkers, steps=steps, rng=np.random.default_rng(seed + t))
            D_est, slope, intercept = estimate_D_from_msd_mom(times, msd, k=k_blocks)
            mu_est, mu_intercept = estimate_mu_from_drift_mom(times, mean_disp, F, k=k_blocks)
            D_minus_mu_kT = D_est - (mu_est * T)
            D_vals.append(float(D_est))
            mu_vals.append(float(mu_est))
            Dminus_vals.append(float(D_minus_mu_kT))
            writer.writerow({
                "seed": seed,
                "T": T,
                "F": F,
                "trial_id": t,
                "sum_mu_bits": float(sum_mu_bits),
                "D_est": float(D_est),
                "mu_mech_est": float(mu_est),
                "D_minus_mu_kT": float(D_minus_mu_kT)
            })
    # robust aggregated summaries (median, MAD)
    import json, statistics
    def mad(arr):
        m = float(statistics.median(arr))
        return float(statistics.median([abs(x - m) for x in arr])) if arr else 0.0
    summary["D_median"] = float(statistics.median(D_vals)) if D_vals else 0.0
    summary["D_mad"] = mad(D_vals)
    summary["mu_median"] = float(statistics.median(mu_vals)) if mu_vals else 0.0
    summary["mu_mad"] = mad(mu_vals)
    summary["Dminus_median"] = float(statistics.median(Dminus_vals)) if Dminus_vals else 0.0
    summary["Dminus_mad"] = mad(Dminus_vals)
    summary_path = os.path.join(out_subdir, f"seed={seed}_summary.json")
    with open(summary_path, "w", encoding='utf-8') as sf:
        json.dump(summary, sf, indent=2)
    return csv_path

def main():
    parser = argparse.ArgumentParser(description="Refined Einstein runner with median-of-means estimators.")
    parser.add_argument("--seeds", nargs="+", type=int, default=[0], help="List of seeds to run")
    parser.add_argument("--T", type=float, default=1.0, help="Temperature")
    parser.add_argument("--F", type=float, default=0.01, help="Bias force")
    parser.add_argument("--trials", type=int, default=10, help="Trials per seed")
    parser.add_argument("--n_walkers", type=int, default=1000)
    parser.add_argument("--steps", type=int, default=1000)
    parser.add_argument("--out", default="results/einstein_refined", help="Output base directory")
    parser.add_argument("--use-ledger", action="store_true", dest="use_ledger", help="Read Σμ from ledger CSV")
    parser.add_argument("--ledger-path", type=str, default=None, help="Path to ledger CSV")
    parser.add_argument("--k-blocks", type=int, default=5, help="Number of blocks for median-of-means slope")
    parser.add_argument("--dry-run", action="store_true", help="Create a tiny example CSV and exit")
    args = parser.parse_args()

    created = []
    for seed in args.seeds:
        if args.dry_run:
            ensure_dir(os.path.join(args.out, f"T={args.T}"))
            run_trials_refined(seed, args.T, args.F, 1, n_walkers=10, steps=10, out_dir=args.out, use_ledger=False, k_blocks=args.k_blocks)
            created.append(os.path.join(args.out, f"T={args.T}", f"seed={seed}.csv"))
            continue
        csv_path = run_trials_refined(seed, args.T, args.F, args.trials, n_walkers=args.n_walkers, steps=args.steps, out_dir=args.out, use_ledger=args.use_ledger, ledger_path=args.ledger_path, k_blocks=args.k_blocks)
        created.append(csv_path)
    print("Created CSVs:")
    for p in created:
        print(f"- {p}")

if __name__ == "__main__":
    main()