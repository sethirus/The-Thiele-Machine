#!/usr/bin/env python3
# experiments/plot_utils.py
# Small plotting utilities for Landauer/Einstein/CWD experiment outputs.
#
# Usage examples:
#  from experiments.plot_utils import plot_landauer
#  plot_landauer("results/landauer", out_dir="plots/landauer")
#
import os
import glob
import csv
import math
import numpy as np
import matplotlib.pyplot as plt

K_B = 1.0
LN2 = math.log(2.0)

def ensure_dir(d):
    os.makedirs(d, exist_ok=True)

def read_landauer_results(base_dir):
    rows = []
    for path in sorted(glob.glob(os.path.join(base_dir, "T=*","seed=*.csv"))):
        with open(path, newline='') as f:
            r = csv.DictReader(f)
            for row in r:
                rows.append({
                    "seed": int(row["seed"]),
                    "T": float(row["T"]),
                    "trial_id": int(row["trial_id"]),
                    "sum_mu_bits": float(row["sum_mu_bits"]),
                    "work_over_kTln2": float(row["work_over_kTln2"]),
                    "protocol": row.get("protocol","")
                })
    return rows

def plot_landauer(base_dir, out_dir="plots/landauer"):
    rows = read_landauer_results(base_dir)
    if not rows:
        print("No landauer rows found in", base_dir); return
    ensure_dir(out_dir)
    by_T = {}
    for r in rows:
        by_T.setdefault(r["T"], []).append(r)
    for T, recs in by_T.items():
        x = [r["sum_mu_bits"] for r in recs]
        y = [r["work_over_kTln2"] for r in recs]
        plt.figure(figsize=(6,4))
        plt.scatter(x, y, alpha=0.7)
        mx = min(min(x), min(y)) - 0.1
        Mx = max(max(x), max(y)) + 0.1
        plt.plot([mx,Mx],[mx,Mx], color='k', linestyle='--', label=r'$y=x$')
        plt.xlabel("sum_mu_bits")
        plt.ylabel("work / (kT ln2)")
        plt.title(f"Landauer: T={T}")
        plt.legend()
        out = os.path.join(out_dir, f"landauer_T={T}.png")
        plt.tight_layout()
        plt.savefig(out, dpi=150)
        plt.close()
        print("Wrote plot:", out)

def plot_einstein(base_dir, out_dir="plots/einstein"):
    # Placeholder: read CSVs like results/einstein/T=*/seed=*.csv with fields D_est, mu_mech_est
    ensure_dir(out_dir)
    paths = sorted(glob.glob(os.path.join(base_dir, "T=*","seed=*.csv")))
    if not paths:
        print("No einstein results found in", base_dir); return
    # quick scatter of D_est vs mu_mech_est * kT
    D = []
    mu_kT = []
    for p in paths:
        with open(p, newline='') as f:
            r = csv.DictReader(f)
            for row in r:
                try:
                    D.append(float(row["D_est"]))
                    mu_kT.append(float(row["mu_mech_est"]) * float(row.get("T",1.0)) * K_B)
                except Exception:
                    continue
    if not D:
        print("No data points parsed for Einstein")
        return
    plt.figure(figsize=(6,4))
    plt.scatter(mu_kT, D, alpha=0.6)
    mn = min(min(mu_kT), min(D)) - 0.1
    mx = max(max(mu_kT), max(D)) + 0.1
    plt.plot([mn,mx],[mn,mx], '--', color='k', label=r'$D=\mu kT$')
    plt.xlabel(r'$\mu_{mech} kT$')
    plt.ylabel('D (est)')
    plt.title('Einstein test')
    plt.legend()
    out = os.path.join(out_dir, "einstein_scatter.png")
    plt.tight_layout()
    plt.savefig(out, dpi=150)
    plt.close()
    print("Wrote plot:", out)

def plot_cwd(base_dir, out_dir="plots/cwd"):
    # Placeholder: produce simple bar chart of W_sighted/(kT ln2) vs sum_mu_sighted
    ensure_dir(out_dir)
    paths = sorted(glob.glob(os.path.join(base_dir, "K=*","seed=*.csv")))
    if not paths:
        print("No cwd results found in", base_dir); return
    Ks = []
    ratios = []
    for p in paths:
        with open(p, newline='') as f:
            r = csv.DictReader(f)
            for row in r:
                try:
                    Ks.append(int(row.get("K",0)))
                    ratios.append(float(row.get("W_sighted",0.0)) / (K_B * float(row.get("T",1.0)) * LN2) - float(row.get("sum_mu_sighted",0.0)))
                except Exception:
                    continue
    if not Ks:
        print("No data for CWD plots"); return
    plt.figure(figsize=(6,4))
    plt.bar(range(len(ratios)), ratios)
    plt.xlabel("run")
    plt.ylabel(r'$W_{sighted}/(kT\ln2) - \sum \mu$')
    plt.title("CWD residuals")
    out = os.path.join(out_dir, "cwd_residuals.png")
    plt.tight_layout()
    plt.savefig(out, dpi=150)
    plt.close()
    print("Wrote plot:", out)