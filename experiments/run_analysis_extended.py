#!/usr/bin/env python3
"""Extended analysis script: computes AIC/BIC, bootstrap CIs, residuals, and confidence bands."""
from pathlib import Path
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import curve_fit
import json

ROOT = Path(__file__).resolve().parents[1]
LAB = ROOT / 'experiments' / 'lab_notebook_template.csv'
OUT_JSON = ROOT / 'experiments' / 'analysis_report_extended.json'
OUT_DIR = ROOT / 'experiments'
OUT_DIR.mkdir(parents=True, exist_ok=True)

def poly_model(N, a, b):
    return a * (N ** b)

def exp_model(N, a, b):
    return a * np.exp(b * N)

def aic_bic(n, rss, k):
    aic = 2 * k + n * np.log(rss / n)
    bic = k * np.log(n) + n * np.log(rss / n)
    return aic, bic


def bootstrap_params(model, N, T, n_boot=500):
    params = []
    rng = np.random.default_rng(0)
    for _ in range(n_boot):
        idx = rng.choice(len(N), size=len(N), replace=True)
        try:
            popt, _ = curve_fit(model, N[idx], T[idx], maxfev=20000)
            params.append(popt)
        except Exception:
            continue
    return np.array(params)


df = pd.read_csv(LAB)
report = {}
for name, group in df.groupby('program_type'):
    N = group['instance_size'].values.astype(float)
    T = group['runtime_seconds'].values.astype(float)
    entry = {'n_points': len(N)}
    if len(N) < 3:
        entry['note'] = 'not enough points for robust analysis'
        report[name] = entry
        continue
    # fit
    try:
        popt_p, _ = curve_fit(poly_model, N, T, maxfev=20000)
        rss_p = np.sum((T - poly_model(N, *popt_p))**2)
        aic_p, bic_p = aic_bic(len(N), rss_p, k=2)
        entry['poly'] = {'a': float(popt_p[0]), 'b': float(popt_p[1]), 'rss': float(rss_p), 'aic': aic_p, 'bic': bic_p}
    except Exception as e:
        entry['poly'] = {'error': str(e)}
    try:
        popt_e, _ = curve_fit(exp_model, N, T, maxfev=20000)
        rss_e = np.sum((T - exp_model(N, *popt_e))**2)
        aic_e, bic_e = aic_bic(len(N), rss_e, k=2)
        entry['exp'] = {'a': float(popt_e[0]), 'b': float(popt_e[1]), 'rss': float(rss_e), 'aic': aic_e, 'bic': bic_e}
    except Exception as e:
        entry['exp'] = {'error': str(e)}

    # bootstrap for poly exponent
    if 'poly' in entry and 'error' not in entry['poly']:
        params = bootstrap_params(poly_model, N, T, n_boot=300)
        if params.size:
            b_vals = params[:,1]
            entry['poly']['bootstrap_b'] = {'median': float(np.median(b_vals)), 'ci_95': [float(np.percentile(b_vals, 2.5)), float(np.percentile(b_vals, 97.5))]}
            # confidence band: use percentiles of predictions
            Nf = np.linspace(min(N), max(N), 200)
            preds = []
            for p in params:
                preds.append(poly_model(Nf, *p))
            preds = np.array(preds)
            low = np.percentile(preds, 2.5, axis=0)
            high = np.percentile(preds, 97.5, axis=0)
            # save plot
            plt.figure()
            plt.scatter(N, T, label='data')
            plt.plot(Nf, poly_model(Nf, entry['poly']['a'], entry['poly']['b']), label='poly fit')
            plt.fill_between(Nf, low, high, color='gray', alpha=0.3, label='95% CI')
            plt.legend()
            plt.xlabel('N'); plt.ylabel('time (s)'); plt.title(f'Poly fit with CI - {name}')
            plt.savefig(OUT_DIR / f'plot_poly_ci_{name}.png')
            plt.close()

    # residual diagnostics
    try:
        if 'poly' in entry and 'error' not in entry['poly']:
            fitted = poly_model(N, entry['poly']['a'], entry['poly']['b'])
            res = T - fitted
            plt.figure()
            plt.scatter(fitted, res)
            plt.axhline(0, color='k', linestyle='--')
            plt.xlabel('Fitted'); plt.ylabel('Residual'); plt.title(f'Residuals (poly) - {name}')
            plt.savefig(OUT_DIR / f'residuals_poly_{name}.png')
            plt.close()
        if 'exp' in entry and 'error' not in entry['exp']:
            fitted = exp_model(N, entry['exp']['a'], entry['exp']['b'])
            res = T - fitted
            plt.figure()
            plt.scatter(fitted, res)
            plt.axhline(0, color='k', linestyle='--')
            plt.xlabel('Fitted'); plt.ylabel('Residual'); plt.title(f'Residuals (exp) - {name}')
            plt.savefig(OUT_DIR / f'residuals_exp_{name}.png')
            plt.close()
    except Exception:
        pass

    report[name] = entry

OUT_JSON.write_text(json.dumps(report, indent=2))
print('Extended analysis complete, report at', OUT_JSON)
