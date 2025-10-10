#!/usr/bin/env python3
"""Run the canonical analysis and produce a verification report (HTML + PNG)."""
from pathlib import Path
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import curve_fit
import json

ROOT = Path(__file__).resolve().parents[1]
LAB = ROOT / 'experiments' / 'lab_notebook_template.csv'
OUT = ROOT / 'experiments' / 'analysis_report.json'

print('Loading lab notebook:', LAB)
df = pd.read_csv(LAB)

# Fit models per group

def poly_model(N, a, b):
    return a * (N ** b)

def exp_model(N, a, b):
    return a * np.exp(b * N)

report = {}
for name, group in df.groupby('program_type'):
    N = group['instance_size'].values.astype(float)
    T = group['runtime_seconds'].values.astype(float)
    entry = {'n_points': len(N)}
    try:
        popt_p, _ = curve_fit(poly_model, N, T, maxfev=10000)
        entry['poly'] = {'a': float(popt_p[0]), 'b': float(popt_p[1])}
    except Exception as e:
        entry['poly'] = {'error': str(e)}
    try:
        popt_e, _ = curve_fit(exp_model, N, T, maxfev=10000)
        entry['exp'] = {'a': float(popt_e[0]), 'b': float(popt_e[1])}
    except Exception as e:
        entry['exp'] = {'error': str(e)}
    report[name] = entry

# Plot simple diagnostics
for name, group in df.groupby('program_type'):
    N = group['instance_size'].values.astype(float)
    T = group['runtime_seconds'].values.astype(float)
    plt.figure()
    plt.scatter(N, T)
    plt.xlabel('N')
    plt.ylabel('time (s)')
    plt.title(f'Scaling: {name}')
    plt.savefig(ROOT / f'experiments/plot_{name}.png')
    plt.close()

OUT.write_text(json.dumps(report, indent=2))
print('Analysis written to', OUT)
