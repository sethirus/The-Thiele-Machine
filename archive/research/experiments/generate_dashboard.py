#!/usr/bin/env python3
"""Generate a simple static dashboard (HTML) summarizing analysis plots and status."""
from pathlib import Path
import json
ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / 'experiments' / 'analysis_report_extended.json'
OUT_HTML = ROOT / 'experiments' / 'dashboard.html'

report = {}
if REPORT.exists():
    report = json.loads(REPORT.read_text(encoding='utf-8'))

plots = list((ROOT / 'experiments').glob('plot_*.png')) + list((ROOT / 'experiments').glob('plot_poly_ci_*.png'))
residuals = list((ROOT / 'experiments').glob('residuals_*.png'))

html = ['<html><head><meta charset="utf-8"><title>Thiele Analysis Dashboard</title></head><body>']
html.append('<h1>Thiele Machine Verification Dashboard</h1>')
html.append('<h2>Model Summaries</h2>')
html.append('<pre>' + json.dumps(report, indent=2) + '</pre>')
html.append('<h2>Plots</h2>')
for p in plots:
    html.append(f'<div><h3>{p.name}</h3><img src="{p.name}" style="max-width:800px"></div>')
for r in residuals:
    html.append(f'<div><h3>{r.name}</h3><img src="{r.name}" style="max-width:800px"></div>')

html.append('</body></html>')
OUT_HTML.write_text('\n'.join(html), encoding='utf-8')
print('Dashboard written to', OUT_HTML)
