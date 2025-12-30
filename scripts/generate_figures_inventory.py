#!/usr/bin/env python3
"""Generate CSV inventory of figures and embedded TikZ in the thesis and repo.
Columns: id,figure_name,kind,location,source_available,recommended_action,notes
"""
from pathlib import Path
import re
import csv

REPO = Path(__file__).resolve().parents[1]
OUT = REPO / 'thesis' / 'figures' / 'inventory.csv'
tex_files = list((REPO / 'thesis').rglob('*.tex'))
image_exts = {'.png', '.svg', '.pdf', '.eps', '.jpg', '.jpeg', '.dot', '.gv'}
rows = []
_id = 1

# Scan tex files for tikzpicture blocks and includegraphics
for tex in sorted(tex_files):
    with tex.open('r', encoding='utf-8', errors='ignore') as f:
        for i, line in enumerate(f, start=1):
            if '\\begin{tikzpicture' in line:
                rows.append({
                    'id': _id,
                    'figure_name': tex.name + f"::tikz@{i}",
                    'kind': 'TikZ (embedded)',
                    'location': f'{tex.relative_to(REPO)}:{i}',
                    'source_available': 'yes',
                    'recommended_action': 'Extract to standalone .tex/.tikz using standalone class; apply unified style and crop with preview',
                    'notes': ''
                })
                _id += 1
            # includegraphics
            if '\\includegraphics' in line:
                m = re.search(r'\\includegraphics(?:\[.*?\])?\{([^}]+)\}', line)
                if m:
                    imgpath = m.group(1)
                    # resolve relative to tex parent
                    imgfile = (tex.parent / imgpath).with_suffix(Path(imgpath).suffix or '')
                    ext = Path(imgpath).suffix.lower()
                    kind = ext[1:].upper() if ext and ext in image_exts else 'Unknown'
                    recommended = ''
                    source_available = 'no'
                    notes = ''
                    # heuristics: if png -> try to find generating script
                    if ext == '.png':
                        recommended = 'Regenerate as vector (SVG/PDF) from original data or plotting script; preserve fonts and improve cropping'
                        # search for scripts mentioning the filename
                        for p in REPO.rglob('*.py'):
                            try:
                                txt = p.read_text()
                            except Exception:
                                continue
                            if Path(imgpath).name in txt:
                                source_available = 'yes (script: ' + str(p.relative_to(REPO)) + ')'
                                notes = 'found in script'
                                break
                    elif ext in {'.svg', '.pdf', '.eps'}:
                        recommended = 'Normalize styling and check padding; prefer using SVG for thesis figures'
                        source_available = 'yes (vector)'
                    else:
                        recommended = 'Review and convert to vector if raster; check source'
                    rows.append({
                        'id': _id,
                        'figure_name': Path(imgpath).name,
                        'kind': kind,
                        'location': f'{tex.relative_to(REPO)}:{i}',
                        'source_available': source_available,
                        'recommended_action': recommended,
                        'notes': notes
                    })
                    _id += 1

# Preload python files into memory to avoid repeated disk scans
py_files = list(REPO.rglob('*.py'))
py_texts = {}
for q in py_files:
    try:
        py_texts[q] = q.read_text()
    except Exception:
        py_texts[q] = ''

# Scan repo for image files and add those not referenced via includegraphics
for p in sorted(REPO.rglob('*')):
    if p.suffix.lower() in image_exts:
        rel = p.relative_to(REPO)
        # check if already recorded (by includegraphics in thesis)
        if any(r['figure_name'] == p.name and (r['location'].startswith('thesis') or r['location'].startswith('thesis/')) for r in rows):
            continue
        # try to find references to file in preloaded scripts
        source_available = 'no'
        for q, txt in py_texts.items():
            if p.name in txt:
                source_available = 'yes (script: ' + str(q.relative_to(REPO)) + ')'
                break
        kind = p.suffix.lower()[1:]
        recommended = 'If plot: regenerate as SVG; if diagram: normalize styling; ensure consistent padding'
        rows.append({
            'id': _id,
            'figure_name': p.name,
            'kind': kind,
            'location': str(rel),
            'source_available': source_available,
            'recommended_action': recommended,
            'notes': ''
        })
        _id += 1

# Write CSV
OUT.parent.mkdir(parents=True, exist_ok=True)
with OUT.open('w', newline='', encoding='utf-8') as csvfile:
    fieldnames = ['id','figure_name','kind','location','source_available','recommended_action','notes']
    writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
    writer.writeheader()
    for r in rows:
        writer.writerow(r)

print(f'Wrote {len(rows)} rows to {OUT}')
print('Summary: counts by kind:')
from collections import Counter
c = Counter(r['kind'] for r in rows)
for k,v in c.items():
    print(f'  {k}: {v}')
