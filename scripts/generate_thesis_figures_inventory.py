#!/usr/bin/env python3
"""Generate CSV inventory of figures and embedded TikZ in the thesis folder.
Columns: id,figure_name,kind,location,source_available,recommended_action,notes
"""
from pathlib import Path
import re
import csv

REPO = Path(__file__).resolve().parents[1]
THESIS = REPO / 'thesis'
OUT = THESIS / 'figures' / 'inventory.csv'
tex_files = list(THESIS.rglob('*.tex'))
image_exts = {'.png', '.svg', '.pdf', '.eps', '.jpg', '.jpeg', '.dot', '.gv'}
rows = []
_id = 1

# Scan Tex files for tikzpicture blocks and includegraphics
for tex in sorted(tex_files):
    try:
        txt = tex.read_text()
    except Exception:
        continue
    for match in re.finditer(r"(?:\\begin\{tikzpicture\})|(?:\\includegraphics(?:\[.*?\])?\{([^}]+)\})", txt):
        span_start = txt.count('\n', 0, match.start()) + 1
        if match.group(0).startswith('\\begin'):
            rows.append({
                'id': _id,
                'figure_name': f'{tex.name}::tikz@{span_start}',
                'kind': 'TikZ (embedded)',
                'location': f'{tex.relative_to(REPO)}:{span_start}',
                'source_available': 'yes',
                'recommended_action': 'Extract to standalone .tex/.tikz using standalone class; apply unified style and crop with preview',
                'notes': ''
            })
            _id += 1
        else:
            imgpath = match.group(1)
            if not imgpath:
                continue
            img_name = Path(imgpath).name
            ext = Path(imgpath).suffix.lower()
            kind = ext[1:].upper() if ext and ext in image_exts else 'Unknown'
            recommended = ''
            source_available = 'no'
            notes = ''
            if ext == '.png':
                recommended = 'Regenerate as vector (SVG/PDF) from original data or plotting script; preserve fonts and improve cropping'
            elif ext in {'.svg', '.pdf', '.eps'}:
                recommended = 'Normalize styling and check padding; prefer using SVG for thesis figures'
                source_available = 'yes (vector)'
            else:
                recommended = 'Review and convert to vector if raster; check source'
            rows.append({
                'id': _id,
                'figure_name': img_name,
                'kind': kind,
                'location': f'{tex.relative_to(REPO)}:{span_start}',
                'source_available': source_available,
                'recommended_action': recommended,
                'notes': ''
            })
            _id += 1

# Scan thesis/figures for image files not referenced
fig_dir = THESIS / 'figures'
if fig_dir.exists():
    for p in sorted(fig_dir.iterdir()):
        if p.suffix.lower() in image_exts:
            if any(r['figure_name'] == p.name for r in rows):
                continue
            rows.append({
                'id': _id,
                'figure_name': p.name,
                'kind': p.suffix.lower()[1:],
                'location': str(p.relative_to(REPO)),
                'source_available': 'no',
                'recommended_action': 'If plot: regenerate as SVG; if diagram: normalize styling; ensure consistent padding',
                'notes': ''
            })
            _id += 1

OUT.parent.mkdir(parents=True, exist_ok=True)
with OUT.open('w', newline='', encoding='utf-8') as csvfile:
    fieldnames = ['id','figure_name','kind','location','source_available','recommended_action','notes']
    writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
    writer.writeheader()
    for r in rows:
        writer.writerow(r)

print(f'Wrote {len(rows)} rows to {OUT}')
from collections import Counter
c = Counter(r['kind'] for r in rows)
print('Summary: counts by kind:')
for k,v in c.items():
    print(f'  {k}: {v}')
