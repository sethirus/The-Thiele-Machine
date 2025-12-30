#!/usr/bin/env python3
"""Extract a TikZ picture from a TeX file and compile it to SVG using pdflatex+dvisvgm.
Usage: render_tikz_to_svg.py <tex-file> <occurrence-index> <out-svg>
occurrence-index is 1-based index of the \begin{tikzpicture} to extract.
"""
from pathlib import Path
import sys
import re
import subprocess

if len(sys.argv) < 4:
    print("Usage: render_tikz_to_svg.py <tex-file> <occurrence-index> <out-svg>")
    sys.exit(2)

tex_file = Path(sys.argv[1])
occ_idx = int(sys.argv[2])
out_svg = Path(sys.argv[3])
work_dir = out_svg.parent
work_dir.mkdir(parents=True, exist_ok=True)

text = tex_file.read_text(encoding='utf-8')
# Find tikzpicture blocks
pattern = r"\\begin\{tikzpicture\}.*?\\end\{tikzpicture\}"
matches = list(re.finditer(pattern, text, re.DOTALL))
if not matches:
    print("No tikzpicture blocks found in", tex_file)
    sys.exit(1)
if occ_idx <= 0 or occ_idx > len(matches):
    print(f"Occurrence index {occ_idx} out of range (1..{len(matches)})")
    sys.exit(1)
block = matches[occ_idx-1].group(0)

# Build standalone tex
standalone_tex = work_dir / (out_svg.stem + '.tex')
standalone_pdf = work_dir / (out_svg.stem + '.pdf')
standalone_log = work_dir / (out_svg.stem + '.log')

preamble = r"""
\documentclass[tikz,border=2pt]{standalone}
\usepackage{amsmath,amssymb}
\usepackage{xcolor}
\usetikzlibrary{shapes,arrows.meta,positioning,calc}
\begin{document}
"""
postamble = r"""
\end{document}
"""

standalone_tex.write_text(preamble + '\n' + block + '\n' + postamble, encoding='utf-8')
print('Wrote standalone tex to', standalone_tex)

# Run pdflatex
cmd = ['pdflatex', '-interaction=nonstopmode', '-halt-on-error', '-output-directory', str(work_dir), str(standalone_tex)]
print('Running:', ' '.join(cmd))
res = subprocess.run(cmd, capture_output=True, text=True)
if res.returncode != 0:
    print('pdflatex failed')
    print(res.stdout)
    print(res.stderr)
    print('LaTeX log:')
    try:
        print(standalone_log.read_text())
    except Exception:
        pass
    sys.exit(1)

# Convert pdf to svg using dvisvgm
if not standalone_pdf.exists():
    print('Expected pdf', standalone_pdf, 'not found')
    sys.exit(1)

# Use dvisvgm without --no-fonts so text remains text (selectable) and fonts are embedded when possible
cmd2 = ['dvisvgm', '--pdf', '-o', str(out_svg), str(standalone_pdf)]
print('Running:', ' '.join(cmd2))
res2 = subprocess.run(cmd2, capture_output=True, text=True)
if res2.returncode != 0:
    print('dvisvgm failed')
    print(res2.stdout)
    print(res2.stderr)
    sys.exit(1)

print('Wrote SVG to', out_svg)
