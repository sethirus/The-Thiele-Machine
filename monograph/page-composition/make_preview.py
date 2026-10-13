#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Devon Thiele
# SPDX-License-Identifier: CC-BY-SA-4.0
"""Show actual adjacent pages, without rearranging anything on them."""
from pathlib import Path
import json, shutil
import fitz
ROOT = Path(__file__).resolve().parent
OUT = Path('/workspace/book-design-review/page-composition')
OUT.mkdir(parents=True, exist_ok=True)
doc = fitz.open(ROOT / 'The-Thiele-Machine-book-design.pdf')
toc = doc.get_toc()
def heading(name):
    return next(t[2] for t in toc if t[1] == name)
def contains(text, first=1):
    for n in range(first, len(doc)+1):
        if text in ' '.join(doc[n-1].get_text().split()).replace('’', "'"):
            return n
    raise ValueError(text)
def left(n):
    return n if n % 2 == 0 else n-1
origin = heading('How I got here')
proof = contains('A raised flag was checked, then committed, then certified', heading('The smallest honest machine'))
starts = [
    ('Opening', left(contains('Put two computers on a table.'))),
    ('How I got here', left(origin)),
    ('The personal account continued', left(contains('Large language models were my hands', origin))),
    ('The formal argument', left(proof)),
    ('Challenges', left(heading('How to break this'))),
    ('Conclusion', left(contains("Now there's you.", heading('Conclusion')))),
]
spreads = fitz.open()
singles = fitz.open()
report = []
w,h = doc[0].rect.width, doc[0].rect.height
for title, start in starts:
    p = spreads.new_page(width=2*w, height=h)
    for side in range(2):
        p.show_pdf_page(fitz.Rect(side*w, 0, (side+1)*w, h), doc, start-1+side)
    p.get_pixmap(matrix=fitz.Matrix(1.4,1.4)).save(OUT / f'spread-{len(spreads)}.png')
    singles.insert_pdf(doc, from_page=start-1, to_page=start, links=False)
    report.append({'title':title,'source_pdf_pages':[start,start+1]})
spreads.set_metadata({'title':'The Thiele Machine — six page-design spreads', 'author':'Devon Thiele'})
spreads.set_toc([[1,title,n+1] for n,(title,_) in enumerate(starts)])
spreads.save(OUT / 'The-Thiele-Machine-six-spreads.pdf', garbage=4, deflate=True)
singles.set_metadata({'title':'The Thiele Machine — page-design sample', 'author':'Devon Thiele'})
singles.set_pagelayout('TwoPageLeft')
singles.set_toc([[1,title,2*n+1] for n,(title,_) in enumerate(starts)])
singles.save(OUT / 'The-Thiele-Machine-page-sample.pdf', garbage=4, deflate=True)
# The sample is a literal extraction, checked after saving.
saved = fitz.open(OUT / 'The-Thiele-Machine-page-sample.pdf')
for n,(_,start) in enumerate(starts):
    for side in range(2):
        assert saved[2*n+side].get_pixmap().samples == doc[start-1+side].get_pixmap().samples
shutil.copyfile(ROOT / 'The-Thiele-Machine-book-design.pdf', OUT / 'The-Thiele-Machine-page-design.pdf')
shutil.copyfile(ROOT / 'verification.json', OUT / 'verification.json')
(OUT / 'selected-pages.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report, indent=2))
