#!/usr/bin/env python3
"""Verify the invariants that constitute this particular reading experiment."""
from collections import Counter
from pathlib import Path
import hashlib
import json

import fitz

HERE = Path(__file__).resolve().parent
receipt = json.loads((HERE/'construction.json').read_text())
pdf = HERE/'The-Thiele-Machine-The-Shape.pdf'
doc = fitz.open(pdf)
expected = Counter(c for c in receipt['source_paragraph'] if not c.isspace())
assert hashlib.sha256(pdf.read_bytes()).hexdigest() == receipt['pdf_sha256']
assert len(receipt['settings']) == 15
assert receipt['word_count'] == 314
assert len(doc) == 20
for setting in receipt['settings']:
    assert sorted(t['id'] for t in setting['words']) == list(range(314))
    page = doc[setting['page']-1]
    actual = Counter(c['c'] for b in page.get_text('rawdict')['blocks'] if 'lines' in b
                     for line in b['lines'] for span in line['spans'] for c in span['chars']
                     if not c['c'].isspace())
    assert actual == expected, setting['operation']
for page in doc:
    for block in page.get_text('dict')['blocks']:
        for line in block.get('lines', []):
            for span in line['spans']:
                assert page.rect.contains(fitz.Rect(span['bbox'])), span
first = doc[receipt['settings'][0]['page']-1].get_pixmap(matrix=fitz.Matrix(2,2))
last = doc[receipt['settings'][-1]['page']-1].get_pixmap(matrix=fitz.Matrix(2,2))
assert first.samples == last.samples
assert doc.metadata['author'] == 'Devon Thiele'
assert all(doc.extract_font(xref)[3] for xref in {f[0] for p in doc for f in p.get_fonts()})
result = {'pages':len(doc), 'settings':15, 'words_per_setting':314,
          'every_word_id_present_once':True, 'all_source_glyphs_in_each_pdf_setting':True,
          'first_and_last_setting_pixel_identical_at_144dpi':True,
          'text_within_page_bounds':True, 'fonts_embedded':True,
          'author':doc.metadata['author'], 'pdf_sha256':receipt['pdf_sha256'],
          'limitation':'These checks verify construction, not artistic success. One large white word is deliberately perceived through the gap in surrounding text.'}
(HERE/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
