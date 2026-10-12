#!/usr/bin/env python3
"""A two-ended book composed from its own documented revisions.

Copyright 2026 Devon Thiele. CC-BY-SA-4.0.
No manuscript or release artifact is modified.
"""
from pathlib import Path
import difflib
import hashlib
import json
import re
import subprocess

import fitz

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE_PATH = 'monograph/monograph.tex'
RELEASE = 'e4c234627651f1b12eb649148a051d5a252ed6b4'
W, H = 540, 720
LEFT, RIGHT = 57, 489
TOP, BOTTOM = 102, 623
INK = (0.08, 0.07, 0.065)
RED = (0.56, 0.16, 0.115)
FONT_ROOT = Path('/usr/share/fonts/opentype/urw-base35')
FONT_PATHS = {'text': FONT_ROOT / 'P052-Roman.otf',
              'italic': FONT_ROOT / 'P052-Italic.otf',
              'display': FONT_ROOT / 'NimbusRoman-Regular.otf',
              'sans': FONT_ROOT / 'NimbusSans-Regular.otf'}
FONTS = {name: fitz.Font(fontfile=str(path)) for name, path in FONT_PATHS.items()}

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()

def source(revision):
    return git('show', f'{revision}:{SOURCE_PATH}')

CURRENT = source(RELEASE)
AUX = (ROOT / 'monograph/monograph.aux').read_text()
REFS = dict(re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]+)\}', AUX))

def paragraph(text, needle):
    hits = [p.strip() for p in re.split(r'\n\s*\n', text) if needle in p]
    assert len(hits) == 1, (needle, len(hits))
    return hits[0]

def plain(text):
    text = re.sub(r'\\ref\{([^}]+)\}', lambda m: REFS[m[1]], text)
    text = re.sub(r'\\(?:emph|textit|textbf|texttt|code)\{([^{}]*)\}', r'\1', text)
    text = text.replace('``', '“').replace("''", '”')
    text = text.replace('\\ge', '≥').replace('\\_', '_').replace('~', ' ')
    text = text.replace('$', '').replace('---', '—').replace('--', '–')
    text = re.sub(r'\s+', ' ', text).strip()
    assert '\\' not in text and '{' not in text and '}' not in text, text
    return text

def text(page, x, y, string, size=12, font='text', color=INK):
    page.insert_font(fontname=font, fontfile=str(FONT_PATHS[font]))
    page.insert_text((x, y), string, fontsize=size, fontname=font, color=color)

def measure(word, size, font='text'):
    return FONTS[font].text_length(word, fontsize=size)

def lines(s, width, size, font='text'):
    out, line = [], ''
    for word in s.split():
        candidate = (line + ' ' + word).strip()
        if measure(candidate, size, font) > width and line:
            out.append(line)
            line = word
        else:
            line = candidate
    if line:
        out.append(line)
    return out

def body(page, s, x=LEFT, y=TOP, width=RIGHT-LEFT, size=12, leading=17, font='text', color=INK):
    for line in lines(s, width, size, font):
        text(page, x, y, line, size, font, color)
        y += leading
    return y

def newpage(doc):
    return doc.new_page(width=W, height=H)

CASES = [
    ('The first shape', '39b6713d', 'Then I hit a wall, and it is the wall this whole document is about.', 22.5),
    ('What the record does', 'ce093c90', "It isn't more computing power.", 25.5),
    ('What a program cannot do', '5e131733', 'The second says that even if reading were free,', 31.5),
    ('What deserves a record', '8d79b656', 'Of all the events a machine could put on its meter,', 25.5),
]

def merged_tokens(old, current):
    a, b = old.split(), current.split()
    result = []
    for tag, i, j, k, l in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if tag == 'equal':
            result.extend({'word': w, 'old': True, 'current': True} for w in a[i:j])
        else:
            result.extend({'word': w, 'old': True, 'current': False} for w in a[i:j])
            result.extend({'word': w, 'old': False, 'current': True} for w in b[k:l])
    assert ' '.join(t['word'] for t in result if t['old']) == old
    assert ' '.join(t['word'] for t in result if t['current']) == current
    return result

def allocate(tokens, size):
    pages = [[]]
    x, y = LEFT, TOP
    for token in tokens:
        width = measure(token['word'], size)
        assert width < RIGHT - LEFT, token
        if x + width > RIGHT:
            x, y = LEFT, y + size * 1.42
        if y > BOTTOM:
            pages.append([])
            x, y = LEFT, TOP
        pages[-1].append({**token, 'x': x, 'y': y, 'size': size, 'width': width})
        x += width + measure(' ', size)
    return pages

def cover(page, direction):
    text(page, LEFT, 61, 'DEVON THIELE', 9, 'sans')
    text(page, LEFT - 3, 249, 'The', 83, 'display')
    text(page, LEFT - 6, 348, 'Thiele', 110, 'display')
    text(page, LEFT - 5, 446, 'Machine', 103, 'display')
    text(page, LEFT, 612, direction, 13, 'italic', RED)
    text(page, LEFT, 666, 'A BOOK IN TWO DIRECTIONS', 7.8, 'sans')

front, back = fitz.open(), fitz.open()
cover(newpage(front), 'What survives.')
cover(newpage(back), 'What it used to say.')

intro_front = newpage(front)
body(intro_front, 'Read from either end.', y=136, size=29, leading=36, font='display')
body(intro_front,
     'From this end, the words are from the released book. From the other, they are from four earlier versions of the same passages. Turn the volume over to enter the other reading.',
     y=252, width=345, size=13, leading=19)
body(intro_front,
     'Both readings use one setting of type. A word that belongs to only one version keeps its place in the other as an absence. Nothing moves in to cover it.',
     y=376, width=345, size=13, leading=19)
body(intro_front,
     'The earlier wording is historical material, not the book’s current claim. The small number at the foot takes you to the other face of the passage.',
     y=499, width=345, size=11, leading=16)
text(intro_front, LEFT, 665, 'READING PROOF · SELECTED PASSAGES · NOT A NEW EDITION', 7.4, 'sans', RED)

intro_back = newpage(back)
body(intro_back, 'This is what changed.', y=136, size=29, leading=36, font='display')
body(intro_back,
     'The words in this direction are earlier wording. They are printed here because the book changed them. Read from the other cover for the surviving passages.',
     y=252, width=345, size=13, leading=19)
body(intro_back,
     'The missing words are present at the other end. Their places are kept even on a page that would otherwise be empty. The revision has a volume.',
     y=376, width=345, size=13, leading=19)
body(intro_back,
     'All four comparisons come from the repository. They are excerpts, not a complete account of the book’s history. Source locations meet in the middle.',
     y=499, width=345, size=11, leading=16)
text(intro_back, LEFT, 665, 'EARLIER WORDING · READ AS HISTORICAL MATERIAL', 7.4, 'sans', RED)

opener = plain(paragraph(CURRENT, 'What I am is curious, past the point of good sense.'))
opener2 = plain(paragraph(CURRENT, 'I pick a thing up and cannot set it down'))
for doc in (front, back):
    p = newpage(doc)
    body(p, opener, y=199, width=395, size=31, leading=40, font='display')
    body(p, opener2, y=409, width=320, size=18, leading=26)
    text(p, LEFT, 665, 'HOW I GOT HERE', 7.8, 'sans', RED)

records = []
allocations = []
for number, (title, revision, needle, size) in enumerate(CASES, 1):
    parent = git('rev-parse', revision + '^')
    before_tex = paragraph(source(parent), needle)
    after_tex = paragraph(CURRENT, needle)
    before, after = plain(before_tex), plain(after_tex)
    tokens = merged_tokens(before, after)
    pages = allocate(tokens, size)
    start = len(front)
    for local, positions in enumerate(pages):
        for doc, which in ((front, 'current'), (back, 'old')):
            p = newpage(doc)
            if local == 0:
                text(p, LEFT, 47, title, 10.5, 'italic', RED)
            for token in positions:
                if token[which]:
                    text(p, token['x'], token['y'], token['word'], token['size'])
            text(p, LEFT, 666, 'CURRENT TEXT' if which == 'current' else 'EARLIER WORDING', 6.8, 'sans', RED)
            if not any(t[which] for t in positions):
                text(p, LEFT, 643, 'The words occupying this page are in the other reading.', 8, 'italic', RED)
        allocations.append({'case': number, 'page_index': len(front)-1, 'tokens': positions})
    records.append({'title': title, 'change': git('rev-parse', revision), 'earlier_revision': parent,
                    'current_revision': RELEASE, 'needle': needle,
                    'before_tex': before_tex, 'after_tex': after_tex,
                    'before': before, 'after': after, 'page_start': start + 1,
                    'page_count': len(pages),
                    'word_counts': {key: sum(t[key] for t in tokens) for key in ('old', 'current')},
                    'shared_words': sum(t['old'] and t['current'] for t in tokens),
                    'withdrawn_words': sum(t['old'] and not t['current'] for t in tokens),
                    'added_words': sum(t['current'] and not t['old'] for t in tokens)})

refusal = plain(paragraph(CURRENT, 'A word on what I actually do, because it runs under everything after it.'))
conclusion = plain(paragraph(CURRENT, "So that's the Thiele Machine. An abstract model with five parts and one rule,"))
for doc in (front, back):
    p = newpage(doc)
    text(p, LEFT, 53, 'How I got here', 10.5, 'italic', RED)
    body(p, refusal, y=117, width=365, size=13.5, leading=20)
    text(p, LEFT, 666, 'RELEASED TEXT · UNCHANGED IN THIS STUDY', 6.8, 'sans', RED)
    p = newpage(doc)
    body(p, conclusion, y=134, width=359, size=15, leading=23)
    text(p, LEFT, 666, 'CONCLUSION · RELEASED TEXT', 6.8, 'sans', RED)

assert len(front) == len(back)
SIDE = len(front)
TOTAL = SIDE * 2 + 2
for doc, which in ((front, 'current'), (back, 'old')):
    for i, p in enumerate(doc):
        if i < 3:
            continue
        physical = i + 1 if which == 'current' else TOTAL - i
        partner = TOTAL - i if which == 'current' else i + 1
        text(p, 425, 666, f'{physical:02d} / {partner:02d}', 8, 'sans')

middle = fitz.open()
p = newpage(middle)
text(p, LEFT, 62, 'The construction', 23, 'display')
body(p,
     'Each pair of passages is aligned word by word. Shared words occupy the same positions. A removed word appears only in the earlier reading; an added word appears only in the current reading. Both reserve the same amount of paper in both directions.',
     y=117, width=367, size=11.2, leading=16)
body(p,
     'The spaces are consequences of these actual edits. They do not measure the machine’s structural cost, the author’s labor, or a reader’s understanding. A displayed history is not a proof that a claim is true.',
     y=245, width=367, size=11.2, leading=16)
y = 381
for i, rec in enumerate(records, 1):
    text(p, LEFT, y, f'{i:02d}  {rec["title"]}', 11, 'text')
    text(p, LEFT, y+18, 'Change ' + rec['change'][:12] + ' · parent ' + rec['earlier_revision'][:12], 7.5, 'sans', RED)
    y += 49
text(p, LEFT, 643, 'Current text: v4.0.0 · ' + RELEASE[:12], 8, 'sans')
text(p, LEFT, 660, 'monograph/monograph.tex · sethirus/The-Thiele-Machine', 8, 'sans')
p = newpage(middle)
text(p, LEFT, 62, 'The object', 23, 'display')
body(p,
     'Devon Thiele is the author. The prose excerpts are taken from the manuscript. The short reading directions and this colophon belong to this design study; they are not additions to the released monograph.',
     y=117, width=367, size=11.2, leading=16)
body(p,
     'Section numbers are resolved against the released book. TeX emphasis becomes roman type and mathematical source notation becomes printed symbols. No claim is silently rewritten. The source bundle preserves both TeX passages, both readings, and every word’s position.',
     y=246, width=367, size=11.2, leading=16)
body(p,
     'One PDF; ordinary opaque paper. The second half is intentionally inverted and sequenced from the other cover. Duplex printing uses the long edge, at actual size. No transparency, cutting, special ink, animation, or external device supplies part of the reading.',
     y=391, width=367, size=11.2, leading=16)
body(p,
     'Reading proof, October 2026. CC-BY-SA-4.0. Fonts: URW Palladio and Nimbus Roman/Sans, embedded. This is an experiment in the book’s form, not the final design of the full monograph.',
     y=539, width=367, size=10, leading=14)

doc = fitz.open()
doc.insert_pdf(front)
doc.insert_pdf(middle, from_page=0, to_page=0)
page = newpage(doc)
page.show_pdf_page(page.rect, middle, 1, rotate=180)
for i in reversed(range(len(back))):
    page = newpage(doc)
    page.show_pdf_page(page.rect, back, i, rotate=180)
assert len(doc) == TOTAL and TOTAL % 2 == 0
doc.set_metadata({'title': 'The Thiele Machine — a book in two directions',
                  'author': 'Devon Thiele',
                  'subject': 'A reading proof constructed from the book’s own revisions',
                  'creator': 'The Thiele Machine book build'})
doc.set_toc([[1, 'What survives', 1], [1, 'The construction', SIDE+1],
             [1, 'What it used to say — turn the book over', TOTAL]])
doc.xref_set_key(doc.pdf_catalog(), 'PageLayout', '/TwoPageRight')
doc.xref_set_key(doc.pdf_catalog(), 'ViewerPreferences', '<</DisplayDocTitle true /Duplex /DuplexFlipLongEdge /PrintScaling /None>>')
out = HERE / 'The-Thiele-Machine-two-directions.pdf'
doc.save(out, garbage=4, deflate=True)
receipt = {'release': RELEASE, 'source_sha256': hashlib.sha256(CURRENT.encode()).hexdigest(),
           'pages': TOTAL, 'side_pages': SIDE, 'cases': records, 'allocations': allocations,
           'pdf_sha256': hashlib.sha256(out.read_bytes()).hexdigest(),
           'scope': 'A deterministic word alignment and typesetting construction, not a formal verification or a physical cost measurement.'}
(HERE / 'construction.json').write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
print(json.dumps({'output': str(out), 'pages': TOTAL, 'cases': [{k: r[k] for k in ['title', 'page_count', 'word_counts', 'withdrawn_words', 'added_words']} for r in records]}, indent=2))
