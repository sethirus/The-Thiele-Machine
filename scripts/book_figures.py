#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2025-2026 Devon Thiele
# SPDX-License-Identifier: CC-BY-SA-4.0
"""The book's images, generated from the book's own definitions.

An image appears only where a sentence of the book asks for one. Before the
essay's last sentence ("The rest of the book is me trying to break all of
it") an image is one case; after it, every case, with the ones that fail at
the same weight. Each image is set in the book's type, and each count it
shows is asserted here, so a wrong figure stops the build instead of being
printed.

    python3 scripts/book_figures.py            write monograph/figures/*.tex
    python3 scripts/book_figures.py --check    fail if a committed figure differs
"""
from __future__ import annotations

import argparse
import itertools
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from thiele_small import small as S  # noqa: E402

OUT = ROOT / "monograph" / "figures"


# ---------------------------------------------------------------- the chairs
# Four people: 1, 2, 3 sit inside, 4 by the door. One move sends each to a
# chair; nobody inside may leave, and the person by the door must come in, so
# each of the four goes to one of the three inside chairs.
INSIDE = (1, 2, 3)
MOVES = list(itertools.product(INSIDE, repeat=4))
STAY = (1, 2, 3, 1)  # the insiders keep their chairs; the newcomer takes chair 1
CW, CH = 14.1, 13.0  # cell width and height, mm


def _seats(move):
    return [''.join(str(p + 1) for p in range(4) if move[p] == c) for c in INSIDE]


def _chair_cell(move):
    return r'\chaircell{%s}{%s}{%s}' % tuple(_seats(move))


def chairs_one() -> str:
    return _chair_cell(STAY) + '\n'


def chairs_all() -> str:
    assert len(MOVES) == 81
    assert all(max(m.count(c) for c in INSIDE) >= 2 for m in MOVES)  # somebody shares
    out = [r'\begin{tikzpicture}[x=1mm,y=1mm]', r'\path (0,0) rectangle (%.1f,%.1f);' % (9 * CW, -9 * CH)]
    for m in MOVES:
        row = (m[0] - 1) * 3 + (m[1] - 1)  # where 1 and 2 go
        col = (m[2] - 1) * 3 + (m[3] - 1)  # where 3 and 4 go
        out.append(r'\node[inner sep=0pt] at (%.2f,%.2f) {%s};'
                   % (col * CW + CW / 2, -row * CH - CH / 2, _chair_cell(m)))
    out.append(r'\end{tikzpicture}')
    return '\n'.join(out) + '\n'


def reseat() -> str:
    """One person per chair, the door counted as a fourth chair: 4! ways. In
    the six that keep the insiders inside, the person by the door stays there."""
    perms = list(itertools.permutations((1, 2, 3, 4)))
    keep = [p for p in perms if all(p[i] != 4 for i in range(3))]
    assert len(perms) == 24 and len(keep) == 6 and all(p[3] == 4 for p in keep)
    order = keep + [p for p in perms if p not in keep]
    out = [r'\begin{tikzpicture}[x=1mm,y=1mm]']
    for k, p in enumerate(order):
        r, c = divmod(k, 6)
        s = [''.join(str(i + 1) for i in range(4) if p[i] == ch) for ch in (1, 2, 3, 4)]
        out.append(r'\node[inner sep=0pt] at (%.2f,%.2f) {\doorcell{%s}{%s}{%s}{%s}};'
                   % (c * 21.0 + 10.5, -r * 11.0 - 5.5, *s))
    out.append(r'\end{tikzpicture}')
    return '\n'.join(out) + '\n'


# ---------------------------------------------------------------- the piles
LISTS = list(itertools.product((1, 2, 3), repeat=3))
CHECKS = [
    lambda l: l[0] <= l[1] <= l[2],  # every number no bigger than the one after it
    lambda l: True,                  # a check that says yes to everything
    lambda l: l == (1, 2, 3),        # "this is that exact list"
]


def _show(l):
    return ' '.join(map(str, l))


def _piles(yes, no) -> str:
    cell = lambda items: r'\raggedright ' + r'\hspace{0pt}'.join(r'\pileitem{%s}' % x for x in items)
    return (r'\begin{tabular}{@{}p{58mm}@{\hspace{9mm}}p{58mm}@{}}' '\n'
            r'\pilehead{yes pile} & \pilehead{no pile}\\[3pt]' '\n'
            + cell(yes) + ' & ' + cell(no) + r'\tabularnewline' '\n' r'\end{tabular}')


def lists_one() -> str:
    return (r'\begin{tabular}{@{}l@{}}\pilehead{yes pile}\\[3pt]\pileitem{%s}\end{tabular}' % _show((1, 2, 3))) + '\n'


def lists_all() -> str:
    assert len(LISTS) == 27
    counts = [(sum(map(c, LISTS)), sum(not c(l) for l in LISTS)) for c in CHECKS]
    assert counts == [(10, 17), (27, 0), (1, 26)], counts
    bands = []
    for c in CHECKS:
        bands.append(_piles([_show(l) for l in LISTS if c(l)], [_show(l) for l in LISTS if not c(l)]))
    return (r'\begin{minipage}{125mm}' '\n' + ('\n' r'\par\vspace{9pt}\noindent' '\n').join(bands)
            + '\n' r'\end{minipage}' '\n')


# ---------------------------------------------------------------- the plans
def chsh_plans() -> str:
    """Sixteen plans (a0, a1, b0, b1). A round on questions x, y is won when
    the answers differ exactly when both questions were one."""
    wins = {}
    for plan in itertools.product((0, 1), repeat=4):
        a, b = plan[:2], plan[2:]
        wins[plan] = sum((a[x] != b[y]) == (x == 1 and y == 1) for x in (0, 1) for y in (0, 1))
    by = defaultdict(list)
    for plan, w in wins.items():
        by[w].append(''.join(map(str, plan)))
    assert len(wins) == 16 and len(by[3]) == 8 and len(by[1]) == 8 and not by[4]
    cols = []
    for w in (4, 3, 2, 1, 0):
        items = r'\\'.join(r'\pileitem{%s}' % p for p in by[w])
        cols.append(r'\begin{tabular}[t]{@{}l@{}}\pilehead{wins %d}\\[3pt]%s\end{tabular}' % (w, items))
    return r'\hspace*{\fill}'.join(cols) + '\n'


# ---------------------------------------------------------------- the programs
ALPHABET = [("INC", 0), ("DEC", 0, 0), ("HALT",), ("CHECK", ("PZero",), 0),
            ("COMMIT", ("PZero",), 0), ("CERTIFY",)]
NAME = {"INC": r'INC $A$', "DEC": r'DEC $A$ 0', "HALT": 'HALT', "CHECK": r'CHECK \emph{is zero} $A$',
        "COMMIT": r'COMMIT \emph{is zero} $A$', "CERTIFY": 'CERTIFY'}
PER_COLUMN = 72


def _runs():
    runs = []
    for n in (1, 2, 3):
        for prog in itertools.product(ALPHABET, repeat=n):
            runs.append((prog, S.run_prog(12, list(prog), S.start(0, 0))))
    assert len(runs) == 258
    up = [(p, k) for p, k in runs if k.cert]
    assert len(up) == 1 and [i[0] for i in up[0][0]] == ["CHECK", "COMMIT", "CERTIFY"] and up[0][1].mu == 3
    k = up[0][1]
    idle = (("DEC", 0, 0),) * 3
    assert any(p == idle and (j.pc, j.ca, j.cb) == (k.pc, k.ca, k.cb) == (4, 0, 0) for p, j in runs)
    return runs


def _order(prog):
    return (len(prog), [ALPHABET.index(i) for i in prog])


def _text(prog):
    return '; '.join(NAME[i[0]] for i in prog)


def _columns(blocks):
    cols, cur = [], []
    for head, lines in blocks:
        items = [('h', head)] + [('l', x) for x in lines]
        for it in items:
            if len(cur) + (2 if it[0] == 'h' else 1) > PER_COLUMN:
                cols.append(cur)
                cur = []
            cur.append(it)
        cur.append(('s', ''))
    cols.append(cur)
    assert len(cols) <= 4, len(cols)
    cols += [[]] * (4 - len(cols))
    tex = []
    for col in cols:
        rows = [r'\censushead{%s}' % x if k == 'h' else r'\censusline{%s}' % x if k == 'l' else r'\censusgap'
                for k, x in col]
        tex.append(r'\begin{minipage}[t]{\censuscol}' + '\n'.join(rows) + r'\end{minipage}')
    return tex


def census_window():
    """Every program, sorted by the only thing the window shows: line, A, B."""
    groups = defaultdict(list)
    for prog, k in _runs():
        groups[(k.pc, k.ca, k.cb)].append(prog)
    blocks = [(r'(%d, %d, %d)\hfill %d' % (*w, len(groups[w])), [_text(p) for p in sorted(groups[w], key=_order)])
              for w in sorted(groups, key=lambda w: (-len(groups[w]), w))]
    c = _columns(blocks)
    return c[0] + r'\hfill' + c[1] + '\n', c[2] + r'\hfill' + c[3] + '\n'


def census_record():
    """The same programs, sorted by the record: flag up, flag down, each with its ledger."""
    runs = _runs()
    up = [(p, k) for p, k in runs if k.cert]
    down = sorted([(p, k) for p, k in runs if not k.cert], key=lambda t: _order(t[0]))
    assert len(down) == 257
    blocks = [(r'flag up\hfill %d' % len(up), [_text(p) + r'\hfill %d' % k.mu for p, k in up]),
              (r'flag down\hfill %d' % len(down), [_text(p) + r'\hfill %d' % k.mu for p, k in down])]
    c = _columns(blocks)
    return c[0] + r'\hfill' + c[1] + '\n', c[2] + r'\hfill' + c[3] + '\n'


def figures() -> dict[str, str]:
    wl, wr = census_window()
    rl, rr = census_record()
    return {
        'chairs-one.tex': chairs_one(), 'chairs-all.tex': chairs_all(), 'reseat.tex': reseat(),
        'lists-one.tex': lists_one(), 'lists-all.tex': lists_all(), 'chsh-plans.tex': chsh_plans(),
        'window-L.tex': wl, 'window-R.tex': wr, 'record-L.tex': rl, 'record-R.tex': rr,
    }


HEADER = '% Generated by scripts/book_figures.py; do not edit.\n'


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    figs = {name: HEADER + body for name, body in figures().items()}
    if args.check:
        stale = [n for n, b in figs.items() if not (OUT / n).exists() or (OUT / n).read_text() != b]
        if stale:
            print('stale figures:', ', '.join(stale))
            return 1
        return 0
    OUT.mkdir(exist_ok=True)
    for name, body in figs.items():
        (OUT / name).write_text(body)
    print('wrote', len(figs), 'figures to', OUT.relative_to(ROOT))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
