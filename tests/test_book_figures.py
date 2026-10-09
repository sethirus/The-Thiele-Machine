# SPDX-FileCopyrightText: 2025-2026 Devon Thiele
# SPDX-License-Identifier: CC-BY-SA-4.0
"""The book's images are generated, current, and placed where the text asks.

Each image in monograph/figures/ is written by scripts/book_figures.py from
the book's own definitions, and the generator asserts every count it prints.
These tests rerun it, compare with the committed files, and check that the
book places each image after the sentence that commissions it: one case before
the essay's last sentence, every case after it.
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BOOK = ROOT / "monograph" / "monograph.tex"
sys.path.insert(0, str(ROOT / "scripts"))

import book_figures  # noqa: E402

PLACEMENT = re.compile(r"\\(pointfigure|wholefigure|wholepage|censusspread)\{([^}]*)\}")
HINGE = "The rest of the book is me trying to break all of it."


def test_committed_figures_match_the_generator() -> None:
    result = subprocess.run([sys.executable, str(ROOT / "scripts" / "book_figures.py"), "--check"],
                            capture_output=True, text=True)
    assert result.returncode == 0, result.stdout + result.stderr


def test_counts_shown_in_the_figures() -> None:
    lists = book_figures.LISTS
    assert len(lists) == 27
    assert [sum(map(c, lists)) for c in book_figures.CHECKS] == [10, 27, 1]
    assert len(book_figures.MOVES) == 81
    runs = book_figures._runs()
    assert sum(k.cert for _, k in runs) == 1
    assert sum(1 for _, k in runs if (k.pc, k.ca, k.cb) == (4, 0, 0)) == 15


def test_points_before_the_essays_last_sentence_wholes_after() -> None:
    text = BOOK.read_text(encoding="utf-8")
    hinge = text.index(HINGE)
    placed = [(m.start(), m.group(1), m.group(2)) for m in PLACEMENT.finditer(text)
              if not text[:m.start()].rstrip().endswith("newcommand{")]
    body = [p for p in placed if p[0] > text.index(r"\begin{document}")]
    assert body, "no images placed"
    for pos, kind, name in body:
        if kind == "pointfigure":
            assert pos < hinge, name
        else:
            assert pos > hinge, name
        stems = [f"{name}-L", f"{name}-R"] if kind == "censusspread" else [name]
        for stem in stems:
            assert (ROOT / "monograph" / "figures" / f"{stem}.tex").exists(), stem
