#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Devon Thiele
# SPDX-License-Identifier: CC-BY-SA-4.0
"""Verify a typography-only build with the complete document body untouched."""
from pathlib import Path
import hashlib
import json
import re
import fitz

ROOT = Path(__file__).resolve().parent
source = (ROOT.parent / "monograph.tex").read_text()
built = (ROOT / "build/book.tex").read_text()
original_body = source.split(r"\begin{document}", 1)[1]
assert built.split(r"\begin{document}", 1)[1] == original_body
assert not json.loads((ROOT / "construction.json").read_text())["composition_changes"]
doc = fitz.open(ROOT / "The-Thiele-Machine-book-design.pdf")
assert doc.metadata["author"] == "Devon Thiele"
log = (ROOT / "build/book.log").read_text(errors="replace")
assert "Missing character" not in log
assert not re.search(r"(?:Reference|Citation) .* undefined|There were undefined|Rerun to get", log)
labels = lambda p: dict(re.findall(r"\\newlabel\{([^}]+)\}\{\{([^{}]*)\}", p.read_text(errors="replace")))
original_labels = labels(ROOT.parent / "monograph.aux")
built_labels = labels(ROOT / "build/book.aux")
assert all(built_labels.get(k) == v for k, v in original_labels.items())
off_page = []
for n, page in enumerate(doc):
    for block in page.get_text("dict")["blocks"]:
        for line in block.get("lines", []):
            for span in line["spans"]:
                r = fitz.Rect(span["bbox"])
                if r.x0 < -1 or r.y0 < -1 or r.x1 > page.rect.width + 1 or r.y1 > page.rect.height + 1:
                    off_page.append([n + 1, span["text"]])
assert not off_page, off_page[:10]
report = {
    "pages": len(doc), "author": doc.metadata["author"],
    "complete_document_body_verbatim": True,
    "body_sha256": hashlib.sha256(original_body.encode()).hexdigest(),
    "content_interventions": [],
    "numbered_labels_preserved": len(original_labels),
    "off_page_text": off_page,
    "overfull_hboxes_pt": [float(x) for x in re.findall(r"Overfull \\hbox \(([\d.]+)pt", log)],
    "scope": "Typography-only working setting; no authored text, organization, or explicit breaks changed.",
}
(ROOT / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
