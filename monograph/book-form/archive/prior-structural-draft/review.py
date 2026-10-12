#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Devon Thiele
# SPDX-License-Identifier: CC-BY-SA-4.0
"""Check the composed book and extract unchanged pages for design review."""
from pathlib import Path
import hashlib
import json
import re

import fitz

ROOT = Path(__file__).resolve().parent
FULL = ROOT / "The-Thiele-Machine-book-design.pdf"
doc = fitz.open(FULL)
toc = doc.get_toc()
log = (ROOT / "build/book.log").read_text(errors="replace")
construction = json.loads((ROOT / "construction.json").read_text())
assert construction["body_roundtrip_identical"]
assert hashlib.sha256((ROOT.parent / "monograph.tex").read_bytes()).hexdigest() == construction["source_sha256"]
assert doc.metadata["author"] == "Devon Thiele"
assert "Overfull" not in log
assert "Missing character" not in log
assert not re.search(r"(?:Reference|Citation) .* undefined|There were undefined|Rerun to get", log)
assert len(doc) % 2 == 0

def page_for_heading(name):
    matches = [t[2] for t in toc if t[1] == name]
    assert len(matches) == 1, (name, matches)
    return matches[0]

def page_for_text(text):
    return next(i + 1 for i, page in enumerate(doc)
                if text in " ".join(page.get_text().split()))

appendices = next(t for t in toc if t[1] == "Appendices")
assert appendices[0] == 1, appendices
assert appendices[2] == page_for_heading("Things I had to learn first")
assert next(t for t in toc if t[1] == "Things I had to learn first")[0] == 2

def label_values(path):
    return dict(re.findall(r"\\newlabel\{([^}]+)\}\{\{([^{}]*)\}", path.read_text(errors="replace")))

old_labels = label_values(ROOT.parent / "monograph.aux")
new_labels = label_values(ROOT / "build/book.aux")
missing_labels = sorted(set(old_labels) - set(new_labels))
changed_labels = {k: [v, new_labels.get(k)] for k, v in old_labels.items()
                  if k in new_labels and v != new_labels[k]}
assert not missing_labels, missing_labels
assert not changed_labels, changed_labels

off_page = []
bad_destinations = []
font_ids = set()
page_metrics = []
all_links = 0
for i, page in enumerate(doc):
    assert abs(page.rect.width - 190 / 25.4 * 72) < .1
    assert abs(page.rect.height - 255 / 25.4 * 72) < .1
    for font in page.get_fonts(full=True):
        font_ids.add(font[0])
    for link in page.get_links():
        all_links += 1
        if "page" in link and not (0 <= link["page"] < len(doc)):
            bad_destinations.append([i + 1, link])
    blocks = page.get_text("dict")["blocks"]
    body_bottom = 0
    body_words = 0
    for block in blocks:
        for line in block.get("lines", []):
            for span in line["spans"]:
                r = fitz.Rect(span["bbox"])
                if r.x0 < -1 or r.y0 < -1 or r.x1 > page.rect.width + 1 or r.y1 > page.rect.height + 1:
                    off_page.append([i + 1, span["text"], list(r)])
                if r.y0 < 670:
                    body_bottom = max(body_bottom, r.y1)
                    body_words += len(span["text"].split())
    page_metrics.append({"pdf_page": i + 1, "printed_label": page.get_label(),
                         "body_words": body_words, "body_bottom_pt": round(body_bottom, 2)})
assert not off_page, off_page[:10]
assert not bad_destinations, bad_destinations[:10]
unembedded = [xref for xref in font_ids if not doc.extract_font(xref)[3]]
assert not unembedded, unembedded

def spread_run(start, end):
    return (start if start % 2 == 0 else start - 1,
            end if end % 2 == 1 else end + 1)

proof_page = page_for_text("A raised flag was checked, then committed, then certified")
checker_page = page_for_text("The compiler checks whether the types line up.")
runs = [
    ("Opening", 1, 9),
    ("The picture / How I got here", *spread_run(page_for_heading("I The picture"),
                                               page_for_heading("What structure is") - 1)),
    ("The machine / a continuous proof passage", *spread_run(proof_page - 1, proof_page + 1)),
    ("Checking it / the scope of refusal", *spread_run(page_for_heading("V Checking it, and its edge"),
                                                      checker_page + 1)),
    ("Conclusion / the return / the appendices", *spread_run(page_for_heading("Conclusion"),
                                                           page_for_heading("Things I had to learn first"))),
]
review = fitz.open()
review_toc = []
review_map = []
for title, start, end in runs:
    review_toc.append([1, title, len(review) + 1])
    assert (len(review) + 1) % 2 == start % 2, (title, start, len(review))
    review.insert_pdf(doc, from_page=start - 1, to_page=end - 1, links=False)
    review_map.extend(range(start, end + 1))
if len(review) % 2:
    review.new_page(width=doc[0].rect.width, height=doc[0].rect.height)
    review_map.append(None)
review.set_toc(review_toc)
review.set_metadata({"title": "The Thiele Machine — selected pages for design review",
                     "author": "Devon Thiele",
                     "subject": "Unchanged pages extracted from the complete book design"})
review.set_pagelayout("TwoPageRight")
review.set_page_labels([{"startpage": 0, "prefix": "Review ", "style": "D", "firstpagenum": 1}])
review_path = ROOT / "The-Thiele-Machine-reading-copy.pdf"
review.save(review_path, garbage=4, deflate=True)
review.close()
review = fitz.open(review_path)
for i, original_page in enumerate(review_map):
    if original_page is None:
        continue
    # Check the saved artifact, including the physical left/right sequence.
    assert (i + 1) % 2 == original_page % 2
    a = doc[original_page - 1].get_pixmap(matrix=fitz.Matrix(1, 1), alpha=False)
    b = review[i].get_pixmap(matrix=fitz.Matrix(1, 1), alpha=False)
    assert a.samples == b.samples, (i + 1, original_page)

# A thumbnail survey makes the whole book's density and pauses inspectable.
atlas = fitz.open()
for first in range(0, len(doc), 168):
    sheet = atlas.new_page(width=1056, height=1764)
    for offset in range(min(168, len(doc) - first)):
        x, y = (offset % 12) * 88, (offset // 12) * 126
        n = first + offset
        sheet.insert_text((x + 5, y + 9), str(n + 1), fontsize=6)
        if doc[n].get_text().strip():
            sheet.show_pdf_page(fitz.Rect(x + 5, y + 14, x + 83, y + 119), doc, n)
    sheet.get_pixmap().save(ROOT / "build" / f"pagination-{first // 168 + 1}.png")

for label, n in [("opening", 6), ("origin", page_for_heading("I The picture")),
                 ("proof", proof_page - (proof_page % 2)),
                 ("checking", checker_page - (checker_page % 2)),
                 ("return", page_for_text("And the two computers from the first pages"))]:
    start = n if n % 2 == 0 else n - 1
    spread = fitz.open()
    page = spread.new_page(width=doc[0].rect.width * 2, height=doc[0].rect.height)
    for column in range(2):
        page.show_pdf_page(fitz.Rect(column * doc[0].rect.width, 0,
                                    (column + 1) * doc[0].rect.width, doc[0].rect.height),
                           doc, start - 1 + column)
    page.get_pixmap(matrix=fitz.Matrix(1.2, 1.2)).save(ROOT / "build" / f"spread-{label}.png")

report = {
    "pages": len(doc), "reading_copy_pages": len(review), "author": doc.metadata["author"],
    "trim_mm": [190, 255], "body_roundtrip_identical": True,
    "numbered_labels_preserved": len(old_labels), "bookmarks": len(toc),
    "links": all_links, "out_of_range_link_destinations": bad_destinations,
    "off_page_text": off_page, "embedded_fonts": len(font_ids),
    "overfull_boxes": 0, "missing_glyphs": 0, "undefined_references": 0,
    "reading_copy_render_identical": True, "reading_copy_preserves_page_side": True,
    "reading_copy_runs": [{"name": title, "pdf_pages": [start, end]} for title, start, end in runs],
    "reading_copy_page_map": review_map,
    "underfull_lines_reported": log.count("Underfull"),
    "package_warnings": [l for l in log.splitlines() if "Warning:" in l],
    "full_pdf_sha256": hashlib.sha256(FULL.read_bytes()).hexdigest(),
    "scope": "Construction and navigation checks; artistic judgement and physical proof remain separate.",
}
(ROOT / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
(ROOT / "build/page-metrics.json").write_text(json.dumps(page_metrics, indent=2) + "\n")
print(json.dumps({k: v for k, v in report.items() if k not in ["reading_copy_page_map"]}, indent=2))
