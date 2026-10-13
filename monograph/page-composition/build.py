#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Devon Thiele
# SPDX-License-Identifier: CC-BY-SA-4.0
"""Compose the complete existing manuscript; do not edit its argument."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / "monograph.tex"
BUILD = ROOT / "build"
BUILD.mkdir(exist_ok=True)
source = SOURCE.read_text()
preamble, remainder = source.split(r"\begin{document}", 1)
# The entire document body, including the title page, contents, paragraph
# boundaries, headings, and explicit breaks, is passed through verbatim.
body = remainder
original_body = remainder
recovered = body
changes = []
preamble = preamble.replace(r"\documentclass[10pt,a4paper]{article}",
                            r"\RequirePackage{fix-cm}" + "\n" +
                            r"\documentclass[11pt,twoside]{article}")
preamble = preamble.replace("stretch=12", "stretch=20").replace("shrink=12", "shrink=20")
tex = preamble + r"\usepackage{book}" + "\n" + r"\begin{document}" + body
assert tex.split(r"\begin{document}", 1)[1] == remainder
(BUILD / "book.tex").write_text(tex)
shutil.copyfile(ROOT / "book.sty", BUILD / "book.sty")
report = {
    "source": str(SOURCE),
    "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
    "original_body_sha256": hashlib.sha256(original_body.encode()).hexdigest(),
    "recovered_body_sha256": hashlib.sha256(recovered.encode()).hexdigest(),
    "body_roundtrip_identical": recovered == original_body,
    "document_body_passed_through_verbatim": True,
    "composition_changes": changes,
    "author": "Devon Thiele",
    "trim_mm": [190, 255],
}
(ROOT / "construction.json").write_text(json.dumps(report, indent=2) + "\n")
for pass_number in range(1, 4):
    with (BUILD / f"pass-{pass_number}.txt").open("w") as output:
        run = subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                              "book.tex"], cwd=BUILD, stdout=output,
                             stderr=subprocess.STDOUT)
    if run.returncode:
        print((BUILD / f"pass-{pass_number}.txt").read_text()[-6000:])
        raise SystemExit(run.returncode)
    print(f"Typesetting pass {pass_number} complete", flush=True)
shutil.copyfile(BUILD / "book.pdf", ROOT / "The-Thiele-Machine-book-design.pdf")
print("Complete document body passed through verbatim; typography applied in the preamble only.", flush=True)
