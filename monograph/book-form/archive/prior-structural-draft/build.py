#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Devon Thiele
# SPDX-License-Identifier: CC-BY-SA-4.0
"""Compose the complete existing manuscript; do not edit its argument."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / "monograph.tex"
BUILD = ROOT / "build"
BUILD.mkdir(exist_ok=True)
source = SOURCE.read_text()
preamble, remainder = source.split(r"\begin{document}", 1)
_, body = remainder.split("\\tableofcontents\n\\clearpage", 1)
original_body = body
preamble = preamble.replace(r"\documentclass[11pt,a4paper]{article}",
                            r"\RequirePackage{fix-cm}" + "\n" +
                            r"\documentclass[11pt,twoside]{article}")
preamble = preamble.replace("stretch=12", "stretch=20").replace("shrink=12", "shrink=20")
changes = []

def change(old, new, purpose, expected=1):
    global body
    assert body.count(old) == expected, (purpose, body.count(old), expected)
    body = body.replace(old, new)
    changes.append({"old": old, "new": new, "purpose": purpose, "count": expected})

change(r"\subsection*{Two computers that end up the same}",
       r"\BookReturnHeading{Two computers that end up the same}",
       "The opening warehouse enters on the recurring reading position.")
for anchor, purpose in [
    ("Large language models were my hands the whole way through",
     "Begin the continuous account of authorship and refusal."),
    ("The compiler checks whether the types line up.",
     "Return to the scope of refusal through the proof checker."),
    ("And the two computers from the first pages, the sorter and the copier, holding the same bits.",
     "Return to the warehouse in the same reading position."),
]:
    change(anchor, "\\BookReturn\n" + anchor, purpose)
change(r"\phantomsection\section*{The point}",
       r"\phantomsection\section*{The point}" + "\n" +
       r"\addcontentsline{toc}{section}{The point}\markboth{The point}{The point}",
       "Include the opening in printable navigation.")
change(r"\phantomsection\section*{Before the book: the short version}",
       r"\phantomsection\section*{Before the book: the short version}" + "\n" +
       r"\addcontentsline{toc}{section}{Before the book: the short version}" +
       r"\markboth{The short version}{The short version}",
       "Include the short version in printable navigation.")
change(r"\appendix", r"\appendix" + "\n" +
       r"\BookAppendices",
       "Distinguish the appendices from Part V in the contents.")
matrix_indices = "$I, A_0, A_1, B_0, B_1, A_0B_0, A_0B_1, A_1B_0, A_1B_1$"
change(matrix_indices, matrix_indices.replace(", ", r",\allowbreak "),
       "Permit line breaks in a long inline list of matrix indices.")
for path in sorted(set(re.findall(r"\((kernel/[A-Za-z0-9/]+\.v)\)", body))):
    old = f"({path})"
    change(old, "(\\BookPath{" + path + "})",
           "Allow a printed source path to break at directory separators.", body.count(old))
change(r"\section{Sources and mathematical dependencies}",
       r"\BookReferences" + "\n" + r"\section{Sources and mathematical dependencies}",
       "Set reference entries with a natural right edge.")
change(r"\subsection{$U$ on a real guest}",
       r"\subsection{\texorpdfstring{$U$}{U} on a real guest}",
       "Give the PDF bookmark a plain-text form of the existing mathematical title.")
change("Now point it at the flag. Potential:",
       "Now point it at the flag.\\looseness=1 Potential:",
       "Give this long paragraph one extra line to avoid a crowded measure.")
for anchor in [
    "Formal verification was a graveyard of dead ends further on.",
    r"In plain words: \code{sm2\_obs s t} says two final states agree on register 0",
]:
    change(anchor, r"\enlargethispage{2\baselineskip}" + "\n" + anchor,
           "Keep a two-line chapter ending with its preceding page.")
change("I should say what Doeblin's condition costs.",
       r"\enlargethispage{2\baselineskip}" + "\n" +
       "I should say what Doeblin's condition costs.\\looseness=-1 ",
       "Keep the chapter's final transition with its argument.")
change("Then the stretches. The bound used the fact",
       "Then the stretches.\\looseness=-1 The bound used the fact",
       "Balance the final page of the toll argument.")
change("With the stretches measured in seconds, when the device hops at random moments, it's checked",
       "With the stretches measured in seconds,\\looseness=-1 when the device hops at random moments, it's checked",
       "Balance the final page of the toll argument.")
change("I should say what Doeblin's condition costs.",
       r"\begingroup\setstretch{0.95}" + "\n" + "I should say what Doeblin's condition costs.",
       "A small leading adjustment keeps the chapter's final paragraphs together.")
change("whether knowing is free.\n", "whether knowing is free.\n\\par\\endgroup\n",
       "Restore the regular leading after the chapter ending.")
change(r"\end{document}", r"\BookEnd" + "\n" + r"\end{document}",
       "Finish the printed sheet with a blank verso when necessary.")

recovered = body
for c in reversed(changes):
    assert recovered.count(c["new"]) == c["count"]
    recovered = recovered.replace(c["new"], c["old"])
assert recovered == original_body, "Composition changed manuscript content"

tex = preamble + r"\usepackage{book}" + "\n" + r"\begin{document}" + "\n" + r"""
\BookTitle
\tableofcontents
\cleardoublepage
\pagenumbering{arabic}
""" + body
(BUILD / "book.tex").write_text(tex)
shutil.copyfile(ROOT / "book.sty", BUILD / "book.sty")
report = {
    "source": str(SOURCE),
    "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
    "original_body_sha256": hashlib.sha256(original_body.encode()).hexdigest(),
    "recovered_body_sha256": hashlib.sha256(recovered.encode()).hexdigest(),
    "body_roundtrip_identical": recovered == original_body,
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
print("Complete manuscript composed; content round-trip identical.", flush=True)
