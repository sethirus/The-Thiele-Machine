from pathlib import Path
import re,json,hashlib,shutil
R=Path(__file__).parent;repo=Path('/workspace/The-Thiele-Machine-book-design');dest=repo/'monograph/companion';dest.mkdir(exist_ok=True)
old=(R/'companion-methodology-original.tex').read_text()
blocks=re.findall(r'\\begin\{verbatim\}([\s\S]*?)\\end\{verbatim\}',old)
release=blocks[0].strip().replace("tag v4.0.0, this edition's release tag",'tag v4.0.0, the companion mathematical-source release').replace('Revision used for this edition:','Companion source revision:').replace('Manuscript source for this edition:', 'Manuscript originally published with that release:').replace('monograph/monograph.tex at the release commit; a file','monograph/monograph.tex at the release commit; a file')
text='''COMPANION CHECKING PROCEDURES
The Thiele Machine — Devon Thiele

These procedures concern the companion software. The book presents the mathematical
claims, their conditions and their arguments on the page. Software checking does not
establish that a definition captures the intended idea or that a model describes a
device. A passing build is not a substitute for either question.

The working editorial revision may differ from the manuscript at v4.0.0. The release
record below identifies the unchanged mathematical sources and their receipt, not a
publication of the revised manuscript. To reproduce that release, use a checkout of
v4.0.0. To check the current working sources, use the commands on the current checkout.

BEGIN RELEASE RECORD
'''+release+'''
END RELEASE RECORD

Prerequisites
Python 3, GNU make, Coq 8.18 and its standard library, CSDP, OCaml with ocamlfind,
and MetaCoq 1.2.1 for Coq 8.18. The vendored lambda-calculus files need MetaCoq.
See scripts/install_metacoq.sh and the repository's dependency documentation.

Clean reproduction
Run from the repository root:

  python3 scripts/reproduce_coq.py

The script snapshots the sources, builds the required vendored modules, regenerates
the build file, rebuilds the proofs, and runs the independent module checker. It
reuses no compiled proof from the checkout. Its pass file is written only after all
stages pass. Additional probe files may be supplied with --probe; none run by default.
A failed run can resume from its snapshot:

  python3 scripts/reproduce_coq.py --resume \\
    --output artifacts/reproduction/RUN_DIRECTORY

A source change requires a new snapshot. Inspect the full statement, definitions and
derivation of any result being compared with the book; compilation does not perform
that comparison.

Receipt interpretation
The corpus digest fingerprints the listed proof files and vendored library, their
paths, the compiler version, the project manifest, and the five audit scripts.
Comments and runs of whitespace in proof text are normalized, as are designated
claim_not_imply audit-note strings. The Python scripts are tokenized without comments;
version two uses token names instead of Python's numeric token IDs so 3.12 and 3.13
agree. See scripts/assumption_receipt_fingerprint.py for the exact serialization.
Regenerate the receipt after a substantive change to the proof corpus.

Other reproduction commands
'''+blocks[-1].strip()+'''

Tests requiring the proof compiler skip without version 8.18 and a compiled tree.
The environment variables pointing tests at a compiled tree are documented in
tests/realize_harness.py. The custom auditor uses heuristics: a warning requires
inspection and is not itself evidence that a theorem is false.

Source comparison material
monograph/companion/source-statements.tex preserves the former printed source-statement
appendix for readers comparing literal declarations. It is excluded from the book build.
monograph/companion/citation-concordance.txt preserves the original source citations,
including names shared by more than one module. The book's source index is the first
place to look for a numbered result.
'''
(repo/'monograph/COMPANION_CHECKS.txt').write_text(text)
shutil.copyfile(R/'companion-source-statements.tex',dest/'source-statements.tex')
# Keep every original citation in its original context, avoiding guessed module associations.
s=(R/'manuscript-before.tex').read_text();lines=['SOURCE CITATION CONCORDANCE\nThe Thiele Machine — Devon Thiele\n\nOriginal citation contexts before the presentation revision.\nThis is lookup material, excluded from the rendered book. Statements in historical\ncontexts below should be compared with the current book and source files.\n\n']
section='Front matter';count=0
for p in s.split('\n\n'):
 ms=re.findall(r'\\(?:section|subsection)\*?\{([^\n]+)\}',p)
 if ms:section=ms[-1]
 if re.search(r'\\code\{|\b[A-Za-z][A-Za-z_/-]*\.v\b',p) and not p.lstrip().startswith('%'):
  count+=1;lines.append(f'[{count}] {section}\n{p}\n\n')
(dest/'citation-concordance.txt').write_text(''.join(lines))
(dest/'README.txt').write_text('''Companion lookup material — not included in the book build.

source-statements.tex: the former appendix of literal declarations and comparisons.
It is retained for source inspection, with historical section references as printed
before this editorial revision. Those references are not a standalone document.

citation-concordance.txt: original source-reference contexts, retained so no locator
is lost when implementation names leave the narrative. The current book supplies the
readable statement; the repository supplies the implementation.

Checking procedures and the release receipt are in ../COMPANION_CHECKS.txt.
''')
print('Companion documentation created;',count,'citation contexts retained')
