#!/usr/bin/env python3
"""Build a print/PDF book design study from the manuscript and actual runs.

Copyright 2026 Devon Thiele. Licensed under CC-BY-SA-4.0.
The study is separate from the published monograph. No manuscript is rewritten.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT))
from thiele_small import small as S

SOURCE = (ROOT / 'monograph/monograph.tex').read_text()

def excerpt(start, end):
    return SOURCE.split(start, 1)[1].split(end, 1)[0].strip()

earned_program = [('CHECK', ('PZero',), 0), ('COMMIT', ('PZero',), 0), ('CERTIFY',)]
quiet_program = [('DEC', 0, 0)] * 3

def states(program):
    result = [S.start(0, 0)]
    for instruction in program:
        result.append(S.exec_(result[-1], instruction))
    return result

earned, quiet = states(earned_program), states(quiet_program)
assert [(s.pc, s.ca, s.cb) for s in earned] == [(s.pc, s.ca, s.cb) for s in quiet]
assert [s.mu for s in earned] == [0, 1, 2, 3]
assert [s.cert for s in earned] == [False, False, False, True]
assert all(s.mu == 0 and not s.cert for s in quiet)
assert not earned[-1].err and not quiet[-1].err

def state_dict(s):
    return {key: getattr(s, key) for key in S.State.__slots__}

receipt = {
    'source_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
    'source_sha256': hashlib.sha256(SOURCE.encode()).hexdigest(),
    'earned_program': earned_program, 'quiet_program': quiet_program,
    'earned_states': list(map(state_dict, earned)),
    'quiet_states': list(map(state_dict, quiet)),
    'scope': 'Executed examples from the handwritten Python mirror. The marks count its charged instructions, not reading, knowledge, physical work, or paper.',
    'historical_design_reviewed': {'design': 'ada54d5f / PR 205', 'reversal': 'ee5e36b4 / PR 206'},
}
(HERE / 'study-data.json').write_text(json.dumps(receipt, indent=2) + '\n')

TEX = r'''\documentclass[11pt]{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{mathpazo}
\usepackage[scaled=.92]{helvet}
\usepackage{amsmath,amssymb}
\usepackage{microtype}
\usepackage{tikz}
\usetikzlibrary{calc,arrows.meta}
\usepackage{geometry}
\geometry{paperwidth=190mm,paperheight=254mm,margin=0mm}
\usepackage{seqsplit}
\usepackage{hyperref}
\hypersetup{pdftitle={The Thiele Machine — book design study},pdfauthor={Devon Thiele},
pdfsubject={A physical page sequence using the book's own machine and its own printed pages},
pdfdisplaydoctitle=true,pdfpagelayout=TwoPageRight,hidelinks}
\pagestyle{empty}
\definecolor{ink}{HTML}{171C1D}
\definecolor{record}{HTML}{A63624}
\definecolor{quiet}{HTML}{59615F}
\definecolor{rule}{HTML}{A3AAA6}
\definecolor{paper}{HTML}{F4F1E9}
\definecolor{mist}{HTML}{E7EAE5}
\setlength{\parindent}{0pt}
\setlength{\parskip}{6pt}
\setlength{\emergencystretch}{1.5em}
\tolerance=1400
\renewcommand{\ttdefault}{lmtt}
\newcommand{\code}[1]{\textnormal{\texttt{\seqsplit{#1}}}}
\newcommand{\pagebegin}{\null\begin{tikzpicture}[remember picture,overlay,x=1mm,y=-1mm,
shift={(current page.north west)},every node/.style={inner sep=0pt,outer sep=0pt}]}
\newcommand{\pageend}{\end{tikzpicture}\clearpage}
% x, y, width, point size, leading, font, ink, text
\newcommand{\txt}[8]{\node[anchor=north west,text width=#3mm,text=#7] at (#1,#2)
  {\fontsize{#4}{#5}\selectfont #6\raggedright #8};}
\newcommand{\body}[4]{\node[anchor=north west,text width=#3mm,text=ink] at (#1,#2)
  {\fontsize{11}{14.8}\selectfont\setlength{\parskip}{5pt}\setlength{\parindent}{0pt} #4};}
\newcommand{\smallbody}[4]{\node[anchor=north west,text width=#3mm,text=ink] at (#1,#2)
  {\fontsize{10}{13.3}\selectfont\setlength{\parskip}{6pt}\setlength{\parindent}{0pt} #4};}
\newcommand{\labeltext}[3]{\txt{#1}{#2}{148}{7.5}{10}{\sffamily}{quiet}{\textls[100]{#3}}}
\newcommand{\folio}[2]{\labeltext{22}{239}{#2}\txt{166}{238}{14}{9}{11}{\sffamily}{ink}{#1}}
\newcommand{\toplabel}[1]{\labeltext{22}{16}{#1}}
\newcommand{\hairline}[3]{\draw[rule,line width=.35pt] (#1,#2)--(#3,#2);}
\newcommand{\markrail}[2]{%
  \foreach \k in {1,2,3}{\draw[rule,line width=.35pt] (162,{194-\k*8})--(178,{194-\k*8});}
  \ifnum#1>0\foreach \k in {1,...,#1}{\draw[record,line width=2.7pt] (162,{194-\k*8})--(178,{194-\k*8});}\fi
  \ifnum#2=1\fill[record] (170,207) circle (2.2);\else\draw[ink,line width=.6pt] (170,207) circle (2.2);\fi}
\newcommand{\window}[1]{%
  \draw[ink,line width=.7pt] (22,70) rectangle (152,214);
  \labeltext{30}{79}{THE VISIBLE STATE}
  \txt{29}{103}{103}{88}{91}{\sffamily\bfseries}{ink}{#1}
  \txt{33}{143}{100}{8}{10}{\sffamily}{quiet}{PROGRAM COUNTER}
  \draw[rule,line width=.35pt] (30,158)--(144,158);
  \txt{31}{170}{50}{31}{34}{\sffamily}{ink}{0}
  \txt{93}{170}{45}{31}{34}{\sffamily}{ink}{0}
  \txt{32}{198}{50}{8}{10}{\sffamily}{quiet}{COUNTER A}
  \txt{94}{198}{45}{8}{10}{\sffamily}{quiet}{COUNTER B}}
\begin{document}
'''

pages = []
def page(content):
    pages.append('\\pagebegin\n' + content + '\n\\pageend\n')

# 1 — The cover's diagram is an actual projection and record of the final state.
page(r'''
\fill[paper] (0,0) rectangle (190,254);
\labeltext{22}{20}{DEVON THIELE}
\draw[ink,line width=.75pt] (22,58) rectangle (152,215);
\txt{29}{66}{115}{21}{25}{\sffamily}{ink}{THE}
\txt{27}{91}{123}{48}{50}{\sffamily\bfseries}{ink}{THIELE}
\txt{27}{114}{130}{44}{49}{\sffamily\bfseries}{ink}{MACHINE}
\hairline{30}{150}{144}
\txt{30}{158}{110}{11}{15}{}{ink}{A Computational Model\\with Explicit Structural Cost}
\txt{30}{198}{110}{9}{11}{\ttfamily}{quiet}{4\hspace{24mm}0\hspace{24mm}0}
\markrail{3}{1}
\draw[record,line width=.5pt] (152,186)--(162,186);
\labeltext{22}{234}{THE THIELE MACHINE}
''')

# 2–3 — The author's opening, unrewritten; the large sentence is also his.
opening = excerpt('\\subsection*{Two computers that end up the same}', 'Now wait until both are done')
# Use exact paragraph boundaries, avoiding an invented continuation.
ending = SOURCE[SOURCE.index('Now wait until both are done'):].split('\n\n', 1)[0]
page(r'''
\toplabel{THE POINT}
\txt{22}{35}{132}{30}{34}{}{ink}{Two computers\\that end up the same}
\body{22}{80}{124}{''' + opening + r'''}
\draw[ink,line width=.7pt] (22,201) rectangle (152,224);
\txt{31}{207}{110}{17}{20}{\ttfamily}{ink}{1\quad 2\quad 3\quad\ldots}
\folio{2}{THE THIELE MACHINE}
''')
page(r'''
\toplabel{THE POINT}
\txt{22}{36}{137}{39}{42}{}{ink}{Same bits.}
\body{22}{75}{124}{''' + ending + r'''}
\draw[ink,line width=.7pt] (22,201) rectangle (152,224);
\txt{31}{207}{110}{17}{20}{\ttfamily}{ink}{1\quad 2\quad 3\quad\ldots}
\folio{3}{TWO COMPUTERS THAT END UP THE SAME}
''')

# 4–5 — The visible rectangles must render identically, not merely look similar.
for n, s, name, program in [
    (4, quiet[-1], 'BASE MOVES', r'DEC A 0\quad DEC A 0\quad DEC A 0'),
    (5, earned[-1], 'EARNED CHAIN', r'CHECK\quad COMMIT\quad CERTIFY'),
]:
    page(r'\toplabel{THE SMALL MACHINE / '+ name + r'}' + '\n'
         + r'\txt{22}{34}{133}{24}{28}{}{ink}{What the window shows.}' + '\n'
         + r'\txt{22}{53}{145}{8}{10}{\ttfamily}{quiet}{' + program + '}' + '\n'
         + rf'\window{{{s.pc}}}\markrail{{{s.mu}}}{{{int(s.cert)}}}' + '\n'
         + rf'\txt{{158}}{{158}}{{24}}{{7}}{{9}}{{\sffamily}}{{quiet}}{{LEDGER {s.mu}}}' + '\n'
         + rf'\txt{{160}}{{216}}{{27}}{{7}}{{9}}{{\sffamily}}{{quiet}}{{FLAG {"UP" if s.cert else "DOWN"}}}' + '\n'
         + rf'\folio{{{n}}}{{SAME START / A = 0 / B = 0}}')

# 6–7 — These blank areas are filled with real PDF objects from pages 4 and 5.
page(r'''
\toplabel{WINDOWS AND SHADOWS}
\txt{22}{34}{141}{30}{34}{}{ink}{Look again.}
\smallbody{22}{57}{131}{These are the two pages you just passed. The rectangle is the window;
the marks beside it belong to the record.}
\labeltext{22}{191}{PAGE 4}
\labeltext{99}{191}{PAGE 5}
\body{22}{203}{133}{The window is unchanged. The question ``is the flag up?'' has two different answers.}
\folio{6}{WINDOWS AND SHADOWS}
''')
window_intro = excerpt('\\subsection{The whole fact, in one paragraph}', 'Think about two states that cast the same shadow.')
page(r'''
\toplabel{WINDOWS AND SHADOWS}
\txt{22}{34}{141}{30}{34}{}{ink}{The same view.}
\smallbody{22}{57}{131}{The two windows below are taken directly from those pages.
Everything outside the rectangle has been removed.}
\labeltext{22}{152}{CROP OF PAGE 4}
\labeltext{99}{152}{CROP OF PAGE 5}
\smallbody{22}{166}{131}{''' + window_intro + r'''}
\folio{7}{WINDOWS AND SHADOWS}
''')

# 8–9 — A real mathematical spread, with assumptions and receipts at the edge.
fibre_words = 'Think about two states that cast the same shadow. ' + excerpt(
    'Think about two states that cast the same shadow.', '\n\nExactly. Let $S$')
fibre_def = 'Exactly. Let $S$ ' + excerpt('Exactly. Let $S$', '\n\n\\begin{theorem}[Decoders need constant fibres]')
fibre_thm = excerpt('\\begin{theorem}[Decoders need constant fibres]\\label{thm:fibre}', '\\end{theorem}')
fibre_proof = excerpt('\\begin{theorem}[Decoders need constant fibres]\\label{thm:fibre}', 'Checked as').split('\\begin{proof}',1)[1].split('\\end{proof}',1)[0]
page(r'''
\toplabel{7 / WINDOWS AND SHADOWS}
\txt{22}{34}{139}{29}{33}{}{ink}{The whole fact,\\in one paragraph}
\body{22}{77}{126}{''' + fibre_words + r'''}
\hairline{22}{211}{152}
\txt{22}{217}{131}{10}{13}{\itshape}{quiet}{The shape on the previous spread is an instance of this argument.}
\folio{8}{THE ARGUMENT}
''')
page(r'''
\toplabel{7 / WINDOWS AND SHADOWS}
\labeltext{22}{35}{THE STATEMENT}
\smallbody{22}{44}{126}{''' + fibre_def + r'''}
\draw[ink,line width=1.4pt] (18,103)--(18,151);
\txt{22}{104}{126}{13}{16}{\bfseries}{ink}{Decoders need constant fibres}
\smallbody{22}{119}{126}{''' + fibre_thm + r'''}
\labeltext{22}{165}{PROOF}
\smallbody{22}{175}{126}{''' + fibre_proof + r'''}
\draw[ink,line width=.6pt] (147,220) rectangle (150,223);
\draw[rule,line width=.4pt] (157,33)--(157,224);
\txt{162}{36}{20}{7}{9}{\sffamily}{quiet}{STATE\\$S$\\[7pt]VIEW\\$V$\\[7pt]WINDOW\\$w$\\[7pt]QUESTION\\$q$\\[7pt]DECODER\\$d$}
\folio{9}{OBSERVATIONPOLICY.V / EXACT CLAIM AND PROOF}
''')

# 10–13 — Four successive states, so a turn of a leaf exposes an actual transition.
captions = [
    ('Start.', r'No facts on the record. No commitment. The flag is down.'),
    ('Check.', r'The counter is zero. The successful check records that claim about edition zero.'),
    ('Commit.', r'The commitment names the checked claim about the same edition. The counter stays zero.'),
    ('Certify.', r'The flag rises. The ledger records three charged instructions.'),
]
for k, s in enumerate(earned):
    title, caption = captions[k]
    name = 'START' if k == 0 else earned_program[k-1][0]
    page(r'\toplabel{THE MACHINE / ' + name + '}' + '\n'
         + r'\txt{22}{32}{135}{35}{39}{}{ink}{' + title + '}' + '\n'
         + r'\txt{22}{51}{130}{10}{13}{}{ink}{' + caption + '}' + '\n'
         + rf'\window{{{s.pc}}}\markrail{{{s.mu}}}{{{int(s.cert)}}}' + '\n'
         + rf'\txt{{158}}{{158}}{{25}}{{7}}{{9}}{{\sffamily}}{{quiet}}{{LEDGER {s.mu}}}' + '\n'
         + rf'\txt{{160}}{{216}}{{27}}{{7}}{{9}}{{\sffamily}}{{quiet}}{{FLAG {"UP" if s.cert else "DOWN"}}}' + '\n'
         + rf'\folio{{{10+k}}}{{A = 0 / B = 0 / EDITION = 0}}')

# 14–15 — Sustained reading. The mechanism must also support ordinary prose.
origin_intro = excerpt('\\label{sec:origin}\n%===========================================================================', 'Once I started digging in,')
origin_middle = 'Once I started digging in, ' + excerpt('Once I started digging in,', '\n\nThe method underneath')
origin_next = 'The method underneath ' + excerpt('The method underneath', '\n\nThen within weeks')
page(r'''
\toplabel{I / THE PICTURE}
\txt{22}{33}{136}{30}{34}{}{ink}{How I got here}
\body{22}{67}{126}{''' + origin_intro + r'''}
\draw[ink,line width=.6pt] (158,33)--(158,215);
\draw[ink,line width=.6pt] (151,33)--(158,33);
\draw[ink,line width=.6pt] (151,215)--(158,215);
\folio{14}{DEVON THIELE}
''')
page(r'''
\toplabel{1 / HOW I GOT HERE}
\body{22}{34}{126}{''' + origin_middle + '\n\n' + origin_next + r'''}
\draw[ink,line width=.6pt] (158,33)--(158,215);
\draw[ink,line width=.6pt] (151,33)--(158,33);
\draw[ink,line width=.6pt] (151,215)--(158,215);
\folio{15}{THE PICTURE}
''')

# 16–17 — The cover returns as the same PDF object, now readable as a record.
page(r'''
\toplabel{RETURN TO THE COVER}
\txt{22}{34}{140}{30}{34}{}{ink}{The ink stayed.}
\smallbody{22}{58}{130}{This is the cover again, unchanged. Its numbers are the final window
of the earned run: program counter 4, counters 0 and 0. The three marks beside the frame
are its ledger. The filled circle is its raised flag.}
\folio{16}{THE THIELE MACHINE}
''')
page(r'''
\toplabel{CONCLUSION}
\txt{22}{35}{136}{32}{36}{}{ink}{Now there's you.}
\body{22}{78}{126}{The theorems are what they are, with their premises printed. The interpretation is mine, and
I've tried to say at every turn which is which, because the first time through I was the
only one checking, and I've met me, and that's not enough people. Now there's you.}
\draw[ink,line width=.75pt] (22,155) rectangle (152,215);
\labeltext{30}{164}{THE THIELE MACHINE}
\txt{30}{187}{110}{14}{18}{}{ink}{Devon Thiele}
\markrail{3}{1}
\folio{17}{THE THIELE MACHINE}
''')

# 18–19 — Design rationale is outside the proposed book sequence.
page(r'''
\toplabel{DESIGN STUDY / NOTES}
\txt{22}{33}{141}{27}{31}{}{ink}{What this tests}
\smallbody{22}{61}{130}{
\textbf{The book becomes an object in its own argument.}
Pages 6 and 7 contain actual reproductions and crops of pages 4 and 5. The restricted
views are identical, while the records outside them differ. The reader can inspect that
claim on the printed object.\par
\textbf{The form becomes readable as the argument develops.}
The cover carries the final state of a specific machine run. The sequence teaches the
reader to read its frame, numbers and marks. When the cover returns, its ink is unchanged.\par
\textbf{Page turns expose real transitions.}
The four states on pages 10--13 come from the small machine's CHECK, COMMIT, CERTIFY run.
The marks count those instructions. They do not measure the reader's attention, understanding,
reading effort, or physical energy.\par
\textbf{Print and PDF use the same pages.}
The mechanism uses position, repetition, comparison and page turning. Color is supplementary:
line weight, count and filled or empty circles carry every distinction in monochrome too.\par
\textbf{This is a prototype.}
The selected prose and theorem text come from the released manuscript. The demonstration
captions are new. This study tests a design language; it is not a newly published edition
or a claim that the entire book has been redesigned.}
\folio{18}{DESIGN RATIONALE / NOT PART OF THE BOOK}
''')
page(r'''
\toplabel{DESIGN STUDY / SCOPE}
\txt{22}{33}{141}{27}{31}{}{ink}{What comes from where}
\smallbody{22}{61}{131}{
\textbf{Manuscript.} The opening's two computers; Chapter 7's window argument, statement
and proof; Chapter 1's autobiographical opening; and the conclusion are excerpts from
Devon Thiele's \textit{The Thiele Machine}. Their order here is a design sample, not a
proposed rearrangement of the manuscript.\par
\textbf{Machine.} From $(A,B)=(0,0)$, three zero-branch DEC instructions and the earned
CHECK, COMMIT, CERTIFY chain both reach the window $(4,0,0)$. Their ledgers are 0 and 3;
their flags are down and up. The generator executes both programs using
\code{thiele\_small/small.py}, the handwritten Python mirror, and checks the displayed states.\par
\textbf{Mathematics.} The window theorem is the manuscript's theorem ``Decoders need
constant fibres.'' Its checked counterparts are
\code{decoding\_requires\_fiber\_constancy} and
\code{selected\_representatives\_give\_decoder}, in \code{ObservationPolicy.v}.\par
\textbf{Earlier design work.} The recorded design in PR 205 and its reversal in PR 206
were inspected, including the generated case diagrams and the prior PDF. Private
brainstorming conversations are not present in the repository.\par
\textbf{Production.} Pages are 190 by 254 millimeters. Text and diagrams remain vector
objects, fonts are embedded, and the same PDF can be read on screen or printed at actual
size. The single-page PDF uses a facing-page viewing preference. No special paper,
transparency, fold, animation or viewer behavior is needed to understand the sequence.}
\folio{19}{DEVON THIELE / BOOK DESIGN STUDY}
''')

assert len(pages) == 19
(HERE / 'study.tex').write_text(TEX + '\n'.join(pages) + '\\end{document}\n')
for pass_number in (1, 2):
    with (HERE / f'build-{pass_number}.log').open('w') as log:
        subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error', 'study.tex'],
                       cwd=HERE, check=True, stdout=log, stderr=subprocess.STDOUT)

# Insert copies of the actual rendered pages, preserving vector text and drawing.
import fitz
base = fitz.open(HERE / 'study.pdf')
out = fitz.open()
out.insert_pdf(base)
mm = 72 / 25.4
def rect(x0,y0,x1,y1): return fitz.Rect(x0*mm,y0*mm,x1*mm,y1*mm)
out[5].show_pdf_page(rect(22,84,87,171),base,3)
out[5].show_pdf_page(rect(99,84,164,171),base,4)
window_clip = rect(22,70,152,214)
out[6].show_pdf_page(rect(22,84,79,147),base,3,clip=window_clip)
out[6].show_pdf_page(rect(99,84,156,147),base,4,clip=window_clip)
out[15].show_pdf_page(rect(44,102,145,237),base,0)
out.set_metadata({'title':'The Thiele Machine — book design study', 'author':'Devon Thiele',
                  'subject':'A physical page sequence using the book’s own machine and printed pages',
                  'creator':'LaTeX and PyMuPDF'})
out.set_pagelayout('TwoPageRight')
out.save(HERE / 'the-thiele-machine-design-study.pdf',garbage=4,deflate=True)

# A literal visual assertion underlying the design, checked after PDF assembly.
final=fitz.open(HERE / 'the-thiele-machine-design-study.pdf')
assert all(len(p.get_text().strip()) > 25 for p in final), 'A page has no readable text'
crop_inside=rect(22.5,70.5,151.5,213.5)
a=final[3].get_pixmap(matrix=fitz.Matrix(2,2),clip=crop_inside,alpha=False)
b=final[4].get_pixmap(matrix=fitz.Matrix(2,2),clip=crop_inside,alpha=False)
assert a.samples == b.samples, 'The supposedly identical printed windows differ'
assert sum(v < 100 for v in a.samples) > 2000, 'The compared window has no visible ink'
receipt['identical_window_pixels'] = True
receipt['pages']=len(final)
receipt['pdf_sha256']=hashlib.sha256((HERE/'the-thiele-machine-design-study.pdf').read_bytes()).hexdigest()
(HERE/'study-data.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('Built',len(final),'pages; executed both traces; rendered windows are identical.')
