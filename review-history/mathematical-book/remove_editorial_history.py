from pathlib import Path
import json
R=Path(__file__).parent;p=R/'working.tex';s=p.read_text();changes=[]
def edit(a,b):
 global s
 assert s.count(a)==1,(a[:100],s.count(a));s=s.replace(a,b);changes.append(dict(before=a,after=b))
edit(r'\section{Every result and where it is checked}',r'\section{Companion source index}')
a=s.index('Every numbered result in this book is in the table below');b=s.index('\\begingroup\\small',a)
edit(s[a:b],r'''This index locates the companion formalizations of the book's numbered results.
Each row gives the result, its section, and the corresponding source names and files.
The mathematical statements, hypotheses and arguments are in the sections named.

``+N'' after a file means that $N$ other files under coq/ and minimal/ define or declare
an identically spelled name. Section variables and hypotheses count; notations, module
aliases and record fields do not. The file named in the row identifies the result used.
A premise has a definition but no proof; a thesis is proposed without claiming a proof.

Most rows give an equivalent statement, or one per numbered part. Where a result is
assembled from several source statements, the row identifies the composition, as in
Corollary~\ref{cor:u23-notrap-bound}. The companion release is identified in the
methodology note (Section~\ref{sec:methodology}).

''')
edit(r'\subsection{Additional source locators}',r'\subsection{Definitions and supporting results}')
edit('''The following names were previously cited in the prose. They are collected here for
readers consulting the companion sources; the mathematical statements remain in the
sections named. Further lookup information is in the companion citation concordance.''','''These entries locate definitions and supporting results in the companion sources.
The first column points to their discussion in the book.''')
edit(r'''\texttt{v4.0.0}. The editorial revision in this book changes the presentation, not those
mathematical sources. Detailed reproduction instructions accompany the repository in
\texttt{monograph/COMPANION\_CHECKS.txt}.''',r'''\texttt{v4.0.0}. Reproduction instructions are in
\texttt{monograph/COMPANION\_CHECKS.txt}.''')
edit('''These works identify the principal mathematical dependencies and the intellectual
background named in the book. The definitions, statements and worked examples remain
on its pages. A published result about thermodynamic cost, quantum correlations or
universal computation is not an additional theorem proved by this manuscript.''','''These works provide the mathematical dependencies and intellectual background cited
in the book.''')
edit("and that's the trade this edition made.","and that's the trade I made.")
p.write_text(s);(R/'editorial-history-removal.json').write_text(json.dumps(changes,indent=2,ensure_ascii=False)+'\n')
print('Removed editorial history and editorial instructions from',len(changes),'passages')
