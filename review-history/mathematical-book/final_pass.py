from pathlib import Path
import json,re
R=Path(__file__).parent
s=(R/'pre-final.tex').read_text(); edits=[]
def edit(a,b,why='Remove implementation framing while preserving the claim'):
 global s
 assert s.count(a)==1,(a[:100],s.count(a))
 edits.append(dict(before=a,after=b,reason=why));s=s.replace(a,b)
def para(needle,new):
 p=[p for p in s.split('\n\n') if needle in p];assert len(p)==1,(needle,len(p));edit(p[0],new)
edit('simple:coq} has it):','simple:','Repair a citation-removal boundary')
para('One more thing before the book starts','')
edit('Part V is how to check all of it and how to break it.','Part V is where to challenge it and what would break it.')
edit("That's it. Add the one rule below and I'll call it a certification system; in the checked\nrecord the rule is a sixth field, so nothing counts as one without it.","That's it. Add the one rule below and I'll call it a certification system.")
para('This book leans on a small number of rules',"This book uses systems defined by stated conditions, and theorems with stated premises.\nI've named each condition where it's used. Here they are side by side, because a reader\nwho wants to break this book should be able to see every place where it says ``suppose,''\nin one list, with what each ``suppose'' buys.")
para('One thing to undo first',"The labels A2 to A6 in this appendix are shorthand for the conditions listed below.\nThey are not additional claims: each label names the rule written beside it.")
edit(r'\subsection{The records that carry a rule}',r'\subsection{Systems and their conditions}')
edit('The record is a general shape.','These conditions describe a general setting.')
edit("Charguéraud and Pottier's time credits in Coq, 2019","Charguéraud and Pottier's time credits, 2019")
# Scope and falsification stay explicit; files cease to be the speaker.
for a,b in [
 ('is false, and the file proves it false','is false, as the following example shows'),
 ('I have to be exact about one thing the file is exact about.','I have to be exact about one thing.'),
 ('so a zero price meets the halving rule, and the file takes it.','so a zero price meets the halving rule and is the price chosen here.'),
 ('slots, and \\emph{no refund cap}; the file says so.','slots, and \\emph{no refund cap}.'),
 ('name, and the file says that too.','name.'),
 ("(the file calls that free forgery)",""),
 ("The file labels it a sanity check, and that's all it is.","It's an illustration, and that's all it is."),
 ("It isn't a Thiele machine in this book's sense, and the file says not to cite it\nas one.","It isn't a Thiele machine in this book's sense."),
 ("my files don't redo","I don't redo here"),
 ("the library's own compiler","the counter-machine compiler"),
 ("One number you'll see in the files:","One useful rational bound:"),
 ('rational code can test','rational arithmetic can test'),
 ('So the files also have the check with a tolerance.','The check can also allow a tolerance.'),
 ("That's simulation and arithmetic. No theorem in the\nfiles says it.","That's simulation and arithmetic; no proof of that limit is given here."),
 ("The Python host in \\texttt{thiele\\_small/chsh.py} implements the same\ninteger check and instruction chain. The\ncheck certifies","The check certifies"),
 ("The source proves\nsoundness only; no converse is stated.","The argument establishes soundness only; no converse is stated."),
 ("The source does not state that the completion set lies inside the no-signalling set.","No inclusion in the no-signalling set is established here."),
 ("What ties it to a machine: the protocol counts one logical event (the file defines that\ncount as the constant one)","What ties it to a machine: the protocol counts one logical event, by definition"),
 ("The file's ``heat to the bath''","Here ``heat to the bath''"),
 ('and anyone who tells you otherwise is reading a file name.','and anyone who tells you otherwise has skipped the conditions.'),
 ("buckets the letters name numerator and denominator, so here $N$ is the difference and $D$ the count, the reverse","buckets $N$ names the numerator and $D$ the denominator: the difference and the count, the reverse"),
]:
 if a in s:edit(a,b)
 else:print('NOT FOUND',a)
edit("The file's header also argues that every point with a rational PSD completion has such a\ncertificate; that is a comment, and no theorem states it.","The further claim that every point with a rational PSD completion has such a certificate\nis not proved here.")
edit("has run $U_P$ on it: the files it lives in aren't extracted, the compiled programs are far too big\nfor any machine to step through, and some of the library's pieces don't compute inside the checker\nat all.","has run $U_P$ on it. An executable version of the full construction has not been produced,\nand its compiled programs are impractically large.")
edit("Here's what ran, on the extracted program, compared against the\nPython guest at the end:","Here's what ran, on the executable host, compared against a separate\nguest implementation at the end:")
edit("The last two stages, the two-counter guest and $U_P$ running it, are proved. They aren't\nrun, for\ntwo reasons: the files that build the guest aren't extracted, and even if they were, $U_P$ on a\ncompiled guest would be slow for the same reason $U$ on a certifying guest is.","The last two stages, the two-counter guest and $U_P$ running it, are proved but have not\nbeen run. An executable version of those stages has not been produced, and $U_P$ on a\ncompiled guest would be slow for the same reason $U$ on a certifying guest is.")
# State the reduction rather than identifying a software-specific formulation.
edit("The library's two-counter machine agrees with the INC/DEC fragment: its step, its stop, and\nits termination match those of the compiled program, so a library problem $(P, a, b)$ halts", "The two-counter machine used by Forster, Larchey-Wendling and coauthors agrees with the\nINC/DEC fragment: its step, its stop, and its termination match those of the compiled program,\nso its halting problem at $(P, a, b)$ has a positive answer")
edit("question ``does program $P$ halt from $\\mathrm{start}(a, b)$?'' is undecidable in the\nlibrary's sense:","question ``does program $P$ halt from $\\mathrm{start}(a, b)$?'' is undecidable in the\nfollowing reduction sense:")
para("The agreement is a case split on the library's instruction",r'''\begin{proof}
The agreement is a case split on the counter-machine instruction at the current line,
and then induction along the run, ending in Theorem~\ref{thm:u34-halting}. Composing a
proposed decider for the compiled program with the compile map would decide two-counter
halting. Forster, Larchey-Wendling and coauthors' reduction would then enumerate the
complement of single-tape binary Turing machine halting, as claimed.
\end{proof}''')
edit("and nobody (in the library's sense) can predict in general what", "and no algorithm can predict in general what")
edit("layer in my files.","layer in this construction.")
edit("to ``two counters,'' and that construction is his and the library's, and I use it as it stands.","to ``two counters,'' and I use that prior construction as it stands.")
# Repeated references retain an explicit pointer to the same reduction formulation.
for a,b in [
 ("in the library's synthetic sense",r'in the reduction sense of Theorem~\ref{thm:u34-undecidable}'),
 ("in the library's sense of Theorem",'in the reduction sense of Theorem'),
 ("in the library's sense of\n",'in the reduction sense of\n'),
 ("in the library's sense",r'in the reduction sense of Theorem~\ref{thm:u34-undecidable}'),
 ("in the library's\nsense",r'in the reduction sense of Theorem~\ref{thm:u34-undecidable}'),
]:
 if a in s:
  old=s;new=s.replace(a,b);edits.append(dict(before=a,after=b,reason='State the mathematical reduction sense',all=True));s=new
# Finish the fraction-free identity without sending the reader to a program.
edit(r'''where $P_1 = \sum_j h_{1j} v_j$, $Q_1 = (h_{11}h_{22} - h_{12}^2) v_2 + (h_{11}h_{23} -
h_{12}h_{13}) v_3 + (h_{11}h_{24} - h_{12}h_{14}) v_4$, and $Q_2$ is the third linear form
. With every $d_k > 0$ the right side is nonnegative and the factor on the
left is positive.''',r'''where, writing $e_{ij}=h_{11}h_{ij}-h_{1i}h_{1j}$,
\[
\begin{aligned}
P_1 &= \sum_j h_{1j}v_j,\\
Q_1 &= d_2v_2+e_{23}v_3+e_{24}v_4,\\
Q_2 &= d_1d_3v_3+(d_2e_{34}-e_{23}e_{24})v_4.
\end{aligned}
\]
Expanding both sides verifies the identity. With every $d_k>0$ the right side is
nonnegative and the factor on the left is positive.''','Supply the mathematical expression previously delegated to a source identifier')
# The source index remains an optional lookup, not an appeal to authority.
edit('Each row has one of three relations to its Coq names. Most are', 'Most rows are')
edit(r'''A name and its file fix the constant, the revision is the one in
Section~\ref{sec:coq}, and Section~\ref{sec:coq-statements} prints twenty-one of the
statements with their premises and that comparison made.''',r'''A name and its file locate the companion statement. The revision and the role of those
sources are described in the methodology note (Section~\ref{sec:methodology}).''')
edit(r'''The solver that proposes the certificate for \code{psatz} in Section~\ref{sec:coq}; Coq checks it again.''','The semidefinite solver used in the companion checking work.')
edit("The ``Thiele'' in those names is a local record, a Turing configuration\nand a number.","The construction here is a Turing configuration paired with a number.")
edit("It isn't a Thiele machine in this book's sense, and the file says not to cite it\nas one simulating Turing machines.","It isn't a Thiele machine in this book's sense, so it does not establish a Thiele simulation\nof Turing machines.")
edit("The files call that rule A2 in the numbering their\ncertification records use", "The rule is called A2 in the conditions table")
edit("halting, and the library already says what that would cost:","halting, with the consequence stated in Theorem~\\ref{thm:u34-undecidable}:")
edit("the same synthetic sense of\n``undecidable''", "the same reduction sense of\n``undecidable''")
edit("(2) The library's undecidability of\nMinsky-machine halting", "(2) The undecidability of Minsky-machine halting proved by\nForster, Larchey-Wendling and coauthors")

# Detached punctuation left by source-only parenthetical references.
new=re.sub(r'[ \t]*\n[ \t]*([,.;:])',r'\1',s)
new=re.sub(r' +([,.;:])',r'\1',new)
new=re.sub(r'\n{3,}','\n\n',new)
(R/'final-edits.json').write_text(json.dumps(edits,indent=2,ensure_ascii=False)+'\n')
(R/'final-stage-preview.tex').write_text(new)
print(len(edits),'final edits')
