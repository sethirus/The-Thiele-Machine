from pathlib import Path
import re,json
R=Path(__file__).parent;repo=Path('/workspace/The-Thiele-Machine-book-design');s=(R/'before.tex').read_text();changes=[]
def edit(a,b,reason='Supply the argument within the book'):
 global s
 assert s.count(a)==1,(a[:120],s.count(a));s=s.replace(a,b);changes.append(dict(before=a,after=b,reason=reason))
def para(needle,new):
 p=[p for p in s.split('\n\n') if needle in p];assert len(p)==1,(needle,len(p));edit(p[0],new)
a=s.index(r'\section{Companion source index}');b=s.index(r'\section{The CHSH derivation, in full}',a)
(repo/'monograph/companion/source-index.tex').write_text(s[a:b]);edit(s[a:b],'','Keep software lookup material outside the book')
a=s.index(r'\section{Methodology note}');b=s.index(r'\section{Sources and mathematical dependencies}',a)
edit(s[a:b],r'''\section{Methodology note}
\label{sec:methodology}

I used a proof assistant to constrain formal derivations produced with language models
and to catch errors. It checks derivations within its logic. It does not establish that
a definition captures the intended idea, that a model describes a physical device, or
that a result matters. Those questions belong to the argument.

''','Remove repository instructions from the book')
para('uses the standard-library fact',r'''A duplicate-free list of $n$ members drawn from an $n$-member set contains the whole set:
if it omitted one member, it would put $n$ distinct members into the remaining $n-1$ places.
Induction on the number of places rules that out: remove one occupied place and its member,
and the same excess remains until no place is left. This is the pigeonhole in the form
Leurechon would recognise.''')
edit('''My file rebuilds L and reproves all of it on the standard library alone;
the route is theirs, and Barendregt's before them.''',r'''The term construction is given in Appendix~\ref{sec:quoting-construction};
the route is theirs, and Barendregt's before them.''')
para("Now the part that isn't mine. Proving that halting",r'''Now the part that isn't mine. Two-counter universality is Minsky's, and the constructions
of Forster, Larchey-Wendling and their coauthors connect it to several other models.
The counter convention matters: DEC at zero goes on to the next instruction; otherwise
it takes one off and jumps. Appendix~\ref{sec:counter-constructions} builds the route
from a tape to counters, packs finitely many counters into two, and gives the halting
diagonal. The remaining step here is to match that two-counter machine to this
machine's INC/DEC fragment, instruction for instruction.''')
edit('''Forster, Larchey-Wendling and coauthors' reduction would then enumerate the
complement of single-tape binary Turing machine halting, as claimed.''',r'''The tape-to-counter reduction in Appendix~\ref{sec:counter-constructions} would then
decide single-tape binary halting and hence enumerate its complement, as claimed.''')
edit('''The two-counter machine used by Forster, Larchey-Wendling and coauthors agrees with the
INC/DEC fragment''','''The two-counter machine with the instruction convention just stated agrees with the
INC/DEC fragment''')
edit('''with the undecidability library's compiler from computable functions to
counter machines doing the hard part''',r'''using the translations of Appendix~\ref{sec:counter-constructions} from computable
functions to counter programs''')
edit('''The four programs are written out from the library's building blocks and proved to compute
those four things.''','''The driver returns the fixed move; the step adds one; the price returns three; and the
reading compares the state with three. The counter constructions in
Appendix~\\ref{sec:counter-constructions} implement all four.''')
edit('''halting run. Express that algorithm in the lambda calculus L and apply the translation from L to
Minsky programs established by Forster, Larchey-Wendling and coauthors. This gives a
program of two-counter instructions that a host program can be read off from, instruction
for instruction. This construction supplies the program that computes the evaluator. The fixed-point argument below is not theirs.''',r'''halting run. Appendix~\ref{sec:counter-constructions} implements this search with a finite
counter program. The host runs those INC and DEC instructions on the required registers,
with HALT marking the returned output. This supplies $W$.''')
edit('''by the same route
through L and the Minsky compiler, reading the Boolean off $D$'s runs with the standard library's
unbounded search''',r'''by the finite-simulation search of Appendix~\ref{sec:counter-constructions}, reading the
Boolean from the first halting run of $D$''')
edit('''The copy is written out again in its own
file, and no theorem derives it from this one; putting the two side by side is how you check
they're the same machine.''',r'''The instruction rules are those already given, with the chosen property language in place
of the three original properties. For sorted lists, decode 0 as the empty list and
$\langle h,t\rangle$ as the list with head $h$ and tail decoded from $t$.
Every positive code has $t$ smaller than itself, so decoding terminates. The checker
returns yes on an empty list or singleton, and on $a,b,\ldots$ exactly when $a\le b$
and it returns yes on $b,\ldots$. Induction on the list proves that this is exactly
adjacent nondecreasing order. The provenance proof uses only equality of properties
and agreement of checker and meaning, so the same instruction-by-instruction argument applies.''')
edit('''exponential packing, which I don't redo here; the compiler behind $U_P$ uses the library's
version of it''',r'''exponential packing, constructed in Appendix~\ref{sec:counter-constructions}''')
para('My first idea was to wire the boxes',r'''My first idea was to wire the boxes to each other myself, two at a time, with a relation that
says one box's run keeps pace with another's. Section~\ref{sec:latch} defines weak base
equivalence, but the equivalence needed here is about computed relations. The seven models
are the weak call-by-value lambda calculus L, Turing machines, two Minsky instruction
conventions, binary stack machines, Conway's FRACTRAN, and the $\mu$-recursive functions.
Their equivalence is prior work, developed in the constructions of Minsky, Shepherdson and
Sturgis, and Forster, Larchey-Wendling and their coauthors. The translations and their
input and output encodings are given in Appendix~\ref{sec:counter-constructions}.''')
edit('''(2) The undecidability of Minsky-machine halting proved by
Forster, Larchey-Wendling and coauthors, carried over to the book's instruction set line by line.''',r'''(2) The tape simulation, prime packing and halting diagonal of
Appendix~\ref{sec:counter-constructions}, carried over to the book's instruction set line by line.''')
edit('''Second, it doesn't contain a Turing machine's rule table running a tape. The Turing machines here are
the library's, and they enter through what they compute.''',r'''Second, the lift does not itself give each Turing transition a record operation. The
tape-to-counter construction of Appendix~\ref{sec:counter-constructions} connects the bases
through what they compute; the lift supplies the record operations.''')
# Explicit internal destinations for constructions and proofs.
edit('''$U$ is the fixed list of 3728 host instructions described above, starting at line 1 and''',r'''$U$ is the fixed list of 3728 host instructions specified by the block expansions in
Appendix~\ref{sec:universal-blocks}, starting at line 1 and''')
edit('''For each, the matching stretch of $U$ is proved to land where the case says.''',r'''The block invariants and the case analysis in Appendix~\ref{sec:universal-blocks}
show where each matching stretch lands.''')
edit(r'\subsection{The quantum set, checked}',r'\subsection{The quantum set}')
edit('''entries. Now the trick. There are four real eight-by-eight matrices''',r'''entries. Appendix~\ref{sec:chsh-derivation}, Section~\ref{sub:four-vectors}, gives the
factorization and the measurements explicitly. Now the trick. There are four real eight-by-eight matrices''')
edit("put Bob's two at the right angle to each other,", "choose an angle between Bob's two that meets both pairs of constraints,")
edit('''and so does Tsirelson's point.

\\subsection{What isn't proved}''',r'''and so does Tsirelson's point. The interval construction, including both endpoint cases,
is in Section~\ref{sub:arcsine-construction}.

\subsection{What isn't proved}''')
edit('''equivalence: a table of four correlators comes from a local model exactly when each is between
$-1$ and $1$ and all eight CHSH inequalities hold.''',r'''equivalence: a table of four correlators comes from a local model exactly when each is between
$-1$ and $1$ and all eight CHSH inequalities hold. Section~\ref{sub:finite-local-construction}
constructs the finite distribution.''')
anchor=r'\subsection{What is not proved}'
edit(anchor,(R/'quantum-constructions.tex').read_text()+'\n'+r'\subsection{Scope of the constructions}')
edit('''The following are cited results and open questions. Where part of one is proved, the
paragraph names the theorem and the part that stays cited.''','''The constructions above establish the correlation characterizations. The following
paragraphs distinguish their scope from the completeness of a particular integer test,
from full behaviours with marginals, and from claims about experimental data.''')
# Give the numeric/RAM lift its concrete representation and step computation.
needle='''(4) Any box on numbers
with a universal base lifts to a Thiele-complete machine, and its step, computable in one model, is
computable in all seven.
\\end{theorem}'''
extra=r'''

\begin{proof}
(1) Compose the translations of Appendix~\ref{sec:counter-constructions}.
(2) Encode a configuration as $\langle\ell,\langle a,b\rangle\rangle$.
Decoding, performing one INC or DEC, and encoding the result are the total finite
arithmetic operations constructed there. The decoding window therefore commutes with
each instruction exactly; loading is the encoding of $(1,a,b)$.
(3) Let RAM registers 0, 1 and 2 hold the simulated line, $A$ and $B$, and keep
register 3 equal to 1. To increment counter register $r$, add register 3 to $r$
and then to register 0. To decrement it with target $j$, use these six lines, numbered 0 to 5:
if $r>0$ jump to 3; add register 3 to register 0; jump to 6;
subtract register 3 from $r$; set register 0 to $j$; jump to 6.
At line 6 the finite block has ended. A base move restarts a block at its first line,
runs it for its length, and keeps the resulting registers; an ended block stays put.
The zero and positive cases give exactly the required window, and neither changes
register 3. Loading puts $(1,a,b,1)$ in registers 0 to 3.
(4) Apply the lift theorem to that universal base and apply (1) to its step function.
\end{proof}
'''
edit(needle,needle+extra)
anchor=r'\section{Methodology note}'
edit(anchor,(R/'computation-constructions.tex').read_text()+'\n'+(R/'universal-construction.tex').read_text()+'\n'+anchor)
# Source terminology in credits is unnecessary to the mathematical attribution.
s=s.replace("The library and I use Minsky's version and Minsky's name.","I use Minsky's version and Minsky's name.")
s=s.replace("the library's machine, so halting is undecidable for it", "the two-counter machine, so halting is undecidable for it")
s=s.replace("the compiler that carries the guest onto two counters is the library's.",r"the counter-compilation construction is given in Appendix~\ref{sec:counter-constructions}.")
# Keep historical credit without making the definitions depend on software.
s=s.replace("library and I use Minsky's version and Minsky's name.","machine uses Minsky's version and Minsky's name.")
s=s.replace("counting from 1 the way the library's two-counter machine does", "counting from 1")
s=s.replace("the library's two-counter\nmachine, which it calls a Minsky machine, numbers its lines from 1", "the two-counter\nmachine used by Forster, Larchey-Wendling and coauthors numbers its lines from 1")
s=s.replace("with halting reduced to the library's", "with halting reduced from two-counter halting")
s=s.replace("L's recursion theorem, Rice and halting, checked; the library's compiler used to put every computably presented Thiele machine on the universal host", "L's recursion theorem, Rice and halting; a counter compilation putting every computably presented Thiele machine on the universal host")
s=s.replace("There's a decider for it with a soundness proof, in two", "There's a certificate checker for it with a soundness proof, in two")
s=s.replace("is not proved here. It's a decider with a soundness proof, as", "is not proved here. The certificate checker is sound, as")

s=s.replace(r'\hypersetup{colorlinks=true,',r'\hypersetup{pdftitle={The Thiele Machine},pdfauthor={Devon Thiele},colorlinks=true,')
s=s.replace(r'\section{Sources and mathematical dependencies}',r'\section{Sources}')
s=s.replace('These works provide the mathematical dependencies and intellectual background cited\nin the book.', 'These works are cited for their results, history and intellectual context.')
s=s.replace('construction is given in Section~\\ref{sec:universal-host} and\nSection~\\ref{sec:presented-universal}, and the counter and lambda references identify the\nestablished machinery under them.', r"""construction is given in Sections~\ref{sec:universal-host} and~\ref{sec:presented-universal}
and Appendices~\ref{sec:quoting-construction}--\ref{sec:universal-blocks}. The counter and
lambda references credit the established constructions.""")
s=re.sub(r'\n{3,}','\n\n',s)
(R/'working.tex').write_text(s);(R/'changes.json').write_text(json.dumps(changes,indent=2,ensure_ascii=False)+'\n')
print(len(changes),'substantive replacements; words',len(s.split()))
labels=set(re.findall(r'\\label\{([^}]+)\}',s));refs=set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}',s));print('Missing labels',refs-labels)
