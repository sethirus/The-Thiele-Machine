from pathlib import Path
import difflib
import hashlib
import json
import re

ROOT = Path(__file__).parent
SOURCE = Path('/workspace/The-Thiele-Machine-book-design/monograph/monograph.tex')
source = SOURCE.read_text()
edits = []

def add(title, reason, old, new):
    assert source.count(old) == 1, (title, source.count(old))
    assert old != new
    start = source.index(old)
    edits.append(dict(title=title, reason=reason, before=old, after=new,
                      start=start, end=start+len(old), line=source.count('\n',0,start)+1))

def between(title, reason, first, following, new):
    start=source.index(first)
    end=source.index(following,start)
    add(title,reason,source[start:end],new)

add('Opening list: state the scope without advertising the disclosure',
    'The following sentences already state the actual conditions.',
    'Proved, with every assumption printed, for any system with the named parts:',
    'Proved, for any system with the named parts:')
add('Short version: let the statement give its conditions',
    'The next sentence immediately supplies the conditions; the announcement adds no substance.',
    'The headline result is proved with every premise printed. With finitely many yes-states and',
    'The headline result is this. With finitely many yes-states and')

# Each repeated status tag is removed in its own exact source context.
for m in re.finditer(r'^.*?, all closed(?:\.|,).*$',source,re.M):
    old=m.group()
    add('Remove an “all closed” tag',
        'Keep the source reference and mathematical claim; remove the repeated software dependency status.',
        old,old.replace(', all closed',''))

add('Entropy bound: keep the source, cut the repeated library inventory',
    'The formalization’s foundations are documented once in Part V. This argument already states its mathematical conditions.',
    r'''\code{ax\_priced\_loss\_tight} (AxProb.v) and \code{ax\_inf\_loss\_bits} (AxInfinite.v). These use Coq's
real numbers, and they lean on four standard-library assumptions, all named in
Section~\ref{sec:coq}: the two decidability principles that come with the reals, functional
extensionality, and excluded middle.''',
    r'''\code{ax\_priced\_loss\_tight} (AxProb.v) and \code{ax\_inf\_loss\_bits} (AxInfinite.v).''')
add('L: remove the global-context badge',
    'The substantive point is that the diagonal argument is reproved for this model.',
    "That's the diagonal for a fixed model, closed under the global context, with its hypotheses in its statement.",
    "That's the diagonal for a fixed model.")
add('Diagonal summary: keep the transition about the mathematics',
    'Closure status does not explain how the machine instantiates the diagonal.',
    "That's the wall on paper, on a family built to fit it, and on one outside model, closed under the global\ncontext. The machine built in Part IV fills in this same shape, closed the same way: on",
    "That's the wall on paper, on a family built to fit it, and on one outside model.\nThe machine built in Part IV fills in this same shape: on")
add('Small-machine conclusion: retain only the source locator',
    'The preceding passage says what the machine establishes. Stop there, with a reference for readers who want the formal counterpart.',
    r'''The formal derivations of these results use no added axioms; each theorem still has
the hypotheses printed in its statement. The sources are EarnedCore.v and EarnedCoreLinks.v,
and Section~\ref{sec:coq} gives the assumption audit and the procedure for repeating it.
The base file uses only Coq's standard library; the link file adds the book's abstract
records and the library of undecidability proofs.''',
    '''The formal counterparts are in EarnedCore.v and EarnedCoreLinks.v.''')
add('Lift summary: one statement, without the closure badge',
    'Retain the reference without repeating dependency status.',
    'All of it is one closed statement too, if you want the whole chapter in one place.',
    'All of it is one statement too, if you want the whole chapter in one place.')

between('Replace the “zero Admitted” subsection with a short dependency note',
    'Remove the boast, the repeated denials, the theorem census, and the claim that zero project axioms defines every edition. Keep one accurate explanation of formal dependencies and where their detailed record lives.',
    r"\subsection{What ``zero Admitted'' means}",
    r'\subsection{What you\'re trusting, in one place}'.replace("\\'", "'"),
    r'''\subsection{Dependencies of the formal derivations}

The companion formalization uses Coq's logic and, in some results, standard-library
axioms: functional extensionality on dependent functions, two decidability principles
for the real numbers, and excluded middle. The report in the reproduction instructions
records these dependencies theorem by theorem. A theorem's own hypotheses are part of
its statement and must be read there; an empty dependency list does not remove them.

This inventory helps someone inspect the formal derivations. It does not establish that
the statements mean what the prose says, describe a physical device, or matter. Those
questions belong to the arguments and, for claims about the world, to experiments.

''')
add('Auditor description: describe its job without a virtue claim',
    'A check for missing derivations is a software rule, not an authorial accomplishment.',
    '''Beyond the type checker, the project has a custom proof auditor I called the Inquisitor,
because a thing that reads every proof looking for ways you've cheated deserves a name you
won't forget. It reads every proof file, and its source names about eighty distinct rules. The main
families: no holes (no Admitted, no admit, no give-up, no unproved axiom or parameter in
project code);''',
    '''Beyond the type checker, the project has a custom proof auditor I called the Inquisitor.
It reads the proof files for patterns that need inspection. Its main rule families cover
missing derivations and undeclared dependencies;''')
add('Reproduction instructions: remove the census from the prose',
    'The linked report already records its own coverage and revision.',
    '''The counts this book reports from the assumption audit (5,997 theorems in 341 files) are the ones
in that report, and they belong to that revision. A change to the proof sources beyond their comments and
layout changes the corpus digest; the audit then has to be run again and its counts read afresh.''',
    '''That report belongs to the identified revision. A change to the proof sources beyond their comments and
layout changes the corpus digest; regenerate the report before comparing a changed source tree.''')
add('Reproduction instructions: read the statement directly',
    'Keep the practical instruction without another closure-status slogan.',
    '''The run has to pass. Don't stop at the pass: read the theorem
types and their global dependencies, because a closed report doesn't make a theorem's own
premises go away.''',
    '''To inspect a result, read its full statement, its derivation and the definitions it uses.
The reproduction run checks the formal source; comparing that source with the argument on
the page remains a separate task.''')
between('Challenge the audit as a record, not as a headline theorem',
    'A discrepancy in a dependency report calls for correcting the report or inspecting the derivation; it is not by itself a counterexample to the mathematics.',
    r'\emph{The audit (Section~\ref{sec:coq}).}',
    r"\subsection{What's mine and what isn't}",
    r'''\emph{The audit (Section~\ref{sec:coq}).} Compare the report with the dependencies of the
source it names. A mismatch is a fault in the record to investigate. The Inquisitor's
findings are also reasons to inspect the source; neither a discrepancy nor a warning
by itself refutes a mathematical result.

''')
for first in ['Zero Admitted; a handful of standard assumptions &',
              "The small machine's files, the Thiele-complete files and the universal programs' files use no axioms &"]:
    line=next(line for line in source.splitlines(True) if line.startswith(first))
    add('Remove an audit-status row from the result ledger',
        'The ledger should summarize the book’s claims, not promote maintenance properties of the companion source into results.',line,'')
add('Conclusion: end the universal-machine result on what it does',
    'This sentence was retained by the previous pass and still gives the audit the last word.',
    '''programs it runs; $U$ and $U_P$ show a fixed interpreter can. The formal derivations of those results use no added axioms; the hypotheses of each
theorem are printed in its statement.''',
    '''programs it runs; $U$ and $U_P$ show a fixed interpreter can.''')
add('Conclusion: remove the axiom qualification from the game summary',
    'Use of real-number foundations is not a lesser grade of result to apologize for.',
    '''pass forces Tsirelson's bound for the tally it's handed. That one does use axioms, the standard
library's: functional extensionality and the two decidability principles of its real numbers,
because the bound is a statement about real numbers. And what the counter has to do with physics,''',
    '''pass forces Tsirelson's bound for the tally it's handed. And what the counter has to do with physics,''')
add('Conclusion: remove the second game dependency count',
    'The absence of a physical premise is explained by the definitions and argument, not an audit tally.',
    '''follow line by line, and the assumption audit on that link finds exactly three standard
axioms from Coq's own library (two that come with its real numbers, and functional
extensionality) and nothing of mine. The reason this is an algebraic claim is in its definitions''',
    '''follow line by line. The reason this is an algebraic claim is in its definitions''')
add('Glossary: define the terms without scoring the project',
    'A glossary can explain Admitted and Print Assumptions without repeating the project’s status.',
    '''proof and asks Coq to check the whole chain. Admitted is the keyword for ``I claim this
without proof,'' and it appears nowhere in the active tree. A Hypothesis inside a Section is a
named premise that becomes an argument of every theorem that uses it when the Section
closes; ``closed under the global context'' doesn't make it go away. Print Assumptions lists
the global axioms a theorem depends on; on the kernel tier it shows only standard-library
ones.''',
    '''proof and asks Coq to check the whole chain. Admitted accepts a statement without a
derivation. A Hypothesis inside a Section is a named premise that becomes an argument of
every theorem that uses it when the Section closes. Print Assumptions lists the global
axioms a theorem depends on; it does not list the hypotheses in the statement itself.''')
between('Assumptions appendix: point to the one dependency note',
    'Retain the existing appendix location but stop repeating the inventory and zero-project-axiom claim.',
    r'\subsection{The axioms of the checker itself}',
    '%===========================================================================\n\\section{What\'s mine, and what isn\'t}',
    r'''\subsection{Foundations of the formalization}

The companion formalization has logical dependencies in addition to the premises in
the table. Section~\ref{sec:coq} describes them and gives the report for each formal result.

''')

start=source.index(r'\section{Every result and where it is checked}')
end=source.index(r'\section{The exact words of twenty-one results}',start)
crosswalk=source[start:end]
old=r'''the Coq names that carry it, the file each lives in, and what the last full assumption
audit printed for it.'''
add('Result index: describe an index of sources',
    'Remove the promise of an axiom score beside every result.',old,
    '''the names of its formal counterparts and the file each lives in.''')
old=crosswalk[crosswalk.index('``none\'\' means'):crosswalk.index('``+N\'\'')]
add('Result index: remove the dependency legend and closure announcements',
    'The detailed dependency inventory remains in the linked report. The index keeps every result and its source.',old,'')
old="definition that states it, marked ``def''. A thesis has no Coq theorem name, because the book proposes it\nwithout claiming to have proved it; its formal schema is a definition, marked ``def''."
add('Result index: remove references to the deleted status column',
    'Definitions, premises and theses remain identified in the result names and explanation.',old,
    'definition that states it. A thesis has no Coq theorem name, because the book proposes it\nwithout claiming to have proved it; its formal schema is a definition.')
add('Result index: remove the residual status commentary',
    'The table points to arguments and sources. It no longer displays audit statuses.',
    '''arguments are in the numbered sections it points to. An audit status reports the
recorded check; running a later version does not change a claim in this book.''',
    '''arguments are in the numbered sections it points to.''')
table=crosswalk[crosswalk.index(r'\begin{longtable}'):crosswalk.index(r'\end{longtable}')+len(r'\end{longtable}')]
rows=[]
column_cells=[]
for line in table.splitlines(True):
    if ' & ' in line:
        cells=line.rstrip('\n').rsplit(' & ',1)
        assert cells[1].endswith(r'\\')
        column_cells.append(cells[1][:-2].strip())
        line=cells[0]+r' \\'+'\n'
    rows.append(line)
newtable=''.join(rows).replace(
    r'p{0.26\linewidth}p{0.07\linewidth}>{\raggedright\arraybackslash}p{0.45\linewidth}>{\raggedright\arraybackslash}p{0.11\linewidth}',
    r'p{0.32\linewidth}p{0.07\linewidth}>{\raggedright\arraybackslash}p{0.54\linewidth}')
assert newtable!=table
add('Result index: delete the Axioms column throughout',
    'The repeated “none” entries visually turn the index into an axiom scorecard. Keep every result, section reference, source identifier and file, in their existing order; use the freed width for the remaining columns.',table,newtable)
add('Exact CHSH statement: drop the repeated FE/RD explanation',
    'The comparison needs to explain what the theorem says; the dependency report remains available separately.',
    r'''and the converse that the three instructions certify exactly when the check passes, and the real
numbers in the statement are why it carries FE and RD, three standard-library assumptions in all, as printed in
Section~\ref{sec:crosswalk}.''',
    '''and the converse that the three instructions certify exactly when the check passes.''')

edits.sort(key=lambda e:e['start'])
for i,e in enumerate(edits):
    e['id']=f'F{i+1:02d}'
    if i: assert edits[i-1]['end']<=e['start']
proposed=source
for e in reversed(edits):
    proposed=proposed[:e['start']]+e['after']+proposed[e['end']:]
for env in ['theorem','lemma','proof','definition','corollary','proposition','observation','premise','verbatim']:
    pattern=rf'\\begin\{{{env}\}}[\s\S]*?\\end\{{{env}\}}'
    assert re.findall(pattern,source)==re.findall(pattern,proposed),env
for pattern in [r'\\(?:begin|end)\{[^}]+\}',r'\\label\{[^}]+\}',r'\\(?:clearpage|newpage)\b']:
    assert re.findall(pattern,source)==re.findall(pattern,proposed),pattern
for phrase in ['all closed','closed under the global context','Zero project-local','no added axioms','none of mine','no axiom of mine','zero Admitted','Zero Admitted']:
    assert phrase not in proposed,phrase
# No result or source cell in the reference table changes.
before_rows=[x.rsplit(' & ',1)[0] for x in table.splitlines() if ' & ' in x]
after_rows=[x[:-3] for x in newtable.splitlines() if ' & ' in x]
assert before_rows==after_rows
(ROOT/'proposed-manuscript.tex').write_text(proposed)
(ROOT/'proposed-edits.json').write_text(json.dumps(edits,indent=2,ensure_ascii=False)+'\n')
(ROOT/'proposed-edits.patch').write_text(''.join(difflib.unified_diff(source.splitlines(True),proposed.splitlines(True),fromfile='a/monograph/monograph.tex',tofile='b/monograph/monograph.tex')))
aux=(SOURCE.parent/'page-composition/build/book.aux').read_text()
refs=dict(re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]+)\}',aux))
def plain(s):
    s=re.sub(r'\\ref\{([^}]+)\}',lambda m:refs.get(m[1],m[1]),s)
    s=re.sub(r'\\(?:section|subsection|emph|texttt|code)\{([^{}]+)\}',r'\1',s)
    s=s.replace(r'\_', '_').replace('~',' ').replace('``','“').replace("''",'”')
    s=s.replace(r'\\','').replace(' & ',' | ').replace('$','')
    return '\n\n'.join(re.sub(r'\s+',' ',p).strip() for p in re.split(r'\n\s*\n',s) if p.strip())
review=['THE THIELE MACHINE — REMOVING THE AXIOM-STATUS REFRAIN',
        'Manuscript by Devon Thiele. Review draft; the working manuscript is unchanged.',
        'The previous pass removed some appeals to the checker but retained the repeated claims of no added axioms, even in replacements it proposed. That preserved the emphasis you objected to. This draft cuts the refrain instead of surrounding it with more qualifications.',
        'Keep the mathematical conditions where the arguments need them. Keep one short explanation of the formalization’s logical dependencies and the reproduction commands. Remove the counts, closure badges, status rows and repeated inventory from the narrative and conclusion.',
        f'{len(edits)} exact edit regions, including a column removed from {len(column_cells)-1} result-index rows. The result and source cells in those rows are unchanged. Two status-only rows are removed from the claim ledger. Two subsection titles change. Chapters and arguments remain in their existing order. Mathematical statements, proof blocks and literal reproduction/source blocks are unchanged.',
        'This is an editorial pass on this issue, not a fresh proof audit. It does not remove Coq sources or change the machine.']
wording=review[:2]
for e in edits:
    review += ['='*72,f"{e['id']}. {e['title']} — source line {e['line']}",e['reason']]
    wording += [f"{e['id']}. {e['title']} — source line {e['line']}"]
    if e['before']==table:
        note=f'Delete only the Axioms column from the complete {len(column_cells)-1}-row result index. Preserve every other cell and the row order. The full revised index is in the complete draft plaintext; the exact row changes are in proposed-edits.patch.'
        review += ['CURRENT: Result | Sec. | Coq name and file | Axioms','PROPOSED: Result | Sec. | Coq name and file',note]
        wording += [note]
    else:
        deletion='[Delete this status-only row.]' if ' & ' in e['before'] else '[Delete this passage.]'
        review += ['CURRENT:',plain(e['before']),'PROPOSED:',plain(e['after']) or deletion]
        wording += [plain(e['after']) or deletion]
(ROOT/'review-plaintext.txt').write_text('\n\n'.join(review)+'\n')
(ROOT/'proposed-wording-only.txt').write_text('\n\n'.join(wording)+'\n')
report=dict(edit_regions=len(edits),result_index_rows=len(column_cells)-1,
            result_and_source_cells_preserved=True,protected_math_and_literal_blocks_unchanged=True,
            labels_environment_sequence_and_explicit_breaks_preserved=True,
            source_sha256=hashlib.sha256(source.encode()).hexdigest(),
            proposed_sha256=hashlib.sha256(proposed.encode()).hexdigest(),
            working_manuscript_unchanged=SOURCE.read_text()==source,
            net_words_removed=len(source.split())-len(proposed.split()))
(ROOT/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
