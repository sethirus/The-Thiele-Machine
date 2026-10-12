from pathlib import Path
import collections
import difflib
import hashlib
import json
import re

ROOT = Path(__file__).parent
SOURCE = Path('/workspace/The-Thiele-Machine-book-design/monograph/monograph.tex')
source = SOURCE.read_text()
initial_hash = hashlib.sha256(SOURCE.read_bytes()).hexdigest()
primary = json.loads((ROOT/'tool-passages.json').read_text())
secondary = json.loads((ROOT/'secondary-passages.json').read_text())
passages = {p['id']: p for p in primary + secondary}
findings = []

def add(title, reason, replacements, category='Emphasis', original_number=None):
    changes = []
    for old, new in replacements:
        assert old != new
        assert source.count(old) == 1, (title, old[:100], source.count(old))
        start = source.index(old)
        changes.append({'before':old, 'after':new, 'start':start, 'end':start+len(old),
                        'line':source.count('\n',0,start)+1})
    findings.append(dict(title=title, reason=reason, changes=changes, category=category,
                         original_number=original_number, line=min(c['line'] for c in changes)))

def one(title, reason, old, new, category='Emphasis'):
    add(title, reason, [(old,new)], category)

def whole(pid, title, reason, new, category='Emphasis'):
    one(title, reason, passages[pid]['text'], new, category)

# Preserve the ten proposals Devon has already reviewed, verbatim.
for e in json.loads((ROOT.parent/'editorial-emphasis/proposed-edits.json').read_text()):
    add(e['title'], e['reason'], [(e['before'],e['after'])], 'Previously reviewed', e['number'])

add('Historical examples: stop borrowing authority from the shared tool',
    'These four comparisons repeatedly turn a historical argument into an endorsement of this book through its choice of software. Keep the people, work and historical facts; remove the shared-tool endorsement.', [
    ('''Per Martin-Löf, a Swedish logician whose type theory sits underneath the kind of proof checker that
checks this book,''', '''Per Martin-Löf, a Swedish logician,'''),
    ('''a proof assistant, the
same kind of tool that checks this book.''', '''a proof assistant.'''),
    ('''checked by Coq, the program that checks this book.''', '''checked by Coq.'''),
    ('''Coq, the same proof checker this book uses.''', '''Coq.''')])

one('The found-or-invented question',
    'The independence of mathematical discovery from this philosophical question does not need another appearance by the checker.',
    '''A proof checker doesn't settle
it either; Coq checks a proof the same whether you think the theorem was out there waiting or
you think you built it.''',
    '''A proof doesn't settle
it either: showing what follows from the premises doesn't decide whether you found the
theorem or made it.''')

one('What the reader gets to examine',
    'Proof terms are implementation objects. Here the book is inviting a reader to examine reasons.',
    '''The results in this book have statements,
premises, and proof terms.''',
    '''The results in this book have statements,
premises, and arguments.''')

one('The project’s scope',
    'State the actual kind of work rather than doubling the word checked and ending the description on the programming language.',
    '''a checked model and a checked machine, on paper and in Coq.''',
    '''a mathematical model and an abstract machine, with proofs of their properties.''')

add('The personal account: compilation is not the author’s central act',
    'These are first-person passages, so they are marked as voice choices for your review. They retain your authorship and the role of the models, while taking compilation out of the definition of what you do.', [
    ('''The symbol-pushing, the actual Coq and the actual math, the models produced and the proof checker judged. The proofs compile or they do not. I refused every one that did not.''',
     '''The symbol-pushing, the code and the formal derivations, the models produced. I used the checker to catch gaps in those derivations.'''),
    ('''Then the model gives me the symbols, the proof checker takes them or throws them back, and I refuse anything that will not compile or does not match the shape I am holding.''',
     '''Then the model gives me the symbols, and I refuse anything whose argument does not hold or does not match the shape I am holding.''')], 'Voice choice')

one('“The proofs you can’t fake”',
    'This absolute assurance undoes the paragraph’s own example of a vacuous theorem. Say what remains your responsibility without claiming the software makes fakery impossible.',
    '''The proofs you can't fake. The statements you can fake by accident, which is the more dangerous failure mode. I refused both kinds.''',
    '''An accepted derivation can still settle an empty question. I had to refuse that too.''', 'Accuracy and emphasis')

add('Repeated announcements that the next argument is checked',
    'These short asides accumulate into a second refrain underneath the arguments. The nearby source references and precise statements already report the formal counterparts. Remove the repeated announcement while keeping those references.', [
    ('''The checked version of the chairs is a theorem a few lines down,''', '''The precise statement of the chairs argument is a theorem a few lines down,'''),
    ('''Four more facts about the halving price, all checked, and the last one is a limit.''', '''Four more facts about the halving price, and the last one is a limit.'''),
    ('''One piece of it I can hand you, and it's checked.''', '''One piece of it I can hand you.'''),
    ('''Runs that mix different moves split two ways, and the answer is short enough to give here,
checked like the last one.''', '''Runs that mix different moves split two ways, and the answer is short enough to give here.'''),
    ('''Both are checked
now, and here's what each one says in plain words.''', '''Here is what each says, and why it holds.'''),
    ('''That's a theorem, and it's
checked in steps.''', '''That's a theorem. Here's the argument.'''),
    ('''Close enough to say exactly, in a limited form, and it's
checked.''', '''Close enough to say exactly, in a limited form.'''),
    ('''Two more pieces of the same count, both checked.''', '''Two more pieces of the same count.'''),
    ('''They are the same set, and that's checked, for strategies
on finitely many levels.''', '''They are the same set, for strategies
on finitely many levels.''')])

one('The file is not the standard of care',
    'Name the distinction directly instead of attributing the care to a source file.',
    '''One thing I have to say plainly, because the file is more careful than I'd like to be.''',
    '''There are three separate claims here, and I need to keep them apart.''')

one('The counter’s proofs and their source locations',
    'Lead with the arguments the reader just saw; retain every source identifier in this passage.',
    r'''Those two proofs are the whole of it, and they're about any counter machine. Coq checks them
over arbitrary states, as \code{nec\_f\_conservation}, with \code{nec\_f\_counter\_monotone} for
the climb, and \code{nec\_f\_initiality} (NecFCounter.v), and here they're on
the page, where you can check every line.''',
    r'''Those two proofs are the whole of it, and they're about any counter machine. They're on
the page, where you can check every line. Their formal counterparts over arbitrary states are
\code{nec\_f\_conservation}, with \code{nec\_f\_counter\_monotone} for the climb, and
\code{nec\_f\_initiality} (NecFCounter.v).''')

one('A proof the reader can inspect',
    'Rerunning software is one way to check a formal counterpart. This sentence is about the reader’s access to the reason.',
    '''and that its honesty is a proof you
can rerun yourself.''',
    '''and that its honesty rests on a proof you
can examine yourself.''')

one('Why the recursion result matters',
    'The important distinction is a derived recursion theorem versus an assumed one. A global-context status is not what makes the model exist.',
    r'''And the one where the recursion theorem is \emph{proved} from the rules, closed under the global context, which is why it exists:''',
    r'''And the one where the recursion theorem is \emph{proved} from the reduction rules rather than assumed:''')

whole('S131', 'The checker’s proof outside the machine',
    'This paragraph says the proof cannot be moved inside and invokes Gödel and Löb as the reason. Later the book explicitly says keeping it outside is a design choice and that these theorems do not forbid checking proofs about checkers. Bring the earlier passage into agreement with that narrower statement.',
    r'''Push on that and it gives, because a receipt is only as good as whoever wrote it. Its trust rests
on the checker meaning what it says, and that gets settled once, from outside the machine.
That's where I chose to stop this machine's chain of reasons. Gödel's second theorem does not
forbid a machine from checking a proof about a checker. It limits a sufficiently strong,
effectively axiomatized theory's ability to prove its own consistency, if the theory is
consistent. Eliezer Yudkowsky and Marcello Herreshoff's 2013 draft on agents that trust their
own rewrites describes a related problem, the Löbian obstacle: how an agent can justify
trust in a successor's proofs. The relation is worth examining, but it does not prove that
my design is forced. So I didn't get rid of the receipt somewhere. I moved it out of the
machine and handed it to whoever reads the record.''', 'Accuracy and emphasis')

add('An argument without a separate formal counterpart',
    'The existing wording tells the reader to discount this argument because it has no checked theorem. Preserve that information without treating it as the measure of the argument’s weight.', [
    ('''One more thing falls out of the same picture, and it's a short argument with no checked
theorem behind it, so take it at that weight.''',
     '''One more thing follows from the same picture, by a short argument.'''),
    ('''I haven't checked this in Coq, and I'm not claiming more than the paragraph
says.''',
     '''There is no separate formal derivation of this argument; the claim is exactly what this
paragraph says.''')])

one('Why this base was usable',
    'Keep the practical benefit of reusing an identified construction, without making being in a Coq library the criterion for the machine’s significance.',
    '''And I care because it's the smallest universal base I know of that is
already in a Coq library, so the hard part (proving that its halting question is
undecidable) is someone else's checked work. I don't have to ask you to take my word for it.''',
    '''For this construction I can reuse the two-counter result in the Coq Library of
Undecidability Proofs. The halting reduction is their work; the step-for-step connection
to this machine is the part I have to establish.''')

add('The price unit comes from the model’s choice of whole numbers',
    'The previous paragraph correctly says the unit is a choice. The next paragraph makes Coq’s successor notation sound like an additional justification. Keep Dedekind and Peano, and make the actual mathematical consequence clear.', [
    ('''Where does that one come from, though? It's older than Coq by about a century.''',
     '''The whole numbers have a history of their own.'''),
    ('''Coq builds
its whole numbers exactly that way, out of zero and ``the next one'' and nothing else, so inside
Coq the number three really is S (S (S O)), the next of the next of the next of zero. What that
changes here is small and I like it: the one a CHECK costs isn't a number pulled from a hat.
It's one application of the smallest step the number system has. You can't charge less than one
S and still charge something.''',
     '''Start from zero and take ``the next one'' three times, and you have three.
Once the prices are whole numbers, one is the smallest positive price. Choosing whole-number
prices, and choosing that unit for CHECK, are still choices of this model.''')], 'Accuracy and emphasis')

one('What establishes the checker’s meaning',
    'The lemma is the reason. Its external checking procedure does not need to be repeated in the sentence identifying it.',
    r'''Lemma~\ref{lem:u34-eval}, a proof about the little program the step calls, checked once by Coq
and priced by nothing on the ledger.''',
    r'''Lemma~\ref{lem:u34-eval}, a proof about the little program the step calls,
priced by nothing on the ledger.''')

one('The states differ whether or not software distinguishes them',
    'The difference is already given explicitly. Ending on Coq turns an elementary distinction into a tool achievement.',
    '''one has a fact in its table and its flag up, and the other doesn't, and Coq
tells them apart in a line.''',
    '''one has a fact in its table and its flag up, and the other doesn't.''')

one('Which premise has been discharged',
    'The recursion theorem has been established; the remaining conditions on the property have not disappeared.',
    r'''And with the recursion theorem proved, the wall of Section~\ref{sec:diagonal} goes up on this
machine without a premise left over.''',
    r'''And with the recursion theorem proved, the wall of Section~\ref{sec:diagonal} goes up on this
machine without assuming that theorem as an extra premise.''', 'Accuracy and emphasis')

one('The comparison with Schroeppel’s proof',
    'Keep the limitation on your reading of the earlier paper. A checked status is not a substitute for comparing the two arguments.',
    '''I haven't followed his proof line by line; this one is checked.''',
    '''I haven't followed his proof line by line, so the comparison stays at that level.
The argument here is the one given above.''')

one('Borrowing a theorem does not cost “nothing in certainty”',
    'Using the same proof assistant makes the formal dependency usable in the project. It does not make the dependency disappear or independently establish its intended meaning.',
    '''Their proof is checked by the same proof assistant as mine, so leaning
on it costs me nothing in certainty.''',
    '''Their theorem is a dependency of this construction. Its statement and hypotheses
still have to match the use I make of it.''', 'Accuracy and emphasis')

one('The running-status table',
    'The table summarizes tests, not a proof of agreement over all runs. Match the qualification already given in the surrounding chapter.',
    '''The small machine & run: Coq, extracted OCaml and Python agree on every step''',
    '''The small machine & run: Coq, extracted OCaml and Python agree on every tested step''', 'Accuracy and emphasis')

one('What is proved equal before extraction',
    'The equality proofs concern the functions supplied to extraction. They do not independently verify extraction, compilation or the executable.',
    '''First, the code
that runs is the code the theorems are about.''',
    '''First, the functions
supplied to extraction are the ones the theorems describe.''', 'Accuracy and emphasis')

one('Popularity is not an extra correctness argument',
    'Keep the trusted dependencies and the ability to inspect the small local pieces. Remove the appeal to age and popularity as a reason to believe the run.',
    '''Coq's extraction, the OCaml compiler, the C tools and the integer library are old and used by a lot of people. The mapping
lines, the drivers and the comparing code are mine, and they're small enough to read in one sitting. That's a reason to trust it. It isn't a proof.''',
    '''The mapping
lines, the drivers and the comparing code are mine, and they're small enough to read in one sitting.
Their behavior, and the behavior of the tools they call, remain part of what the tests have to examine.''')

one('What a single execution tells you',
    'A run can expose a fault, so “would never show it” is too strong. The valid point is that execution alone does not prove fidelity to the specification.',
    '''A run
of extracted code only tells you the extracted code agrees with itself. If the extraction, or one of
the integer mappings, or a driver had slipped somewhere, a run on its own would never show it.''',
    '''A run
shows what that build did on those inputs. It does not by itself establish that extraction,
the integer mappings and the drivers implement the definitions correctly.''', 'Accuracy and emphasis')

one('Agreement between implementations',
    'The comparison can expose discrepancies on tested runs. Neither independence nor the probability of a shared mistake is established by the described tests.',
    '''When they agree on every step of thousands of programs, a
slip in the extraction, the integer mappings or the drivers would have to be matched by the same
slip in a machine written separately by hand to hide. I can imagine that happening. I can't imagine
it happening often.''',
    '''Comparing every step of thousands of programs can expose a
slip in the extraction, the integer mappings or the drivers. Agreement on those runs leaves
untested runs open, and a shared mistake can survive both implementations.''', 'Accuracy and emphasis')

one('The compiler’s heading',
    'The heading should name the route the chapter builds. This changes only a heading’s wording, not its position, level or contents.',
    r'\subsection{A compiler, all in Coq}',
    r'\subsection{From source programs to the host}', 'Voice choice')

one('What each compiler stage establishes',
    'Describe the guarantee instead of twice naming the language in which it is written.',
    '''Every stage is a Coq function with a Coq proof:''',
    '''Each translation stage has a proof that it preserves the program's result:''')

one('The calorimeter’s physical assumption',
    'The issue is an assumed physical relation, not the lack of a Coq statement.',
    '''so it also assumes the bath receives what the
register loses, and no Coq says that.''',
    '''so it assumes the bath receives what the
register loses. That physical relation is not established here.''')

one('The checking chapter’s heading',
    'Name the chapter’s job in relation to your work. The location, section level and label stay unchanged.',
    r'\section{What Coq is, and why}',
    r'\section{What the checks establish}', 'Voice choice')

whole('T140', 'The checking chapter’s opening',
    'Introduce the limited task given to the software instead of presenting its language as an exceptional source of authority.',
    '''Coq is the tool I used to check the formal derivations. A statement and a proposed
derivation are written in a precise language, and the checker tests whether the derivation
follows the system's rules from its definitions and assumptions. The rest of this section
says what that check covers, what it depends on, and what it leaves for us to read.''')

whole('T141', 'The name-and-renaming digression',
    'This is the longest passage whose subject is the tool’s identity. Recommend shortening it to the information readers need to identify the companion sources. It is an authored digression, so this cut is marked as a voice choice, not a factual correction.',
    '''The companion formalization uses Coq 8.18. The project was renamed the Rocq Prover in
March 2025; this book uses the older name to identify the version its sources were checked with.''', 'Voice choice')

add('The types-as-claims explanation',
    'Keep the explanation of the proof representation, while avoiding the suggestion that all types are claims or that writing definitions in a language guarantees nothing was smuggled into them.', [
    (r'''In Coq, types are
\emph{claims}.''', r'''In Coq, a claim can be written as a type, and a proof of it as a value of that type.'''),
    ('''The numbers, lists and states this book uses are all defined that
way, inside the system, so the foundation is explicit; nothing is smuggled.''',
     '''The source gives the definitions of the numbers, lists and states used here,
so you can inspect exactly which objects the formal derivations concern.''')], 'Accuracy and emphasis')

whole('T143', 'What an accepted derivation establishes',
    'Compilation can succeed with an admitted statement, and a vacuous claim is not literally meaningless. Explain acceptance, assumptions and the translation problem accurately, without making either compilation or its rejection the definition of truth.',
    r'''The checker tests a proposed derivation against its statement, under the definitions and
assumptions it uses. Admitted skips the derivation and turns the statement into an assumption;
the file can still compile. That is why a successful build alone does not show that every
claimed result has been proved. Even a complete derivation can settle the wrong question.
A statement can be true for an empty reason, such as a condition nothing satisfies.
Whether it expresses what I meant remains my responsibility.
\hyperref[sec:point]{The point} said a short version of this: the source names identify
formal statements and their derivations, and the sentences around them are my account of
what those statements establish. Comparing the two means reading the definitions, the
premises and the conclusion. The checker does not do that reading for us.''', 'Accuracy and emphasis')

one('Repeated closed-status assurances in the audit explanation',
    'Keep the audit counts, file coverage and reproduction instructions. Condense the repeated reassurance that two printouts said the same thing.',
    '''Each also ends by printing the assumptions of
every headline theorem in it, and every one
of those lines says the theorem is closed. A lemma a closed theorem uses is closed with it. So for those files every headline
theorem is closed under the global context, resting on no axiom of mine or of the standard
library, and two separate printouts say so. That isn't the same as having no premises: each
theorem keeps the hypotheses written in its own statement.''',
    '''Those files also print the assumptions of their headline theorems. Both those
printouts and the full audit report no added axioms for these results. That does not remove
the hypotheses written in each theorem's statement.''')

one('What the trust list is a list of',
    'Separate the dependencies of the formal checks and physical applications from the validity of a readable mathematical argument.',
    '''If you accept every checked theorem in this book, here is what you're still taking on trust,
all of it, so you don't have to collect it from five chapters.''',
    '''Here are the dependencies of the formal checks, the executable tests and the physical
interpretations, in one place, so you don't have to collect them from five chapters.''')

one('The stale bytecode-use census',
    'The paragraph says “332 files in the audit”; this edition’s receipt says 341. The related counts 44 and 267 have not been re-established in this pass. Remove the stale census, retaining the actual dependency explanation and the independent-checker procedure. Do not silently substitute 341 while leaving the two subset counts unverified.',
    r'''Of the 332 files
in the audit, 44 call \code{vm\_compute} themselves, and 267 reach the machine one way or the
other, because the standard library's arithmetic deciders (\code{lia}, \code{nia}, \code{lra},
\code{nra}, \code{psatz}) check their certificates on it;''',
    r'''The build uses it both through explicit calls to \code{vm\_compute}
and through arithmetic deciders (\code{lia}, \code{nia}, \code{lra},
\code{nra}, \code{psatz}) that check certificates on it;''', 'Stale description')

one('The auditor’s “pedigree”',
    'An import rule is a project constraint, not a source of intellectual authority.',
    '''or it doesn't
get to claim the kernel's pedigree''',
    '''or it fails
the project's dependency rule''')

one('What establishes that the bound is algebraic',
    'An assumption report lists formal dependencies; it cannot determine what a symbol means physically. Keep the dependency facts and attach the conclusion to the definitions and argument.',
    '''and nothing of mine, which is how anyone can see
that no physics was smuggled in.''',
    '''and nothing of mine. The reason this is an algebraic claim is in its definitions
and the argument: no premise identifies the counts or matrices with a physical device.''', 'Accuracy and emphasis')

one('What the learning appendix was for',
    'The narrative milestone is building the argument, not getting the proofs to compile. Marked as a first-person voice choice.',
    '''By the time the
proofs compiled I'd needed enough of half a dozen of
them that I had to put down somewhere what those fields had words for.''',
    '''By the time the
argument had taken shape I'd needed enough of half a dozen of
them that I had to put down somewhere what those fields had words for.''', 'Voice choice')

one('Tactics build derivations',
    'A tactic is an instruction to the proof-building machinery; its execution is not itself the logical reason a theorem holds.',
    '''A tactic is a step inside a proof:''',
    '''A tactic is an instruction for building a formal derivation:''', 'Accuracy and emphasis')

one('The operating-system meaning of kernel is used after all',
    'The proof-carrying-code discussion uses kernel in the operating-system sense at line 10198. Replace the contradictory claim that this meaning is never used.',
    '''Third, the
operating-system kernel, which I never use and mention only so you know it isn't meant.''',
    '''Third, the
operating-system kernel, the core of an operating system, as in the packet-filter example
in Section~\\ref{sec:models}.''', 'Accuracy and emphasis')

one('Bennett and the four-state example',
    'Keep the credit and the modest scope. The point of the example is the distinction it makes visible, not getting software to agree with Bennett.',
    '''Bennett did the hard part in 1982; I built a toy with four dots on it and got Coq to agree
with him.''',
    '''Bennett did the hard part in 1982; my four-dot example puts the difference between
learning and committing where you can work through it yourself.''')

one('The grade/counter appendix is behind the main chapter',
    'The appendix says there is no checked theorem. The main chapter cites NecFGrade.v, which contains the grade, loop-cost, no-fixed-grade and input-grade theorems. Correct the status and keep the qualifications on the structured language and the chosen loop.',
    r'''On loop-free programs the counter agrees with a fixed
grade exactly, and where a run's cost depends on its data it holds the exact number that a fixed
grade can only bound; that's argued in Section~\ref{sec:counter}, with no checked theorem
behind it, and cost-aware
type theories such as calf get exactness back with grades that depend on the inputs.''',
    r'''For the well-graded, loop-free programs defined in Section~\ref{sec:counter}, on runs
that do not trap, the counter's rise equals the fixed grade. The loop built there costs
its input value, so no fixed whole number is its exact grade on every input; an
input-dependent grade is exact. The arguments and their formal counterparts are given
there (NecFGrade.v). Cost-aware type theories such as calf allow grades that depend on
the inputs.''', 'Stale description')

one('The closing account of the contribution',
    'The size of a mechanization is not an additional result. State what those arguments connect.',
    '''Under all four sits a
large body of mechanized proof that
ties those statements to one small machine and the programs that run on it.''',
    '''The proofs connect
those statements to one small machine and the programs that run on it.''')

add('The crosswalk’s legend',
    'A definition can use parameters and assumptions; “def” is a kind of entry, not a claim of independence. Also distinguish proposing a thesis from proving it.', [
    ('''``def'' marks a definition, which
has nothing to assume.''', '''``def'' marks a definition rather than a theorem; its parameters and any assumptions
on them remain part of what it defines.'''),
    ('''A thesis has no Coq name, because the book states it
and doesn't claim it;''', '''A thesis has no Coq theorem name, because the book proposes it
without claiming to have proved it;''')], 'Accuracy and emphasis')

one('The crosswalk is an index, not the authority over all prose',
    'A stronger claim needs a further argument. Its absence from one formal statement does not, by itself, make it false. Preserve the requirement that any claimed restatement be faithful.',
    '''No row is meant to say more than its Coq names, and where the prose does,
the prose is wrong.''',
    '''Where a row claims to restate a formal result, it must preserve that result's scope.
Any stronger claim needs a further argument, and the row must say where that argument is given.''', 'Accuracy and emphasis')

one('How to compare the printed statements with the source',
    'Matching the list of premises alone is not enough, and reading unfamiliar source syntax is not effortless. The comparison must include definitions, quantifiers and conclusions.',
    '''You don't need to read Coq to use this. Put
the printed theorem next to the block and check that every premise in the block turns up in the
sentence. That's the whole test.''',
    '''Each source block has a plain reading beside it. Compare the definitions, the premises,
the quantifiers and the conclusion with the printed theorem. Checking the translation
against the source also takes enough of its notation to follow those parts; matching
the list of premises alone is not the whole test.''', 'Accuracy and emphasis')

one('Why the bounded checker terminates',
    'Give the construction’s reason for termination: decoding terminates and execution has finite fuel. Keep the named formal result.',
    '''The checker answers on every input because it's a Coq function that always returns''',
    '''The checker answers on every input because decoding terminates and the routine runs for
at most the supplied finite number of steps''')

# Give the findings stable reading order, while keeping related cuts grouped.
findings.sort(key=lambda f:f['line'])
for i,f in enumerate(findings,1):
    f['id']=f'E{i:02}'

changes = sorted([(c,f['id']) for f in findings for c in f['changes']],key=lambda x:x[0]['start'])
for (a,aid),(b,bid) in zip(changes,changes[1:]):
    assert a['end'] <= b['start'], ('overlap',aid,bid)
proposed = source
for c,_ in reversed(changes):
    proposed=proposed[:c['start']]+c['after']+proposed[c['end']:]

# No manuscript is written. The patch is a review artifact only.
patch=''.join(difflib.unified_diff(source.splitlines(True),proposed.splitlines(True),
            fromfile='a/monograph/monograph.tex',tofile='b/monograph/monograph.tex'))
(ROOT/'all-proposed-edits.patch').write_text(patch)
(ROOT/'all-proposed-edits.json').write_text(json.dumps(findings,indent=2,ensure_ascii=False)+'\n')

aux=(SOURCE.parent/'page-composition/build/book.aux').read_text()
refs=dict(re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]+)\}',aux))
def plain(s):
    s=re.sub(r'\\ref\{([^}]+)\}',lambda m:refs.get(m[1],m[1]),s)
    s=re.sub(r'\\(?:section|subsection|emph|texttt|code)\{([^{}]+)\}',r'\1',s)
    s=re.sub(r'\\hyperref\[[^\]]+\]\{([^{}]+)\}',r'\1',s)
    s=s.replace(r'\_', '_').replace('~',' ').replace('``','“').replace("''",'”')
    return re.sub(r'\s+',' ',s).strip()

headings=[]
for m in re.finditer(r'^(?:\\phantomsection)?\\(part|section|subsection)\*?\{([^\n]+)\}',source,re.M):
    title=m[2].split('}')[0]
    headings.append((source.count('\n',0,m.start())+1,m[1],plain(title)))
def place(line):
    names={}
    for l,kind,title in headings:
        if l>line:break
        if kind=='part':names={'part':title}
        elif kind=='section':names.pop('subsection',None);names['section']=title
        else:names['subsection']=title
    if line >= 17580:
        names['part'] = 'Appendices' if line < 21261 else 'Sources'
    return ' / '.join(names.values())

for f in findings:
    f['location']=place(f['line'])
(ROOT/'all-proposed-edits.json').write_text(json.dumps(findings,indent=2,ensure_ascii=False)+'\n')

intro=f'''THE THIELE MACHINE — FULL EDITORIAL AUDIT OF PROOF-TOOL EMPHASIS
Manuscript by Devon Thiele. Review proposals only. No manuscript changes applied.

The first ten suggestions caught the most visible framing. The same pattern also appears
in the personal account, chapter transitions, the explanation of proof checking, the
implementation chapter and the appendices. This pass follows it through the entire book.

There are {len(findings)} grouped findings containing {len(changes)} exact replacements.
The original ten proposals are included unchanged and identified by their previous numbers.
Most replacements are short cuts or changes of emphasis. The first-person changes, two
heading changes and shortened name-history paragraph are explicitly marked VOICE CHOICE.
They are proposals for your judgment, just like the rest; no one has applied them.

Editorial principle: the argument carries the claim. The formalization is a companion
that can expose gaps in a specified derivation. Tool acceptance does not determine the
importance of the work, choose its definitions, validate its interpretation or confer
novelty. Conversely, having no separate formal counterpart does not refute an argument.

Scope and method: the complete 23,288-line manuscript was searched, from preamble through
the last bibliography entry. The review inventoried 319 tool/foundation-related paragraphs
and screened 294 additional candidate passages for the same framing without tool names.
Relevant passages were read in context, with follow-up reads around ambiguous statements.
The section coverage and dispositions are recorded in coverage.txt and passage-dispositions.tsv.
This is a manuscript-wide editorial audit of this issue, including nearby accuracy and
consistency problems. It is not a fresh verification of every mathematical derivation,
every historical citation or every claim of originality in the 282,043-word TeX source.

WHAT THE FULL PASS ADDS

1. Remove shared-checker endorsements from historical comparisons.
2. Stop treating compilation as the central accomplishment or the identity of the author.
3. Remove the repeated “and it is checked” refrain where the argument and source already follow.
4. Correct claims of certainty, infallibility, automatic totality and independence that the
   described tools or tests do not establish.
5. Make the checking chapter serve the argument; shorten the tool-name digression if you
   agree with that voice choice.
6. Let the appendices document the work without making source syntax the arbiter of all prose.
7. Correct stale descriptions where the book and its current companion sources disagree.

WHAT SHOULD STAY

“Gap-catcher. Not the proof. The proof is the argument.” Keep that paragraph exactly.
Keep theorem statements, proofs, hypotheses, mathematical definitions, formal source blocks,
source identifiers, genuine limitations, reproducibility commands, and attribution of prior work.
Keep the distinction between the machine's CHECK instruction and the external proof checker.
Keep the real-number assumptions and their per-result accounting; deleting them would hide
dependencies rather than improve the emphasis. Keep the honest distinction between runs that
were tested and constructions whose behavior is proved but which have never been run.
Keep the classification of contributions as known mathematics, synthesis, implementation or
mechanization where that is the actual contribution. Changing “mechanized” to “new” would
misrepresent the work. This audit recommends no such change.
Keep the historical discussions when they explain the machine or an argument. The particular
name-history cut below is a judgment about focus, not a ban on historical digressions.
Gallina does not occur by name in the current manuscript.

READING THIS REVIEW

Each entry gives its location, source line, reason, CURRENT wording and PROPOSED replacement.
Only the displayed span changes; surrounding text stays. Source lines refer to the unchanged
manuscript. Displayed section numbers are resolved from the existing book; the patch retains
the original LaTeX cross-references. Multi-location entries print every replacement separately.
No paragraphs or chapters are moved, and all existing paragraph boundaries remain in place.

CONTENTS
'''
for f in findings:
    tag=f' [earlier #{f["original_number"]}]' if f['original_number'] else ''
    tag+=' [VOICE CHOICE]' if f['category']=='Voice choice' else ''
    intro+=f'{f["id"]}. {f["title"]}{tag} — line {f["line"]}\n'

out=[intro]
for f in findings:
    out.extend(['='*76,f'{f["id"]}. {f["title"]}',
                f'Location: {f["location"]}',f'Type: {f["category"]}',
                ('Earlier proposal '+str(f['original_number'])+' — wording retained.' if f['original_number'] else ''),
                'WHY: '+f['reason']])
    for k,c in enumerate(f['changes'],1):
        if len(f['changes'])>1:out.append(f'PASSAGE {k} — source line {c["line"]}')
        else:out.append(f'Source line {c["line"]}')
        out.extend(['CURRENT:',plain(c['before']),'PROPOSED:',plain(c['after'])])

out.append('''NOTES ON THE ACCURACY FINDINGS

The grade/counter status is a confirmed stale sentence, not an inference from a passing build.
NecFGrade.v explicitly states nec_f_grade_exact, nec_f_grade_exact_small, nec_f_loop_cost,
nec_f_loop_no_fixed_grade and nec_f_loop_input_grade. Its definitions require well-graded
branches and the conservation hypothesis. The proposed wording keeps that restricted scope.

The 332-file denominator conflicts with the current receipt's files_probed value of 341.
The old 44/267 bytecode figures were not independently recomputed. The proposal removes the
unnecessary census and keeps the explanation of how the checking path uses bytecode.

The earlier Gödel passage conflicts with the book's later, explicit statement that keeping
the checker proof outside is a design choice. The proposal fixes that contradiction without
claiming self-verification has no limitations.

The operating-system use of “kernel” is present in the packet-filter discussion, despite the
glossary's claim never to use that meaning. The proposed glossary sentence identifies it.

There is a residual technical-reference load after these edits: theorem identifiers, the
crosswalk, exact source statements and reproduction instructions. Their presence is useful
and does not require enthusiasm for Coq. No proposal here relocates them or changes the
book's existing organization. Their visual weight remains a separate page-composition issue.

No mathematical theorem, proof source, release tag, repository commit or published artifact
has been changed by this review. The full proposed patch is supplied solely for inspection.
''')
(ROOT/'full-audit-plaintext.txt').write_text('\n\n'.join(x for x in out if x)+'\n')

reading=['THE THIELE MACHINE — PROPOSED WORDING ONLY',
         'Review proposals, not an edited manuscript. Nothing has been applied.',
         'This shorter copy contains the proposed wording at every location. The complete audit has the current wording, reasons, and coverage.']
for f in findings:
    reading.extend([f'{f["id"]}. {f["title"]}'+(' [VOICE CHOICE]' if f['category']=='Voice choice' else ''),
                    'Location: '+f['location']])
    for c in f['changes']:
        reading.extend([f'Source line {c["line"]}:',plain(c['after'])])
(ROOT/'proposed-wording-only.txt').write_text('\n\n'.join(reading)+'\n')

# Every inventoried passage gets a disposition, including material deliberately retained.
lines=['ID\tStart line\tEnd line\tPass\tDisposition\tReason']
for p in primary+secondary:
    end=p.get('end_line',p['line']+p['text'].count('\n'))
    linked=[f['id'] for f in findings if any(p['line']<=c['line']<=end for c in f['changes'])]
    if linked:
        decision=', '.join(linked);why='See exact proposed changes in the plaintext review.'
    else:
        decision='RETAIN in this pass'
        if p['line']>=21261:why='Bibliographic title, credit or source note; no tool-authority edit recommended.'
        elif p['line']<237:why='Preamble or source comment; no reader-facing tool-authority claim.'
        elif 'verbatim' in p['text'] or re.match(r'^(Theorem|Lemma|Definition) ',p['text']):why='Exact source/reproduction material; preserve literal content.'
        elif '\\begin{' in p['text']:why='Statement, table or structured reference; no framing edit recommended. Not a fresh proof audit.'
        elif p['text'].startswith('Checked as'):why='Specific source/assumption receipt, not a substitute for the preceding argument.'
        else:why='Screened for emphasis; describes an argument, scope, provenance, implementation or relevant history without a further edit recommended.'
    lines.append(f'{p["id"]}\t{p["line"]}\t{end}\t'+('tool/foundation' if p['id'][0]=='T' else 'wider framing')+f'\t{decision}\t{why}')
(ROOT/'passage-dispositions.tsv').write_text('\n'.join(lines)+'\n')

regions=[('Front matter',237,2210),('Part I: The picture',2211,3109),('Part II: The axiom',3110,5436),
         ('Part III: The logic',5437,10841),('Part IV: The machine',10842,16079),
         ('Part V: Checking it, and its edge',16080,17579),('Appendix A: Things I had to learn first',17580,17939),
         ('Appendix B: Every assumption in one place',17940,18060),('Appendix C: What is mine',18061,18451),
         ('Appendix D: Result crosswalk',18452,18781),('Appendix E: Exact statements',18782,20050),
         ('Appendix F: CHSH derivation',20051,21124),('Appendix G: Quoting construction',21125,21260),
         ('Sources and mathematical dependencies',21261,23288)]
cov=['COVERAGE — PROOF-TOOL EMPHASIS AUDIT','Whole manuscript searched; relevant prose and neighboring context reviewed.','The dispositions distinguish exact source material and retained references from proposed changes.','']
for name,lo,hi in regions:
    ids=[f['id'] for f in findings if any(lo<=c['line']<=hi for c in f['changes'])]
    cov.append(f'{name} (lines {lo}–{hi}): '+(', '.join(ids) if ids else 'No emphasis edit recommended.'))
cov.extend(['','SECTION MAP'])
sections=[(l,k,t) for l,k,t in headings if k in ('part','section')]
for i,(lo,k,t) in enumerate(sections):
    hi=next((l-1 for l,kk,tt in sections[i+1:] if kk=='section'),len(source.splitlines()))
    if k=='part':cov.append('\nPART: '+t);continue
    ids=[f['id'] for f in findings if any(lo<=c['line']<=hi for c in f['changes'])]
    cov.append(f'L{lo} {t}: '+(', '.join(ids) if ids else 'Retain for this issue.'))
(ROOT/'coverage.txt').write_text('\n'.join(cov)+'\n')

# Structural checks on the in-memory proposal, not a proof verification run.
def environments(s):return re.findall(r'\\(?:begin|end)\{[^}]+\}',s)
def blocks(s):return re.findall(r'\\begin\{(theorem|lemma|proof|definition|corollary|proposition|observation|premise)\}[\s\S]*?\\end\{\1\}',s)
assert environments(source)==environments(proposed)
assert re.findall(r'\\label\{[^}]+\}',source)==re.findall(r'\\label\{[^}]+\}',proposed)
assert source.count('\n\n')==proposed.count('\n\n'), 'paragraph boundary count changed'
assert re.findall(r'\\(?:clearpage|newpage)\b',source)==re.findall(r'\\(?:clearpage|newpage)\b',proposed)
for env in ['theorem','lemma','proof','definition','corollary','proposition','observation','premise','verbatim']:
    pat=rf'\\begin\{{{env}\}}[\s\S]*?\\end\{{{env}\}}'
    assert re.findall(pat,source)==re.findall(pat,proposed), ('changed protected block',env)
assert SOURCE.read_text()==source
stats={'source':str(SOURCE),'source_sha256':initial_hash,'source_lines':len(source.splitlines()),
       'source_words_whitespace':len(source.split()),'tool_foundation_passages':len(primary),
       'wider_framing_passages':len(secondary),'grouped_findings':len(findings),'exact_replacements':len(changes),
       'previous_ten_included_unchanged':True,'voice_choices':sum(f['category']=='Voice choice' for f in findings),
       'protected_math_and_verbatim_blocks_unchanged':True,'labels_and_explicit_breaks_unchanged':True,
       'paragraph_boundary_count_unchanged':True,'manuscript_written':False,'patch_applied':False,
       'source_sha256_after':hashlib.sha256(SOURCE.read_bytes()).hexdigest()}
(ROOT/'verification.json').write_text(json.dumps(stats,indent=2)+'\n')
print(json.dumps(stats,indent=2))
