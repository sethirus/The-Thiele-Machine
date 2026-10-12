from pathlib import Path
import json,re,difflib
R=Path(__file__).parent
old=(R/'before.tex').read_text(); edits=[]
def replace(tag,a,b,reason):
 assert old.count(a)==1,(tag,old.count(a))
 edits.append(dict(tag=tag,before=a,after=b,reason=reason))
def span(tag,start,end,b,reason):
 assert old.count(start)==1,(tag,'start')
 a=old.index(start);z=old.index(end,a)
 replace(tag,old[a:z].rstrip(),b.strip(),reason)
span('opening_purpose','The strongest thing in this book first,','Here\'s the whole thing before',r'''
Structure is something a machine can hold and act on. Which things belong together,
which change preserves a relation, which earlier act a later move depends on: those
can be part of its state and its rules. That is the commitment behind the Thiele
Machine. I want to take those relations apart, put them to work, and ask what survives
when the machine changes or when we look at it through a smaller window.

The way into that question is two computers with the same answer. The answer leaves
something out. We can give that difference a place in the machine, let the step
maintain it, and ask what an observer can recover and what a change costs. A record
of a checked claim will be the first case I work through. It gives the argument
something definite to stand on: states you can point at, moves you can follow, and
rules you can try to break.
''','Lead with structural state, operations and observation; introduce certification as a worked case, not the purpose of the book.')
replace('opening_transition',"Here's the whole thing before any of the careful parts. I'm going to start with one small picture,", "Start with one small picture. I'm going to",'Remove a competing whole-book synopsis after the new opening.')
replace('two_computers_relation',r'''One of them found
something out about your list and stood behind it. The other one is holding identical bits and found
out nothing.''',r'''The first compared the entries and checked their order. The second loaded the same
answer without doing either. The list is in order in both; the difference is what
each run did with it.''','Make the contrast concern the run and its relation to the object, not two grades of truth.')
replace('established_scope',r'''I'm going to call the difference \emph{established}. The first machine established that your list is
sorted. The second has the same answer and established nothing. The rest of this chapter is me
taking that one word apart.''',r'''I'm going to call the first run's relation to that answer \emph{established}: it
checked the order of this list. The second run has the answer without that relation.
The list's order is there either way. What can a machine keep of the difference
between the runs? The rest of this chapter takes that question apart.''','Define the opening contrast operationally without making the machine confer truth.')
# This anchor uses literal TeX quotation marks.
span('model_framing',"\\emph{What ``new model of computation'' means here.}", 'Which leaves a fair question hanging:',r'''
\emph{What ``new model of computation'' means here.} The Thiele Machine makes chosen
structural distinctions explicit in the state, the step and its cost. In the case
on the table, that includes which object a check concerned, which edition it saw,
and which later act may rely on it. A record keeps something of those relations;
a window determines how much an observer can recover. Change what is kept or what
the window shows, and you change which questions the resulting state can answer.
The computing base supplies the operations. The record adds no computable function.
''','Put the role of state and observation before the comparison of computing power.')
replace('every_program_role',r'''\emph{Which} programs the guarantee covers: this one becomes every one. Most of the rest of the
book is how far that ``every'' goes and where it stops.''',r'''\emph{Which} programs the guarantee covers: this one becomes every one. Here the
relation between a check and its object has a job in the machine: the step reads
it and refuses a commitment when it no longer fits. That is one concrete way to
make structure part of what the machine does.''','Explain what enforcement demonstrates instead of making it the destination of the rest of the book.')
span('short_version_summary',r'\emph{The book in one paragraph.}',"I didn't invent a machine.",r'''
\emph{The book in one paragraph.} The Thiele Machine is an account of computation
that holds structure in the state and makes its treatment explicit in the step.
Start with things and their relations, then ask which moves preserve them, which
lose distinctions, and which distinctions an observer can see. The worked core is
a state, a step rule, a cost for each move and a yes-or-no reading, with a toll on
turning that reading on. A ledger adds the costs; a window shows some of the state.
This small case lets us derive definite consequences: a permanent reading over
finitely many yes-states can only rise through a merge; a price on merges then
forces the toll. A window may hide that change and its price. Over any base, a
driven permanent record is a latch; records with more stages give a direction of
such readings. These are results about the pieces they name. Part IV gives them a
concrete form in a machine with six instruction kinds, where checks and commitments
are tied to the same edition of an object. The later constructions change the base,
join machines and run one inside another, asking what structure and accounting
survive. That is the route from the picture to the machinery. The five steps below
follow it, with the premises and the limits of each claim.
''','Replace the certification headline with the progression from structure through observation to implementations and composition.')
span('short_version_argument','What this book is. An argument, made with that model,',r'\emph{Holding a sorting',r'''
What this book is. An argument about what an account of computation should preserve.
An answer, a run and a view of a run keep different things. The sorter and the copier
make that difference visible; the model lets us ask exactly which distinctions a
description retains and what follows when it drops them. My proposal is to carry
those structural relations and their accounting in the step itself. Here is the
argument in five steps, each with where it stands.
''','Avoid describing Turing computation itself as unable to represent structure; state the proposal in terms of chosen descriptions.')
replace('vouching_is_local',r'''Whether vouching has a
price is the question the rest of the book takes up.''',r'''Whether that act has a price is the first accounting question the book takes up.''','Keep the vouching question as the first case rather than the scope of the whole book.')
replace('permanence_heading',r'''\emph{Establishing is not free.} If the step''',r'''\emph{Writing a permanent record.} If the step''','Make the prose heading match the conditional result instead of implying a general law of truth or discovery.')
replace('structural_reading_route',r'''Section~\ref{sec:toll}, Section~\ref{sec:a2-not-arbitrary}, Section~\ref{sec:latch},
Section~\ref{sec:smallest} and Section~\ref{sec:conclusion}.''',r'''Section~\ref{sec:structure}, Section~\ref{sec:toll}, Section~\ref{sec:a2-not-arbitrary},
Section~\ref{sec:windows}, Section~\ref{sec:latch}, Section~\ref{sec:direction} and
Section~\ref{sec:shadow-exact}. Then follow the construction in Section~\ref{sec:smallest}
through Sections~\ref{sec:every-model} and~\ref{sec:parts}, and the conclusion in
Section~\ref{sec:conclusion}.''','Make the suggested argument route include structure, observation, the direction, change of base and composition.')
span('straight_purpose',r'\emph{What this project is.}',r'\emph{The universal certification result.}',r'''
\emph{What this project is.} An account of the relations a computation carries,
the moves that act on them, and the views through which they can be read. The
smallest accounting case uses a yes-or-no reading and a toll; structural entitlement
adds an object, a checked relation and a history that earned it. The generic
flag-raising step pays to set a flag and checks nothing. In the earned version,
a checker establishes a stated property of a particular object, and the step
keeps that check tied to the edition it concerned. The model, the results under
its premises and the instructions of a particular build each have their own scope.
''','Present structural entitlement as a developed case and keep truth tied to the actual checked property.')
replace('universal_result_local',r'''\emph{The universal certification result.} The universal certification result is this: when the''',r'''\emph{The permanent-record result.} For the yes-or-no case, the universal certification result is this: when the''','Name the structural property before the certification interpretation.')
replace('structure_chapter_question',r'''The question this book is about lives in the gap
between the third and the fourth, and nothing in the kindergarten has shown you yet that
there's a charge in that gap. It's shown you there might be a place for one.''',r'''The first cost question I want to put to that structure lives in the gap between
the third and the fourth. Nothing in the kindergarten has shown a charge in that
gap. It has separated the acts well enough for us to ask.''','Make the transition to records a chosen investigation rather than a redefinition of the book.')
span('structure_to_toll','So that\'s where I am at the end of one word.',r'\part{The axiom}',r'''
So that's where I am at the end of one word. A grouping, the act of making it,
the information kept about it, and a commitment to rely on it are different things.
The blocks let you separate them with your hands. Now I want that separation in a
machine's state and moves, where we can ask what each act preserves and what it
costs. The next two sections take the smallest record I can give it, a yes-or-no
reading, put a price on its change, and ask which premises force that price.
A failure there would tell us something definite about that proposed cost. A success
would give us one case to carry into the wider questions of observation and structure.
''','Replace the claim that the entire book depends on pricing vouching with the actual transition from structure to a worked accounting case.')
span('toll_entry','I left you with a question I couldn\'t answer:', 'One thing about where the buckets went,',r'''
Take the distinction between arranging something and recording an act concerning it.
Give the record two positions, no and yes. I want to build the smallest thing that
could carry a bill for that change, on paper, with a pencil, write the bill into its
rules, and see what follows. Then we can ask whether that rule follows from anything
else. Keeping the case this small lets us see which part of the construction does
which part of the work.
''','Give the record construction a clear role in the structural inquiry without treating it as the purpose of all computation.')
replace('partition_result_scope',r'''That's what ``structural'' in this
book's subtitle means at the level of a theorem.''',r'''That gives the grouping itself a precise role in this part of the construction.''','Do not reduce every use of structural in the book to one certification theorem.')
# Additional edits are appended below before application.
span('pointer_entry',"Here's where I am. Over any base,",r'\subsection{The claim}',r'''
The structural results leave a choice open. A base-driven permanent record is a
latch on an event, and the event is free to choose (Section~\ref{sec:latch}, the two
cups on one die). Five real systems each picked a different one
(Section~\ref{sec:models}). For the worked case in this book I picked certification.
This chapter asks whether that choice has a reason beyond the construction: is there
something about how people and machines rely on records that selects this event?

I have a thesis, in the sense the Church-Turing thesis is one
(Section~\ref{sec:structure}): a claim tying defined notions to the world. Its fate
matters to that choice of event. The latch, the windows and the counting arguments
use their stated premises whichever event a system records. Here is the claim,
where I got it, what can be checked, and how to kill it.
''','Locate the pointer thesis as a proposed choice within the broader model; preserve its actual claim.')
replace('pointer_question_scope',r'''And which event to record is a thesis with a borrowed shape and a listed set of
refutations (Section~\ref{sec:pointer}).''',r'''For the choice of event, the pointer thesis proposes certification and lists how
that proposal could fail (Section~\ref{sec:pointer}).''','Keep a thesis about choosing an event from defining the purpose of the structural results.')
replace('accounting_uniqueness_scope',r'''The obvious question to ask of all that is whether the toll is the only way. A theorem saying so
would be the best thing this book could hold: a short list of requirements that any account of
what a step costs has to meet, whatever field it comes from, with the toll and the counter the
only accounting left standing. I looked for that theorem, and the answer I can give you is no, and''',r'''One accounting question remains: do the structural requirements select the toll
alone? A short list of requirements leaving only one price would settle that choice.
The requirements I tried do not do it, and''','Remove a second competing claim about what would matter most in the book; retain the counterexample and its consequences.')
span('small_machine_role','So the machine in this book is a small one.',r'\subsection{What the model actually asks for}',r'''
So the machine in this book is a small one. I want the state and every way of
changing it where you can inspect them. Six instruction kinds let us follow how a
check stays tied to an object, how a change makes it stale, and how the next move
uses that relation. Each kind takes operands, a counter or a property or a line to
jump to, so there are unboundedly many instructions. This is one construction of
the model; the theorems will say which facts depend on these particular choices.
Smallest, in this chapter's title, is my account of building it. No comparison
class, measure of size or proof of minimality stands behind the word.
''','Replace six instructions are the idea with an inspectable construction of the idea.')
replace('minsky_representation',r'''with the second bin as scratch space. It's slow. Exponentially slow. A
two-counter machine doing your taxes would finish sometime after the sun burns out. But
``universal'' is a claim about what's \emph{possible}. Pleasant doesn't come into it, and on that
claim two bins of pebbles are as strong as anything.''',r'''with the second bin as scratch space. That representation can turn a modest input
into an enormous pile, handled one pebble at a time. It is a way to establish
universality: the two bins can express every Turing computation under the encoding.
Here they give me a base whose ordinary moves are easy to inspect. The structural
results each say which properties of a base they need; Section~\ref{sec:every-model}
carries the earned layer to other bases under explicit interface conditions.''','Explain why the counter base is used; replace performance hyperbole with the actual representational cost and change-of-base scope.')
replace('u_runtime_scope',r'''And it's slow: every guest step unpacks the program number from the front,
on a machine where copying a number means moving it a pebble at a time.''',r'''This interpreter unpacks the program number from the front for every guest step,
and copies a number one pebble at a time. That determines the running time measured
in Section~\ref{sec:running}; the simulation result above compares the states and
ledgers at matching points.''','Keep runtime facts attached to the particular interpreter and distinguish the measured quantities.')
replace('up_runtime_scope',r'''PAYs. Nothing here is fast, and the compiler's packing is Minsky's, so it's slower still.''',r'''PAYs. The compiler also uses Minsky's packing. These choices determine the time
needed to realize the guest's charge on this host.''','State the implementation mechanism instead of a global verdict about the model.')
replace('encoding_limit',r'''\item \textbf{Slow, and fed directly.} Universality is Minsky's, with the inputs placed straight in
the counters. Getting from an arbitrary Turing machine to two counters goes through his
exponential packing, constructed in Appendix~\ref{sec:counter-constructions}, and nothing about it is fast.''',r'''\item \textbf{Encoding and running time.} The universality construction loads encoded
inputs directly into the counters. Its route from an arbitrary Turing machine uses
Minsky's exponential packing (Appendix~\ref{sec:counter-constructions}). That is the
cost of this route to the two-counter base. The lift to another base has its own
interface conditions, and an efficient implementation would need its own analysis.''','Bound the performance limitation without promising an efficient alternative or concealing the encoding requirement.')
span('running_role','Everything so far is theorems. A fair reader',r'\begin{center}',r'''
The constructions give exact rules for states and steps. This chapter asks how
executable implementations follow those rules. It builds the small machine twice,
once from the formal definitions and once separately, runs both, and compares the
whole state after each tested step. Then it runs the universal programs on guests
small enough to finish and source programs through the executable part of the compiler.

There are two counts to keep apart here. The ledger measures what the price list
charges; the number of interpreter steps measures the work this representation takes
to carry out the run. One guest step can take millions of host steps while adding
one mark to its ledger. The state comparisons test the implementation, and the times
tell us which demonstrations are practical on it. Here is what ran and what did not.
''','Frame execution as tests of particular constructions; distinguish structural ledger cost from interpreter running time before presenting benchmarks.')
replace('runtime_evidence',r'''certifies is proved. It isn't run. I'm not going to dress that up.''',r'''certifies is covered by the mathematical simulation argument, but this execution
has not been performed.''','Retain the important non-execution limit without making impracticality the rhetorical verdict.')
span('why_this_runtime','Why so slow? Because a fixed program on a machine of counters',r'\subsection{From source programs to the host}',r'''
The large counts come from this encoding and the unit operations used to read it.
They measure the work done by this interpreter. The structural comparison asks
whether the related states preserve the guest's computation, record and ledger;
the execution tests check that comparison on the cases in the table. Whether another
interpreter or another base realizes the same relations efficiently needs a separate
construction and a running-time analysis. Nothing in these measurements gives a
lower bound for all such realizations.
''','Explain exactly what the benchmark supports and what would be needed to generalize it.')
replace('compiler_runtime',r'''time. Counters are unary, and unary is slow, and the slowdown grows with the values. How it grows
with the size of the program I haven't measured.''',r'''time. This implementation's unit operations make the work grow with the values
being handled. I haven't measured how it grows with program size.''','Tie the observed overhead to its mechanism without suggesting a result about all machines of the model.')
span('chsh_role','But first, why is a quantum game in a book about records at all?',r'\subsection{The game}',r'''
What does this example contribute to the structural question? It separates the
counts, the relation they satisfy, the act of checking that relation and the record
kept of the act. A tally is written down for nothing on this machine. Its checker
uses integer arithmetic to decide a precise matrix condition. The step then ties
the passing check to this edition of the tally, and the earned chain costs three
marks, just as it does for a simpler claim. The mathematical depth of the condition
and the price of those three acts are different quantities. That makes this a useful
case to hold against the small examples.

The tally alone supplies no history of how it was obtained. A made-up tally can
pass the same arithmetic test as a played one. The claims here concern its numbers
and the machine's treatment of them; the guarantee paragraph below says exactly how.
''','Explain the quantum example through data, relation, action and record rather than introducing the whole book as about records.')
replace('ledger_proposals',r'''And then there's what I'm proposing. These are mine. They reach further than any theorem in
here, and nothing in the tables puts an unavoidable physical price on every observable change.''',r'''The proposal joining these results is to make structural relations and their
accounting part of the state and the step. The items below spell out that proposal
and a narrower choice within it, the pointer thesis about certification. They reach
further than the theorems; none puts an unavoidable physical price on every observable change.''','Give the proposal list a hierarchy while retaining every listed proposal and its status.')
replace('ledger_pointer_scope',r'''\item That certification is the event worth recording, which is the pointer thesis (Section~\ref{sec:pointer}).''',r'''\item Within the record construction, that certification is the event selected by the reliance criterion of the pointer thesis (Section~\ref{sec:pointer}).''','State the particular proposal using its actual criterion rather than making certification the global purpose.')
span('scope_proposal',"\\emph{What I'm proposing beyond that.}",'%===========================================================================\n\\section{Conclusion}',r'''
\emph{What I'm proposing beyond that.} A structural account of computation: the
relations it carries belong in the state, their treatment belongs in the step,
and a cost model is one part of that account. The permanent record supplies a
case we can take apart. The pointer thesis asks whether certification deserves
that record in the systems it describes. It can fail without changing the latch
or window arguments, which use no such selection criterion.

The larger proposal is about which distinctions an account of computation ought
to preserve. The constructions show particular ways to preserve them and what
follows under the stated premises. Their worth depends on the questions we need
the account to answer. If a program's log and a proof about that program recover
every distinction we need, that weakens the case for requiring the account in the
step. If a deployed system has good reasons for a wall or a penalty rather than
a toll, that weighs against the proposed pricing there. Those are ways to examine
the proposal, alongside the counterexamples that test individual theorems.
''','Separate the broader architectural proposal from the event-selection thesis, and keep meaningful ways to challenge each.')
# More conclusion edits follow.
span('conclusion_opening',"I started with one word and a machine I couldn't explain.", 'The question got an exact form in Part II:',r'''
Put the triangle, the cups and the two computers back on the table. Turning the
triangle preserves relations you can check with your fingers. Turning a cup records
an act; a row of cups can distinguish stages that one cup cannot. The two computers
can leave the same answer while differing in what they did to reach it. In each
case we had to say what the things were, which moves were allowed, which relations
survived, and what our way of looking could tell apart.

Part I gave that question its vocabulary: structure as relations among things,
kept under chosen changes, carried by whatever stuff, relative to a frame. A
partition supplied the smallest sorting by the ruler I chose. Making a grouping,
keeping it, checking it and standing behind it separated into different acts.
That gave me a case in which to ask how an account of computation could carry the
difference and price a change.
''','Return to the tangible structural inquiry, not the history of discovering a certification cost.')
replace('conclusion_case_transition','The question got an exact form in Part II: five parts, one rule, one theorem you proved at', 'The record case got an exact form in Part II: five parts, one rule, one theorem you proved at','Name the scope of the accounting construction in the conclusion.')
span('conclusion_construction','Part IV built one small machine, two counters and six instruction kinds,','Then a check worth earning,',r'''
Part IV made the relations operational. The small machine's state ties a checked
claim to an edition of a counter. Its step uses that tie: change the counter and
the old check no longer authorizes a commitment. From a clean start, a raised flag
therefore requires a passing check, a commitment about the same edition and a
certificate, in order. Three marks suffice and no such run pays less. These are
facts about the construction, including the case of a check that cannot fail.
Its two-counter base supplies universality under the stated encoding.

The universal programs ask whether those relations survive another machine doing
the work. On the host with more counters, $U$ runs the small machine's programs
from clean starts, matches halting and answers, earns its own flag exactly when
the guest raises one, and matches the ledger at corresponding points. With PAY
added, $U_P$ runs every computably presented Thiele machine, latches the guest's
reading through its own earned chain, and carries the guest's ledger with the
stated surcharge: at most two at the raise when the reading starts at no. The
simulation arguments describe which states correspond; the execution chapter
measures the time this particular representation takes.

Changing the base and joining machines ask the structural question more widely.
The lift works under its interface conditions, with counterexamples where those
conditions fail (Section~\ref{sec:every-model}). Side-by-side machines need both
records; a single total can lose which side acted. Sequential hand-offs and nested
runs each need their own conditions (Section~\ref{sec:parts}). These constructions
make us say which relation is carried through a change and which is lost. The
six instruction kinds are one place to inspect that work.
''','Give concrete construction, simulation, change of base and composition their respective roles; reduce repeated certification-detail dominance.')
span('conclusion_return','And the two computers from the first pages, the sorter and the copier,',r'\appendix',r'''
And the two computers from the first pages, the sorter and the copier, holding the
same list. Walk the warehouse again. The list is in order on both. On the machine
with the earned layer, a different part of the state tells you whether a check and
a matching commitment occurred. Its rules maintain the relation to the edition
that was checked. Cover that part of the machine and the distinction disappears
from your view. Change the counter and you can watch the old check become stale.
Those are different operations, with different consequences, and you can follow
each one.

A report carried out of the warehouse raises another question: what connects that
report to the machine? The flag alone supplies no answer. A window, a copying
operation, a second machine and a reader each introduce relations of their own.
The book's constructions ask explicitly which of them hold. That is how the
example reaches beyond the lamp: through what survives a change of view, a change
of state, or a change of machine.

So that's the Thiele Machine: structure held as state, acted on by a step, with an
account of the changes and a view that may keep or lose their distinctions. The
record and its toll give that proposal a worked mathematical core. The small
machine and its interpreters give us particular constructions to take apart.
The argument is for treating those relations as part of computation itself.
Each theorem answers a stated question under stated premises; the choice of which
questions an account ought to preserve remains there for you to challenge.
''','End on the structural proposal and its concrete operations; remove the claim that the certification lamp was the sole purpose.')

replace('five_models_question',r'''the one question this book is about: \emph{is there a price on the moment the record is written?}''',r'''the pricing question from the paper models: \emph{is there a price on the moment the record is written?}''','Keep the five-system comparison focused on its actual question without presenting it as the purpose of the book.')
replace('record_window_scope',r'''Now point the three escapes back at the record this book is about, because that's where they''',r'''Now point the three escapes back at the record we have been constructing, because that's where they''','Refer to the worked record rather than redefine the whole book by it.')
replace('change_of_base_role',r'''If it did, it would be a curiosity. The whole point of the opening chapter was that the second
computer is missing something \emph{any} computer could have. So this chapter tries to break that,
from both directions: the panel onto other boxes, and other boxes run inside mine.''',r'''The opening asked which distinctions the machine could carry in its state and
steps. Now we can ask which parts of that construction depend on the computing
base. This chapter works in both directions: the earned layer onto other bases,
and other bases run inside this one. The interface conditions will say exactly
what has to survive the change.''','Connect base-independence to the structural inquiry and its precise interfaces.')

# Verify and apply exact non-overlapping replacements.
spans=sorted((old.index(e['before']),old.index(e['before'])+len(e['before']),e) for e in edits)
for a,b in zip(spans,spans[1:]):assert a[1]<=b[0],(a[2]['tag'],b[2]['tag'])
new=old
for a,b,e in reversed(spans):new=new[:a]+e['after']+new[b:]
heads=lambda s:re.findall(r'\\(?:part|section|subsection|subsubsection)\*?\{([^}]+)\}',s)
assert heads(old)==heads(new)
assert re.findall(r'\\label\{[^}]+\}',old)==re.findall(r'\\label\{[^}]+\}',new)
for env in ('theorem','lemma','proposition','corollary','observation','definition','premise','conjecture','thesis','proof'):
 pat=r'\\begin\{'+env+r'\}(.*?)\\end\{'+env+r'\}'
 assert re.findall(pat,old,re.S)==re.findall(pat,new,re.S),env
labels=set(re.findall(r'\\label\{([^}]+)\}',new));refs=set(re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}',new));assert refs<=labels,refs-labels
p=Path('/workspace/The-Thiele-Machine-book-design/monograph/monograph.tex')
assert p.read_text() in (old,(R/'working.tex').read_text()),'Source changed outside this pass'
p.write_text(new);(R/'working.tex').write_text(new)
(R/'edits.json').write_text(json.dumps([e for _,_,e in spans],indent=2,ensure_ascii=False)+'\n')
(R/'changes.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='before.tex',tofile='working.tex')))
(R/'Changed-passages.txt').write_text('\n\n'.join(f"{i}. {e['tag']}\nReason: {e['reason']}\n\nBEFORE\n{e['before']}\n\nAFTER\n{e['after']}" for i,(_,_,e) in enumerate(spans,1)))
print(len(edits),'edits;',len(old.split()),'words before;',len(new.split()),'words after; headings, labels, mathematical statements and proofs preserved.')
