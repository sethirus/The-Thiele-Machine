What a machine can't decide about itself

In chapter ten I said you'd watch the same move get made again and again: somebody says
"everything is X," it's true enough to do real work with, and then somebody draws the
diagonal. I owe you the diagonal itself now. The last few chapters handed a box to any
machine that steps, and the next thing anyone wants from a machine with a box is for it to
tell sound shortcuts from unsound ones by itself. Before I let anything claim that, I have
to show you the wall every such claim runs into, and then exactly where a machine with a box
stands next to it.

It doesn't stand on the far side, because nobody's on the far side. A box keeps a
distinction and pays for it. What it can't do is the judging.


Five names and a table

Do this first, with a pencil, because the whole family of arguments is this one trick.

Write five friends' names down the left of a page. Next to each name, write a row of five
digits, each 0 or 1, anything you like. Now build a new row. Its first digit is the opposite
of the first digit of the first row. Its second digit is the opposite of the second digit of
the second row. And so on, down the diagonal. Look at what you've made. It differs from row
one in place one, from row two in place two, from every row at that row's own place. So it's
nobody's row. Your table of five missed something.

With five rows that's a cute fact. Georg Cantor made the point in 1891 that it works for any
list, however long, even an endless one: hand me a complete list of all endless rows of two
symbols, and I'll walk the diagonal flipping as I go and hand you back a row that's on no line
of your list. So there's no complete list. There are more rows like that than there are places
on any list, and that's where "some infinities are bigger than others" comes from. (He wrote
his two symbols as m and w, and that paper wasn't even his first proof of the fact. The first
was in 1874, by a harder road, and in 1891 he called the new one much simpler. The diagonal was
him finding the easy way.)

Now look at what the argument did, because it's going to happen again, in new clothes. There
was a table: rows are the things being listed, columns are questions, and each square says
"does row i do column j." There was the diagonal: the squares where a thing gets asked about
itself. There was a flip, something with no fixed point, like turning yes into no, applied
along the diagonal. And what got knocked down was the thing assumed at the start: the complete
list. Nothing outside the assumption was touched. A table, a diagonal, a flip, and the
assumption eating itself.


The same move, again and again

Russell, in 1902, from chapter ten: the collection of all collections that don't contain
themselves. That's Cantor's flipped diagonal with "contains" as the table, and Russell said as
much in 1903: he got there by running Cantor's argument on a supposed collection of everything.
What got knocked down was the assumed collection of everything, and Zermelo's fix was to stop
assuming it.

Jules Richard, a French mathematician who taught at schools in Tours, Dijon and Châteauroux, noticed
in a short note in 1905 that some phrases define numbers ("the ratio of a circle's circumference to
its diameter"). There are only as many phrases as there are whole numbers, so list the numbers they
define, run Cantor's diagonal down their decimal digits, and you get a number no phrase defines,
except that you just defined it, in the phrase that describes the diagonal. The lesson I take from
it is the one this whole chapter turns on: keep apart the language a system talks in and the language
you use to talk about it. Mix them and the diagonal bites you.

Richard's paradox has a cousin small enough to do at the table, and it comes with a footnote I can't
resist. Russell, the first to put it in print, in 1906, credited it to G. G. Berry, a junior librarian
at the Bodleian Library in Oxford. In the version in Principia Mathematica it's about syllables. Take
the phrase "the least integer not nameable in fewer than nineteen syllables." There are only so many
phrases shorter than nineteen syllables, so they name only so many numbers, so some least number is
left over, and the phrase picks it out. Now count the phrase: the, least, in-te-ger, not, name-a-ble,
in, few-er, than, nine-teen, syl-la-bles. Eighteen. In eighteen syllables it has named the number that
can't be named in fewer than nineteen. "Nameable" is a word about the language, used inside the
language, and that's where the bite is.

Kurt Gödel, 1931, with an improvement in 1936 by Barkley Rosser, a student of Alonzo Church, that lets
it assume only that the system doesn't contradict itself. Take any such formal system, with rules you
can check mechanically, strong enough to do some arithmetic. Then there are sentences it can neither
prove nor disprove. The engine lets you build, for any property you can write down, a sentence the
system proves equivalent to "my own code number has that property." Apply it to "not provable," and you
get a sentence equivalent, inside the system, to its own unprovability. The table is the sentences
listed by code number, the diagonal is a sentence about its own code, and the flip turns provable into
not provable. Two cautions, which the Stanford Encyclopedia stresses too: the sentence doesn't literally
"say" anything about itself; it's provably equivalent to a claim about its code, which is less mystical
and more exact. And the theorem doesn't say the sentence can't be known. It says this one system can't
settle it.

How did the world take it? Mostly, at first, it didn't. Gödel, twenty-four years old, announced the first
theorem in a round-table discussion on the last day of a conference in Königsberg in September 1930, and
by the account of Solomon Feferman, one of the editors of Gödel's collected works, the room met it with
general incomprehension, except for one man. John von Neumann pulled Gödel aside, kept thinking about it,
and a couple of months later saw that the argument gave something more: a system like that can't prove it
doesn't contradict itself. He wrote to Gödel with it in a letter dated 20 November 1930. Gödel had already
got there; his paper had reached the journal three days earlier with that second theorem announced in it,
and von Neumann left the credit with Gödel. It's "somebody got there first" again, except this time the
person who got there second was von Neumann.

Alan Turing, 1936. Chapter one told how what he actually proved differs from the halting problem as it's
taught. The taught version fits on two index cards. Card A is the Checker: hand it any program card and it
announces "stops" or "runs forever." Card B is the Contrarian: "Hand me to the Checker. If it says I stop,
run forever. If it says I run forever, stop." Hand B to A, and either answer is wrong. So there's no Checker.
The table is programs against programs, the diagonal is a program run on itself, and the flip turns stop into
loop.

Stephen Kleene, 1938, and this is the one that turns the paradox into a tool, so slow down. Everything above
needs the thing that refers to itself to exist: Gödel's sentence has to be buildable; the Contrarian has to be
able to "hand me to the Checker." Kleene's recursion theorem says: for any way of transforming programs that
you can compute, there's a program that behaves exactly as if it had been handed its own source code. Any
program may be written as though it already had a copy of itself in hand. He stated it almost in passing, in
a paper about something else, and proved it in the last two lines of one section. I have that count from
Yiannis Moschovakis, a logician who wrote a 2010 paper about it called "Kleene's Amazing Second Recursion
Theorem," and he calls it a little gem. It's why programs that print their own source code exist in every
ordinary programming language. Try one in English: "Print the following twice, the second time in quotes:
'Print the following twice, the second time in quotes:'" Obey it.

Those programs are called quines, and the name comes from Douglas Hofstadter in 1979, in Gödel, Escher, Bach,
in honour of the philosopher Willard Van Orman Quine, who had made a long study of self-reference that works
indirectly. Quine left a sentence you can take apart at the table, from a 1962 essay on paradox: "yields
falsehood when preceded by its quotation" yields falsehood when preceded by its quotation. Do what it says.
Take the part in quotation marks, put a quoted copy of it in front of itself, and look: it's the whole sentence,
word for word. So the sentence says that it itself is false. It's the liar paradox, built without any "this
sentence," just an instruction to quote and copy. Quoting and copying is Kleene's trick in plain English. The
paradox is what you get when the copy says something about its own truth. The tool is what you get when the
copy just does something.

Henry Rice, 1953, whom you met in chapter seven: the general form. Any question about what a program does,
not how it's written, that some programs pass and some fail, has no program that answers it for all programs.
"Does this program stop" is one. "Does this program ever print 7" is another. "Does this program contain the
word 'if'" isn't, because that's about the text.

And the one that's an attack. Ken Thompson, who built the original Unix operating system, gave a lecture
published in 1984. Build a compiler that, when it compiles the login program, plants a back door, and when it
compiles a compiler, plants both habits in that one too. Then delete the trick from the source code. The
compiled compiler still carries it, and recompiling a clean source with the poisoned compiler plants it again,
forever. Reading the source never shows it. Picture a locksmith who teaches an apprentice to cut a spare for
every town-hall key, and to teach that to every apprentice they train, and never to write it in the manual. Years
later the manual is spotless and every locksmith in town cuts the spare. Thompson's compiler is Kleene's trick
with a knife in it.

Thompson wasn't first either, and he said so: he wrote that he first read of the possibility in an Air Force
review of the security of an early operating system called Multics, and asked anyone who could find it to send
him the reference. It's Paul Karger and Roger Schell's 1974 security evaluation of Multics, which already described
a trap door planted in a compiler that keeps itself alive. Is there any way out? A partial one. David A. Wheeler,
in 2005 and in his 2009 dissertation, worked out a check: compile the suspect compiler's source with a second,
independently made compiler, use the result to compile that source again, and compare it bit for bit with the
suspect. If they match, under his stated conditions, the source and the binary correspond. Two compilers having
different authors is useful evidence, not a substitute for those conditions. The question has moved to a place
where we can name what we trust.

And Bill Lawvere, in 1969, proved a theorem that, as I read it, makes all of these one theorem in disguise: if
there's a function with no fixed point, a flip, then no thing can list every question about itself. Cantor,
Russell, Gödel and Turing all come out as cases. Noson Yanofsky retold it in 2003 without the heavy machinery. I
mention it because "it's the same wall" is a claim I make below, and it's fair at the level of the argument's shape.
Every case has its own fine print about who counts as a judge, and that fine print is exactly where most
overclaims live.


Where the diagonal gets misused

Before pointing it at a machine with a box, look at how it gets misused. Each time, the trouble is forgetting who
the judge is and what it has to judge.

"Gödel shows minds aren't machines." John Lucas, a philosopher at Oxford, argued it in 1961. Roger Penrose, the
Oxford mathematical physicist, revived it in two books, The Emperor's New Mind in 1989 and Shadows of the Mind in
1994. The standard replies, as far as I can tell, have held up: the Gödel sentence is true only if the system doesn't
contradict itself, so a person who "sees" it's true has to know that, which is the hard part; and nobody can build the
Gödel sentence of a system they can't write down, so people might be machines too complicated to diagonalise. The
theorem has an "if" in it, and the argument drops the "if."

The part that's easy to miss is that Gödel himself didn't go as far as Lucas. In a lecture on 26 December 1951, at a
meeting of the American Mathematical Society at Brown University, he drew only an either-or from his own theorems:
either the human mind infinitely surpasses any finite machine, even in pure mathematics, or there are questions about
whole numbers, of a certain simple kind, that no proof a human can conceive will ever settle. Feferman, writing about
that lecture, says Gödel privately believed the first half and still stated only the either-or, because he didn't have
a knock-down argument against the machine side. Gödel meant to publish the lecture and never did. So the man whose
theorem gets quoted for "minds aren't machines" stated an either-or and left the deciding to whoever came next. The "if"
is there again, kept by the person with the most right to drop it.

"Undecidable means unknowable." No. Two senses share the word: no single program that's right on every case, and a
sentence one particular system can't settle. Neither means nobody can know a given answer. Any single case is easy in
the first sense: for any one program, one of "say yes" and "say no" is right. What's ruled out is one inside procedure
that's right on every case.

"Everything interesting is undecidable." No. Rice is about what programs do, over all programs. It says nothing against
checking the text, nothing against answering for particular programs, nothing against checks allowed to say "I don't
know," nothing against checking finite machines. Real compilers and analysers live with Rice by being careful and
incomplete, and what limits them in practice is mostly cost.

"Self-reference is a paradox." It's a theorem with a construction, as Kleene, the quines and Thompson show.


Now point it at the box

Here's the question with nothing in it but what this book has built. A machine steps. A box rides along and turns up on
an event, chapter fourteen. When the event is "a check passed," chapter eight says the box lets you lean on a claim, and
for a claim that a shortcut is sound, that's what makes the shortcut usable. So: can a machine like that have, as one of
its own programs, a procedure that correctly decides, for every program, "does this program have a sound shortcut"? Call
that an autopilot: hand it any program and it says yes or no, and it's always right.

The exact claim is narrower than that question in plain words, so here it is first. "Has a shortcut" can be any question
about programs with two features: two programs that behave the same always get the same answer, and there's one program
that passes and one that fails. That's all the argument gets to look at. It doesn't see soundness. Whether a particular
question about shortcuts has those two features is a separate fact, checked one machine at a time. A procedure that only
answers for some programs, or needs outside evidence, isn't what the wall rules out.

And because the argument only looks at what programs do, not how, "shortcut" here is a label. A question like "is there a
cheaper program that gives the same answers?" isn't the argument's question. The nearest thing I know of is Manuel Blum's
speedup theorem from 1967, and it goes somewhere stranger: there are functions with no fastest program at all, where every
program for them has another that's faster on all but finitely many inputs. That's about cost, not deciding, and nothing in
this book proves anything there.

The answer is no, under conditions, and the proof is the two index cards. Suppose there were an autopilot that says yes
exactly when a program has a shortcut. Build the flip: "If the autopilot says yes about me, behave like the program that
fails; if it says no, behave like the one that passes." If the machine has Kleene's trick, so a program can be handed its
own code, and if that flip is something the machine can run, and if the question only depends on what programs do, and if
there's one program each way, then there's a program that behaves exactly like its own flip. Ask the autopilot about it. If
it says yes, the program behaves like the one that fails, and behaving alike means getting the same answer, so it fails: the
autopilot was wrong. If it says no, the program behaves like the one that passes, so it passes: wrong again. Those are the
only two answers.

Look at what that used: Kleene's trick, the flip being runnable, the two examples, and "behaves alike, answers alike." It
never touched the tally, the toll, or the box. It's Rice's trick one floor over, with its own conditions, so it isn't Rice's
theorem word for word, and it says nothing about whether this question is harder or easier than the halting problem.

So the wall is there. The honest part is who counts as the judge. The argument rules out a judge whose flip the machine
itself can run. It says nothing about a judge standing outside. An outside judge can exist for the very same question,
right on every program. The line between inside and outside is Richard's lesson: the language you talk about a system in
isn't the language it talks in.


What this does to the book

It does two things. It keeps me honest: nothing in this book claims a machine with a box can check its own shortcuts on
autopilot, because that's a wall, the same wall, and I've shown you the bricks. And it tells you what a box can do instead:
it can carry a shortcut along with its receipt, so that "was this earned?" is answered by a step you can point at. No judge
has to exist for that, which is lucky, because on a machine with Kleene's trick no inside one can. The diagonal says the
judging can't be automated from inside. The cup says the commitment can be recorded. Different jobs, and a box does the
second.

The diagonal has a famous cousin that looks like it ought to bite a box too. Gödel's second theorem says a system strong
enough for arithmetic that doesn't contradict itself can't prove that it doesn't, and Martin Löb sharpened that in 1955: if
such a system proves "if this is provable, it's true," it already proves the thing itself. So can a box vouch for itself, and
does Löb stop it?

You might guess yes, since a box looks like a system talking about itself. It lands somewhere else, and mostly it's a
relief. Hold two things side by side: "there's a receipt for this somewhere," and the receipt in your hand. Löb's theorem is
about provability, the bare claim that some proof exists somewhere. A raised box isn't the receipt in your hand either. From a
clean start, chapter eight says a check passed before the raise. The box doesn't say which claim, and it doesn't hold a proof of
it. Sergei Artemov's line from chapter eight, between "there's a proof" and "this is the proof," is useful here, but a box doesn't
turn one into the other. The trust in this book comes from a proof about the checker, the clean start and every move, made
outside the machine. It isn't a proof inside the machine that the machine is sound, so it doesn't get around Gödel or Löb.

Push on that and it gives, because a receipt is only as good as whoever wrote it. Its trust rests on the checker meaning what it
says, and that gets settled once, from outside. That's where I chose to stop this machine's chain of reasons. Eliezer Yudkowsky
and Marcello Herreshoff's 2013 draft on programs that trust their own rewrites describes a related problem they call the Löbian
obstacle: how a program can justify trusting its successor's proofs. It's a cousin of this question, it doesn't settle it, and it
doesn't make my design the only possible one. So I didn't get rid of the receipt somewhere. I moved it out of the machine and handed
it to whoever reads the record.

One more thing follows from the same picture, and it's short enough to check by hand. Can a box rest on itself, the way the sentence
"this sentence is certified" would like to? Not if it's established and permanent. The check behind the raise happened while the box
was still down, because the box goes up only after that check passes. And once up it never comes down, so it goes up only once. So no
claim whose truth needs the box already up can be the claim the box went up on. Saul Kripke's 1975 theory of truth calls a sentence that
only ever leans on itself ungrounded, and established boxes are grounded in his sense: every one bottoms out in a check that didn't lean on
it. Caspar Oesterheld's 2019 work on programs that cooperate by simulating each other needed a grounding step of the same kind to stop an
endless regress.


Two walls

One last distinction, because the two are easy to run together, and running them together is the easiest way to misread this book.

There's a second wall, nothing to do with the diagonal. It's chapter seven's: two states that differ in their box can give the same view
through a window that doesn't let the box through, and then no reader of the window can get the box back. That wall comes from missing
information. Nothing about it is undecidable. It holds for small finite things with nothing to compute. Rice isn't underneath it.

So there are two walls, on two different axes. The diagonal is about what no inside procedure can decide. The window is about what no outside
watcher can see. The book needs both, and I'll try not to call one by the other's name.
