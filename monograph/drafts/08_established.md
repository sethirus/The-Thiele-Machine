Established

The last chapter ended at a whiteboard. Give a worker a whiteboard and a pen, and
ask for an answer with a line underneath that says "CHECKED = YES." The worker can
write both. So can somebody who copied the answer and checked nothing. The extra
line tells you nothing about which one happened.

This chapter is about what it takes for that line to mean something. It's the case
page one called the sharpest, and it's sharp because the two answers are the same
bits, and everything that differs is in what was kept.


Two computers that end up the same

Put two computers on a table and hand each one the same list of a thousand
numbers.

The first one sorts it. It compares, swaps, walks the list again and again until
nothing is out of order. Then it does one more thing: it walks the whole list front
to back and checks that every number is no bigger than the one after it. That check
could have failed. It passes. Then the computer tidies up after itself, wipes its
scratch work, and leaves the sorted list in memory. (That check is about order. Whether the list still holds your thousand numbers and no others is a second
question, and it would take a second check.)

The second computer never looks at your list. Somebody typed the sorted version in
earlier, the same thousand numbers in the same order, and it puts them in memory.

Now wait until both are done and read what's left: the list, the working registers,
where each one is in its program. Arrange for both to stop at the same point in the
same program and clear their scratch work, and all of that can agree. The first
compared the numbers and checked their order. The second loaded the answer and did
neither. Wheel the boxes out, swap them, and bring them back. From what's left,
neither of us can tell which run happened.

Be careful about what that does and doesn't say. It doesn't say every atom of two
real computers matches; the room, the heat, a clock or a saved log might still carry
evidence. And an ordinary computer can keep a "checked" flag or a log that can't be
changed. These two were set up so the difference got wiped from what you can read.
That choice, and what it stops the next reader from answering, is the example.

Who cares? Anybody who's been handed a sheet that says "all tests passed." Anybody
who's looked at an inspection sticker on a windshield: the sticker looks the same
whether somebody checked the brakes or somebody sold the sticker. An audit, a proof,
a ledger, an AI that sounds very sure of itself: each one is a pile of bits that
could have come out of either computer, and the question that matters is the one
the bits can't answer. Did something establish this, or did it just print it? I'll
come back to every one of those at the end of this chapter and say which ones this
book actually helps with, and it's fewer than you'd hope.


Look harder

The obvious answer is: look at everything, not just the end. So make the computers
as easy to look at as computers get. Scale them up to the size of a warehouse, every
wire a lamp that's lit or dark, every switch something you can walk up to and touch.
Nothing is hidden in a chip too small to see. Put them side by side and walk the
floor.

While they run, you'd see the difference: one has a whole wing lighting up,
comparing and swapping, and the other just copies. But they finish, and the
comparing wing goes dark. Walk the floor now and look at every lamp. The sorted list
is spelled out in lit and dark lamps in both, the same pattern, and everything else
is dark in both, because both cleaned up.

There's no lamp anywhere that says "a check ran here and passed." It isn't hidden,
and it isn't scrambled. It just isn't there. Looking harder doesn't help, because
the problem was never that you couldn't see enough. Nothing was kept.


So keep the trace

Then don't let the run go. Keep the trace: every comparison, every swap, the check
and its answer, written down as it happens. Wheel the computers out and back, read
the traces, and you'll know which one sorted.

It's the right instinct, and it gets most of the way. But it has three problems.

First, a trace is bits, and bits can be typed in. Whoever typed the sorted list into
the second computer can type a trace in too: "compared, swapped, checked, passed," a
few thousand lines of it, every one of them believable. A trace a program writes is
something the program produced. Keeping it doesn't answer the question. It moves it:
did something establish this trace, or did it just print it?

Second, the way out of that is to take the pen away from the program. Don't let the
program write its own trace. Have something underneath it write the trace, one step
at a time, as the steps actually happen, so nothing a program does can add a line
that didn't happen or erase one that did. Airplanes do a version of this. Flight
recorders go back to a prototype David Warren built in Melbourne in the 1950s; he
was an Australian scientist at the Aeronautical Research Laboratories, working on
jet fuel, and after a string of unexplained airliner crashes he wanted a box that
would hold the instrument readings and the voices in the cockpit for whoever came
looking afterwards. I know his story from museum and encyclopedia accounts, not his
own report. What comes out of a recorder is evidence of what its channels carried,
as long as the recorder and its sensors worked. A recorded reading can still be wrong
about the airplane. The recorder has the right shape, though, and that shape isn't
mine. In computer security it's called a reference monitor, and I'll come back to it.

Third, you can't keep everything. If every tick of a run can go either of two ways,
then after n ticks there are 2 to the n possible histories, and a fixed number of
bits eventually can't tell them all apart. Flight recorders make a practical choice
here: a voice recorder loops, replacing the oldest sound when it's full. Thirty
minutes, two hours, twenty-five hours: the window depends on the aircraft and the
rule, and the FAA's 2026 rule stretches it to twenty-five hours for certain new
aircraft. Whatever the length, it's a window.

The fingerprint is the sharpest answer to that, so take it seriously. Fold every new
line of the trace into a short scramble of everything before it, and you've got a
hash chain. Haber and Stornetta's timestamps work that way, from chapter four; so do
the audit logs Bruce Schneier and John Kelsey designed in 1999, and the measurement
registers in the security chip a lot of computers carry. That really does keep
something about the whole trace in a few dozen bytes. But look at what it keeps: a
binding, not the content. To read the history you still need the trace stored
somewhere, and the fingerprint only tells you whether a copy somebody hands you is
the one that went in. It holds only because nobody knows how to find two traces with
the same fingerprint, which is a bet on how hard a search is, not a law of nature.
Moni Naor and Guy Rothblum proved a sharp version of that in 2005, and even called it
a fingerprint: checking a big file somebody else stores, against an opponent with
unlimited computing, costs on the order of the whole file, and doing even slightly
better against a weaker opponent needs exactly that kind of bet. And squeezing
endlessly growing traces into a fixed number of bits has to land many traces on one
fingerprint. That's two arrows meeting, hidden behind how hard it is to find which
ones. It's a very clever way of forgetting, not a way out of it.

So the real question was never "save everything." It's: what's the smallest thing
worth keeping for good, and what does keeping it take? Not every comparison the sort
made. Just the one fact that a check of this very claim passed and the question got
closed. And keeping even that one fact for good takes something, on every machine:
two arrows meeting, or fresh paper forever. That's chapters one and two.

So it was never true that computers can't keep records. They keep records all day.
What nothing in an ordinary computer's rules does is make a record paid for,
permanent, and earned. Those come in at different places. Paid for is the toll.
Permanent is in the definition: a Thiele machine's settled answer never goes back.
Earned, meaning a check of this very claim passed first, isn't in the definition at
all. It's what this chapter adds.


More boxes to tick

Go back to the sorter. It checked the order of the list. Did it also check that
none of the numbers went missing? The list can be the same whether that second check
ran or not. One lamp saying "checked" won't tell you which work was done.

So put a sheet beside the scratch work, with a box for each check you care about:
one for order, one for "nothing missing," and so on. When you come back you want to
know which boxes got ticked.

Count what that takes. Say four checks would pass on this list. Each one can be run
or skipped. That's two choices, four times over: sixteen different sheets, all
sitting behind the same list. Two of them that differ on even one box can't be the
same state of the machine, because asking about that box would need two answers. So
the machine needs room for all sixteen behind that one list. In general, it's two to
the number of checks that would pass, for every list, added up over the lists. And
you can build a machine with exactly that much room and no more: keep the list and
the sheet, clear the sheet whenever a new list is written, and tick a box only when
its check passes.

Look at one small piece of it, because the arrows meet there too. A list that's true
or false, and one check. Three states: false; true and unchecked; true and checked.
The check takes "true and unchecked" to "true and checked," and leaves "true and
checked" where it is. Two arrows, one landing place, right above the same list.

Now keep the old sheets when the list gets wiped and reused. Think of carbon copies
filed before each sheet goes in the bin. On each of n rounds you can choose to check
or not. Bring every round back to the same final list. Then ask about any round you
like: was that one checked? Two histories that disagree on any round need two
different states, however alike the final list looks. That's 2 to the n states for n
rounds. Keep asking for one more round, with the same freedom and the right to ask
about every one, and no finite amount of room is enough. That's where the endless
paper comes from: not from keeping one answer, but from keeping a file of answers
that never stops growing.

Ask the file a smaller question, "was anything ever checked?", and it becomes a single
box that only goes up. That's the kind of record a Thiele machine keeps.


Computed, stored, established

Three words get used like they're one.

Computed is about the steps. The first computer computed the sorted list. The second
didn't.

Stored is about the bits. Both stored it.

Established is neither, and that's the whole problem. It isn't the steps, because
they're gone. It isn't the bits, because they're the same. It's this: whoever reads
the first computer has a right to lean on "this list is in order," because a test
that could have failed was run on this very list, it passed, and then the question got
closed. The second computer has the same sentence and no right to it. That's a true
fact about the two of them, and it's written down nowhere, in either one.

Four words, and I'll hold them still from here on. A check is the test, the thing that
could say no. A commit is the closing: the question shut for good, about that version
of that thing. The record is whatever stays behind to say so. And established, in the
sense a machine can carry, is all three, about one thing.

What if the second computer, handed the typed-in list, runs the check on it? Then it
has what the first had, and if it closes the question and keeps the record, it has
established the list is in order. It didn't sort and doesn't need to. The line here is
between checked and unchecked, not between worked hard and didn't. Whatever this book
counts, it isn't effort.


The clerk who forgets everything

The picture of a computer in chapter one was a person with a pencil, a strip of paper
and a short list of rules, and Turing's 1936 paper takes it a long way. He's careful
with the clerk's mind: whatever the clerk knows, beyond a handful of states, has to go
down on paper. Then he goes all the way. He imagines the clerk getting up, walking off,
forgetting everything, and coming back later. To pick up where he left off, the clerk
leaves himself "a note of instructions," and Turing says that note is the clerk's
state of mind, as far as the computing goes. Marks on paper and a note are the whole
state.

The two computers are sitting right inside that. Suppose the clerk didn't write the
note. Somebody slipped it under the door, in the right form, with the right
instructions. He comes back, reads it, carries on, and every mark he makes from then
on is exactly what he'd have made if he'd written it himself. Turing's model can't
tell the clerk who did the work from the clerk who was handed a note saying he did. It
was never asked to. Turing wanted something you could check without crawling into
anybody's head, and a note on a desk is as checkable as it gets. That's why the paper
still works ninety years later. A Turing machine could keep a note of who wrote the
note, and rules about who's allowed to. This one just doesn't.

So the founding picture of computing is a man who leaves his desk, forgets everything
he was doing, and trusts a sticky note. I relate to him deeply.


Information doesn't have it either

The next guess is information: one computer got some, the other didn't. That one dies
fast. Claude Shannon, who turned information into a number in 1948, says on his first
page that the meaning of a message is "irrelevant to the engineering problem." His
measure depends on the chances of the possible messages, and the same message from the
same set of chances gets the same number whichever computer it came from, or if one of
them got hit by lightning and came out right by luck.

Fine, forget the set of messages and look at the one string. In the 1960s three people
separately worked out how to measure the information in one string: Ray Solomonoff,
who was after a theory of guessing what comes next; Andrei Kolmogorov, the great Soviet
mathematician; and Gregory Chaitin. Their measure is the length of the shortest
program that prints the string. The two computers hold the same string and get the
same number. And running a program can't add much of that kind of information: what
comes out can't hold more than what went in plus the program, give or take a little.
Leonid Levin, who studied under Kolmogorov, proved a general version, and has a line
for it that's too good not to repeat: you can torture an uninformed witness all you
want, you won't get information about the crime.

That doesn't say sorting tells a person nothing. A person in a hurry can read the
smallest number straight off the first slot of a sorted list. Short descriptions,
useful access, and a record that a particular check ran are three different things.

Logic says the same thing in a different coat. The standard logic of knowing, the one
Jaakko Hintikka worked out in 1962, has a property called logical omniscience: if you
know some facts, you automatically know everything that follows from them. So by that
logic, once you knew every number on your list, you already knew whether it was in
order. Hintikka flagged the problem himself, and people have been trying to fix it
ever since. The fixes read like a pile until I asked each one the same question: when
it lets you write "known" next to "in order," what does it make you write in the
margin? Hintikka's margin is empty. Each fix writes one thing there.

The closest one to me is Sergei Artemov's, from 1995. He wanted a logic that could
name the proof itself: you only get to know a thing if you've built an actual reason
for it, and the reason travels along with the claim. That's almost a record. Almost,
because nothing in his margin says the reason was ever run, or when. Others taught it
to count. Ho Ngoc Duc, in 1997, made knowing take steps of reasoning, and Artemov and
Roman Kuznets, in 2014, asked how big a reason can get before knowing by it stops being
practical. Francisco Bavera and Eduardo Bonelli, in 2018, turned it into a programming
language whose terms carry the history of the computation that made them, and Samuel
Bucheli, Meghdad Ghari and Thomas Studer, in 2017, put reasons on a time line where
they last and change.

Line those up against what this chapter wants in the margin: earned, paid for,
permanent, and placed at a step in the run. Artemov's reason is nearly earned. The
counted versions put prices on reasoning. The time line gives dates. What none of them
has is the closing of a question as a single step with a price on it. Push on mine,
though, and it gives twice. Artemov's margin holds the reason itself, and mine only
says a check passed. And their prices grow with how hard the thing was to know; this
book charges the step that closes the question, and how long the checking took never
enters it. For a measure of effort, read theirs.

And yet you know something after the sort that you didn't before. You can stop
worrying. Something happened, and it's the first solid clue: whatever established is,
it isn't new bits. It's the same bits, settled: a question sorted into yes and no, with
yes made to stay.


Statues that walk off

If it isn't in the information, maybe it's in the knowing, so I went and read the
philosophers. They'd been arguing about the difference between having the right answer
and knowing it for a couple of thousand years.

Plato's version is a joke about statues. There was a story that the sculptor Daedalus
made statues so lifelike they'd walk off if you didn't tie them down. True beliefs,
Plato says in the Meno, are like that: they wander off, and they're not worth much
until you tie them down with the reason why. Once they're tied down, they're knowledge,
and they stay put. Knowledge tied to a reason, and knowledge that stays.

Then in 1963 Edmund Gettier broke the tidy version in three pages. Smith and Jones are
up for the same job. Smith has good reason to think Jones will get it, and he's counted
the coins in Jones's pocket: ten. So Smith figures, with good reason, that the man who
gets the job has ten coins in his pocket. Then Smith gets the job, and, without knowing
it, Smith also has ten coins in his pocket. Smith had a belief that was true and backed
by a reason, and it still wasn't knowledge. He was right by luck, because his reason was
about the wrong pocket.

That's the push that matters for a machine. Checking one pocket and closing the question
about another is right by luck. So whatever a machine closes, the check behind it has to
be about this very claim, and here's exactly what that means. Four things.

It checks the same property the commit names, not a cousin of it.

It checks that property on the same thing the commit names, not the thing next to it.

Nothing has written to that thing between the check and the commit, so it's still the
same version the check looked at.

And the check is honest: it says yes when the property holds and no when it doesn't, on
anything it could ever be handed.

Break the first three and you're Smith with his ten coins. Break the fourth and the
check is a rubber stamp. Two notes on those. The fourth asks a little more than it needs:
to rule out luck, a check only has to never say yes when the property is false. And the
third is a very old bug in computing wearing Gettier's coat. Security people call it
time-of-check to time-of-use: check a file, use it, and something swaps the file in
between. Matt Bishop and Michael Dilger wrote up how to hunt for it in 1996. Databases
guard against the same thing by making sure, just before a commit, that nothing they
read has been written since; H. T. Kung and John Robinson called that optimistic
concurrency control in 1981. A philosopher's pocket and a programmer's race condition
are the same bug. One limit, said now: a machine can only promise "nothing has written
to that thing" about its own memory. For brake pads or a voter roll, that condition
becomes an assumption about whoever measured.

Does anything fix Gettier for good? People tried for years. The first patch was "no
false steps in the reasoning." Then the philosopher Alvin Goldman came back with barns,
crediting them to Carl Ginet. You're driving through a county that, without your
knowing, is full of fake barns, just painted fronts propped up to look real. You look at
the one real barn and think "that's a barn." It's true, you believe it, you have a good
reason, your own eyes, and there's no false step anywhere. And you were still lucky: if
you'd glanced at the next one over you'd have believed the same thing and been wrong.
Every patch gets a new barn. What I keep from that: whether a check was good isn't only
about this one case. It's about what the check would have done on the cases next door.


What "could have failed" means

I keep saying the first computer's check could have failed. The computer is
deterministic. Given your list, the check was always going to pass. So in what sense
could it have failed?

Here's the sense. Hand the checking step a list that's out of order, and it says no.
That's all. Chance has nothing to do with it. A check splits every possible input into a
pile it says yes to and a pile it says no to, and "could have failed" means the no pile
isn't empty. A check that says yes to everything has an empty no pile. It tells you
nothing, however long it runs. The philosopher Robert Nozick made a version of this a
condition for knowing, in 1981: you know a thing only if, had it been false, you
wouldn't believe it.

Notice that "could have failed" is about what the check would have done on other lists.
It's not a fact about the finished state at all. Look at the first computer's memory: a
sorted list. Nothing in those bits says "and whatever made me would have caught a
mistake." That's exactly why the only way a machine can own this is to write something
down at the moment the check passes, and have that something mean what it says. Even
then the record only carries half of it. It can say a check ran on this version and
passed. That the check would have said no on a bad list is a fact about the checker, and
that half rests on a proof about the checker, made once, outside any run.

Rig a check to pass only on your one list. Is that cheating? No. It's an honest check of
a different claim: "this is that exact list." Its no pile is huge: every other list. It
establishes exactly that and nothing more. A check establishes what it's honest about.

And one thing I'll say plainly now: nothing here stops you from asking a question that
can't come out no, like "is this number at least zero." Ask one, pay for the check and
the close, and nothing is established but the record of asking.


Computing already had a word for it

Computing already has a word for this and uses it every day. Anyone who's used a
database has seen it: COMMIT. A database does a pile of tentative work, and then there's
one moment, the commit, written to a log, after which the change counts.

Jim Gray, who more or less built the theory behind that, opens his 1981 paper on it by
saying the idea comes from contract law, and his example is a wedding. People negotiate,
somebody asks, two people say "I do," and from then on it's binding. If it was a mistake,
you don't erase it. You do another transaction to fix it, the way a bad contract gets a
second contract.

The wedding was a philosopher's example first. J. L. Austin, lecturing at Harvard in
1955, said "I do" makes a marriage; it doesn't describe one, and sayings like that aren't
true or false. They can misfire: the wrong person says it, a step gets skipped. A commit
works the same way. Writing the commit record doesn't report that a question got closed.
Writing it is the closing. It can't be false; it can misfire, by closing without the
check, or about the wrong pocket. Then somebody else reads the record, and for them it
turns into a report, "this was checked and closed," and a report can be false. That's how
a commit gets tied to the truth: through a check, and no further than the check reaches.

Robin Milner, building a proof checker in the 1970s, ran out of memory, so he decided to
keep only the finished theorems and throw the proofs away, like a teacher rubbing out the
blackboard to make room. The obvious worry is forgery: if the proofs are gone, what stops
someone from just writing a theorem down? His answer was beautiful. Theorems got their own
type in the programming language, and the only way to make one was through the rules of
logic. You couldn't forge one because the language wouldn't let you build it any other
way. He named that language ML, for Meta Language. I wanted to call my machine the meta
machine. I'm choosing to treat that as a coincidence.

Bitcoin keeps a history that's expensive to replace. A node that comes back online checks
the candidate chains against its rules and follows the valid one with the most work
behind it. Replacing an old block means redoing the work that ties every later block to
it. That's protection under assumptions about the attacker and the network, and a recent
block can still be undone. And the work is tied to something scarce, electricity and
hardware. A unit of cost in this book is tied to nothing. The economist Eric Budish showed
in 2025 what that tie has to cost: for Bitcoin's kind of trust to hold, the honest work has
to stay expensive at every moment compared with what an attacker could win. A flat charge
of one unit can't do that, and isn't trying to. It's a count, not a lock. The lock is the
rule that the close waits for the check, and it would work at a price of zero. The price is
there because, on a finite machine, keeping the answer makes two arrows meet.

And Bitcoin wasn't first. Pull on its footnotes and three of the eight references in the
paper that started it point to Stuart Haber and Scott Stornetta, who in 1991 worked out how
to stamp a document with a time nobody could fake later, by chaining each stamp to the ones
before. A company built on their idea, Surety, printed a short fingerprint of its chain in
the classified ads of the New York Times once a week from 1995, and was still doing it in
2018, under "Notices & Lost and Found," according to a piece the journalist Daniel Oberhaus
wrote that year. To make a record nobody could quietly rewrite, they put it somewhere a
million people would keep a copy without meaning to.

All of those work. I lean on all of them. The next thing isn't "they're broken." It's
where they sit. The database's commit is bits in a log, kept by a database program, on a
machine whose own step will overwrite those bits the moment some instruction says to.
Milner's guarantee holds inside programs written in his language and nowhere else. Bitcoin
is a set of rules running on ordinary computers that do whatever they're told. Each one is
a program or a rule sitting on top of a machine that can't tell the two computers apart.

The obvious answer: put the rule one level lower, in the piece of the system every action
has to pass through. Security people call that a reference monitor. James Anderson
described it in a 1972 planning study for the US Air Force: a piece every access passes
through, that can't be tampered with, and small enough to check. Fred Schneider argued in
2000 that a monitor that only watches a run as it goes can enforce exactly the rules whose
breaking shows up at some point you can name, and "no close without an earlier passing
check of the same claim" is one of those. And Arthur Azevedo de Amorim and six coauthors
built monitors in 2015 that check a rule at every single instruction, and proved them
correct. Putting a rule under every program, so nothing can get around it, is their move,
not mine. A monitor that wouldn't let any program raise its record without paying and
without the check first would be one way to build what this book describes. That's an
implementation, not the thing. What I'm putting under that move is narrower: a record that
has to be paid for, that has to be earned, and a reason from counting why the price of a
record that never comes down can't be zero on a finite machine.


The two computers, put back together

Here's the two-computer story again, rebuilt as Thiele machines, with the record and a
running count written out. The record here is established: it goes up only right after a
check of the claim passes. The prices are one to check, one to raise the record, and
nothing for ordinary work.

Why does the check cost anything, if effort never counts? Not for the work. The check
leaves a mark saying it passed, so the raise can see it, and you've already drawn what
that mark does: "true and unchecked" and "true and checked" both land on "true and
checked." Two arrows meet, so Bennett's rule charges it. The raise costs one because
that's the toll. And the copier's raise costs one even though it's refused, because the
price is on the button, the same as the stamp pressed on YES in chapter four.

  [table: the sorter and the copier, step by step]

At the end, the lists are still the same. Everything else differs. The sorter's record is
up and its count reads 2. The copier's record is down, and it paid 1 for the attempt,
because an attempt costs what it costs. Nothing the copier can do raises its record without
first running a passing check of the claim. And anything that lets through only the list
can't tell you which is which. Walk the warehouse now and there's finally a lamp that's lit
in one and dark in the other.

How literally should you take that table? It's a picture of the condition, and that
condition is the whole of what established means. What it needs from the question is a
checker that says yes exactly when the answer is yes. Without one, the record is honest
about whatever the checker reads, and only by convention about your list. That's Gettier's
pocket again.

And a lamp for whom? The record is bits too. It's a lamp in the machine, for anybody
walking that warehouse. Print it out and hand it across a desk, and you're back at the
sticker on the windshield: the person reading it has to trust whoever handed it over, or
have some way to check the box that says it ran. That's the last chapter's problem, and
this book doesn't solve it. What changes is the question, from "did it run?" to "do I
trust the box that says it ran?" That's a smaller question. It isn't no question.

So, back to the list from the start of the chapter. The windshield sticker is about whether
a piece of paper is genuine, and nothing here touches it. The "all tests passed" sheet fits
only if the test is a checker proved to mean what it says; a set of tests that can miss a bug
establishes "this procedure said yes," which is true and smaller. An audit or a ledger kept
by a program on an ordinary computer is bits the program wrote; it fits only where the step
underneath keeps the record and refuses to raise it without the check. A proof is one
example: checking its steps is a check that can say no, though whether its statement says
what you meant is still yours to read. The AI that sounds sure of itself isn't touched at
all.

Now the honest half. Take away the rule that the raise waits for the check, and keep only
the bare toll from page one, and the copier has an easier move: pay one, raise the record,
done. The toll is satisfied and the receipt is real, but it's a receipt for nothing. The
bare toll prices the closing of the door. The check behind it goes unpriced and unrequired.
That's why established is a condition you add, not something the definition hands you.


What putting it in the step buys

The hardest objection is one I'd rather make myself. You defined a mark and a charge, then
showed the charge gets paid when the mark goes up. That's your definitions agreeing with
each other.

For the bare machine, that's fair, and the copier's receipt for nothing is the proof. What
makes the record mean established is the condition that it goes up only after a check of
that very claim passed, meeting the first three of the four conditions, with the fourth, an
honest checker, a fact about the checker. And the condition isn't about one program. On
every run from a clean start, if the record is up, then somewhere earlier a check of the
claim passed, with nothing touching the thing between the check and the raise.

So a raised record, from a clean start, tells you a claim went through a passing check before
the raise. That piece of history is what it keeps, and only that. It doesn't say the claim
still holds at the end; the thing it's about can change after the raise. The record stays up
about the version that was checked.

That "every run" is what a rule on every step buys. A log written by one program is only as
good as that program. A rule the step itself enforces covers every run, hostile programs
included. There are two limits on that "every," and I'll say them now so you don't have to
find them later. It's every run, not every everything: from a clean start, one step at a
time, on a step that does what its definition says. A hostile start, a soldering iron on the
record's bit, or a hostile reader is outside it. And on their own, the record and the count
are what people who prove programs correct call ghost state: erase them and every program
computes exactly what it did before. What isn't ghost is whatever the step reads before it
lets the record rise: the check in front of it.

A computer that runs a Thiele machine, your laptop say, isn't that machine. It implements
it, inside bounds, the way a laptop implements a Turing machine. Turing's tape never runs
out, and a laptop's memory does; strictly, a laptop is a very big finite machine, and it acts
like a Turing machine only on the computations that fit. Nobody minds, because the bound is
known and most of what people compute fits. That's the same deal any device running a Thiele
machine gets. The bounds aren't fine print. They're the whole difference between running a
model and being one.

How much can a difference in size matter? On 4 June 1996 the first Ariane 5 rocket lifted off
and broke apart about forty seconds later. The inquiry board, chaired by the mathematician
Jacques-Louis Lions, traced it to one conversion in the guidance software: a 64-bit number, a
value tied to horizontal speed, squeezed into a 16-bit whole number. On Ariane 4, where the
software came from, that value could never get big enough to overflow, because of how that
rocket flew. Ariane 5 flew differently. The value got too big, the backup unit failed on it,
the main unit failed the same way a fraction of a second later, and the code doing the
converting didn't even serve a purpose once the rocket was off the ground; it was kept so the
software would match the old rocket's. The board's report says the assumption that made the
conversion safe had been agreed on and then, without anyone meaning to, kept out of sight of
any outside review. An assumption about size that holds on one machine is a fact about how
that machine gets used. The code doesn't carry it, and yet it travels with the code without
anybody noticing. The only defence I know is the dull one: write the assumption into every
statement that needs it, where the next person will trip over it.
