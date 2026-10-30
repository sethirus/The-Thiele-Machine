Looking isn't keeping

The toll charges the move that settles something for good. But there's another
thing a machine does that feels like it ought to cost at least as much, maybe
more, and that's finding out. Every time a machine rules out a possibility, it
knows more than it did. If two arrows meeting costs something, does learning cost
something too?

Most people's gut says yes, and finding out is the expensive part. Most
physicists felt that way too, for a long time. It's why one little imaginary
creature kept them busy for over a century. This chapter is about where that
feeling goes wrong, and where it's right. The short version: looking doesn't have
to make two arrows meet. It uses up a blank page instead, and you can hand the
page back. Wiping the page to use it again is where two arrows meet. And making a
record that stays, one nobody can hand back, is paying for good.


A small being at a small door

In December 1867 James Clerk Maxwell, who had published his equations for
electricity and magnetism two years before, wrote a letter to his friend Peter
Tait about a problem he couldn't get rid of. Take a box of gas at one temperature,
with a wall down the middle and a tiny door in the wall. Now imagine, he said, a
"very observant and neat-fingered being" sitting at the door, who can see the
molecules coming. When a fast one comes from the left, it opens the door and lets
it through. When a slow one comes from the right, same. Otherwise it keeps the
door shut. It never pushes anything. It only opens and closes a frictionless door
at the right moments.

After a while the right side is hot and the left side is cold, and you've got a
difference you could run an engine off, made out of nothing but looking. That's
supposed to be impossible. It's exactly what the second law of thermodynamics
says can't happen, and the second law is the one law physicists are least willing
to give up. Arthur Eddington wrote in a 1928 book of popular lectures that a
theory found to contradict it has nothing for it but to collapse in deepest
humiliation.

Maxwell put the being in his textbook in 1871, and it got named Maxwell's demon,
though not by Maxwell. William Thomson, later Lord Kelvin, called it a demon in
the journal Nature in 1874. Maxwell, in an undated note to Tait headed
"Concerning Demons," tried to take the name back: "Call him no more a demon but a
valve." Nobody listened, which is probably for the best, because "Maxwell's
valve" wouldn't have lasted a century. But his correction is exactly right, and
it's the whole problem: the being does no work. It opens and shuts a door.

So physicists spent the next century trying to find where the being was
cheating. The obvious answer pulls hard: the being has to see the molecules, and
seeing costs. In 1929 Leo Szilard cut the box down to a single molecule and did
the arithmetic. The second law survives, he said, if finding out which side the
molecule is on costs at least as much as the being gains. In 1951 the French
physicist Léon Brillouin made it concrete: to see a molecule you have to bounce
light off it, and, the way the philosopher of physics Jeffrey Bub sums it up,
finding out that way costs at least one halving's worth of entropy for every bit.
For thirty years that was the answer. Information costs because getting it costs.

But that's a price on one way of looking. It doesn't show that every way of
looking has to pay it.

Szilard is worth one more minute, for a reason that has nothing to do with the
demon. Four years after the one-molecule engine, in September 1933, by his own
later telling, he was waiting at a traffic light on Southampton Row in London. He
had just read a newspaper report in which Ernest Rutherford, the physicist who
announced the atomic nucleus in 1911, called the hope of getting power out of
atoms moonshine. As the light changed, it occurred to him that an element which
gave off two neutrons when it swallowed one could keep a reaction going by itself.
That's the nuclear chain reaction, thought up crossing a street. It's his memory
of himself, and Richard Rhodes's history of the bomb opens with it, in a chapter
called "Moonshine," so hold it as the man's own story, not a record made at the
time. It changes nothing about the demon. What it adds is a picture of the man:
the same mind looked at one molecule in 1929 and one neutron in 1933, and both
times the question was what a single small step forces downstream.


Bennett moves where the cost is

In 1982 Charles Bennett, who had already shown in 1973 that computing can be done
with no two arrows meeting if you keep the whole history, took the demon apart one
step at a time.

The being looks at a molecule and writes down which side it's on. Draw it.
Before the look, there are two ways the world could be: molecule on the left with
a blank notepad, or molecule on the right with a blank notepad. After the look,
there are two ways: molecule left with the pad saying "left," or molecule right
with the pad saying "right." Two went in, two came out, and you can read the
before off the after. No two arrows met.

But something got used up: the blank page. Before the look, the pad was blank and
ready. After it, the pad is full. That's the fresh paper from chapter one. The
look didn't merge anything. It borrowed a page.

So where's the cost? The being has one notepad and a lot of molecules. After the
first molecule the page is full, and to do the next one it has to wipe it. Draw
the wipe. Pad says "left" goes to blank. Pad says "right" goes to blank. Two
arrows, one landing place. There it is. Looking feels like the active part, the
thing the being does, and wiping feels like housekeeping. The housekeeping is
where two arrows meet.

That's Bennett's, and it's the same rule chapter three wrote on the move: what has
to cost is "the erasure of a bit or the merging of two computation paths." In the
same 2003 paper he lists copying onto a blank place among the operations that can,
in principle, be done without any such cost.


The demon on a sheet of paper

Build it, because the whole thing is four dots, and you should see the arrows
meet or not meet for yourself.

The machine has a hidden bit, which is the molecule's side, and a display, which
is the notepad. Write its four states as pairs, hidden bit first and display
second: 00, 01, 10, 11. It has two moves.

MEASURE copies the hidden bit onto the display the way a light switch adds: if the
hidden bit is 1, flip the display; if it's 0, leave it alone. Draw the arrows. 00
goes to 00. 01 goes to 01. 10 goes to 11. 11 goes to 10. Every state has exactly
one arrow landing on it. Nothing met.

Look at the two states where the display starts blank, 00 and 10. They go to 00
and 11: the hidden bit got copied onto the blank display. That's the look.

WIPE sets the display to 0 no matter what it held. 00 goes to 00, and 01 goes to
00 as well. 10 goes to 10, and 11 goes to 10 as well. Two arrows land on 00 and
two land on 10. That's the wipe, and arrows meet twice.

  [table: before, after MEASURE, after WIPE]

So Bennett's rule charges WIPE at least one, and it's allowed to charge MEASURE
nothing. Zero on the price list doesn't mean zero spent in a real device; a real
MEASURE takes time and energy, and it uses up the blank display. What it doesn't do
is make two arrows meet.

One detail worth seeing. Follow only the two cases you actually set up, the ones
with a blank display: after MEASURE they're 00 and 11. WIPE sends those to 00 and
10. Still two different states, because the hidden bit still tells them apart. So
on those two cases, WIPE didn't lose anything. The rule charges it anyway, because
the rule has to answer for every state it might be handed, and on the full table
the arrows meet. The price is the worst case on purpose.

Now be the one watching. You can see the display and not the hidden bit. The
display starts blank, so you've got two candidates for what's going on: 00 or 10.
One bit you don't know. The machine runs MEASURE, and you look. If the display
shows 1, only 10 could have done that. If it shows 0, only 00. Your two candidates
went down to one. You learned the hidden bit.

The price was zero. And the machine's own list of where it could be went from 00
and 10 to 00 and 11. Still two. Nothing it could have been got merged with
anything else.

You narrowed. It didn't.


Two rows of dots

That last line is the thing I had to get straight before any of this made sense,
so here it is as a picture.

Draw the machine's possible states as a row of dots. Now draw a second row above
it: the dots that you, watching from outside, still think it might be on. The
first row is a fact about the machine. The second is a fact about you, about what
you've seen and what you've crossed off. Both rows can shrink, and they shrink for
different reasons.

The machine's row shrinks only when two of its arrows meet. That's what the price
charges. Run the halving rule from chapter three along a whole run and the counts
just multiply: if the first move costs one, the row can at most halve; if the next
costs two, it can shrink to a quarter of that; and so on. So a run can't shrink
the machine's own row by more halvings than it paid for, all told. (Count with
whole questions instead and you lose a little: four places and three places both
take two yes-or-no questions to pin down, so the rounded count can't see that
squeeze. The plain count can.)

Your row shrinks when you see something some of your candidates couldn't have
shown you, and you cross them off. Nothing happened to the machine. It didn't
merge anything. It doesn't know you're watching. It would have done the same thing
with nobody there.

The physicist Edwin Jaynes had a name for mixing those two rows up, and it's one
of the most useful names I know: the mind projection fallacy, treating what you
know about a thing as if it were a property of the thing. Your list of candidates
is in your head. The machine's row is in the machine. The price is about the
machine's row, and crossing a candidate off yours doesn't move it.

I have to be fair to Jaynes, though, because he'd argue with where I just took his
phrase. In a 1965 paper he wrote that entropy is "an anthropomorphic concept," a
phrase he credited to the physicist Eugene Wigner, meaning it belongs to the
particular experiments you or I choose to do on a system, not to the system alone.
For Jaynes, the second law is about what's known too, and the line I'd like to
draw, that physics cares about the machine's row and not yours, is exactly the
line he'd refuse. That fight, Jaynes against Boltzmann, is one of the oldest in
the subject, and I can't settle it and don't have to. What I need is only this:
the two rows are different rows, and only one of them belongs to the machine.


Who holds the pen

Here's the most beautiful thing in this chapter, and you find it by playing with
the four dots, not by thinking about them.

Run MEASURE twice. The first time copies the hidden bit onto the display. The
second time adds the hidden bit in again, and adding it twice the light-switch way
gets you back where you started. Check the arrows: 10 goes to 11, and 11 goes back
to 10. The display went full and then blank again, no two arrows met, and the price
was zero both times.

So a display that was blank before the first MEASURE can be put back to blank with
no arrows meeting, by a second MEASURE. Not by WIPE. This is the borrowed page
being handed back: while the original is still there to check against, the copy
can be un-copied.

What's the difference? MEASURE looks at the hidden bit while it clears the
display. It has the thing the copy came from, so it can undo the copy. WIPE
doesn't look. It sets the display to 0 regardless, and "regardless" is exactly
where the arrows meet. Bennett has this in his 2003 paper too: he lists erasing
"one of two copies of data known to be identical" as a step that loses nothing,
because you're only removing a duplicate. And Lídia del Rio and her colleagues
argued in 2011 that the cost of erasing a system depends on how much the eraser
already knows about it, dropping to zero, and in the quantum case below zero. The
cost of clearing a record falls on whoever clears it, and it's lower the more they
know.

Try it with a card under a cup, red or blue, and a note that's blank or marked.
Start with the note blank. Lift the cup: for red, flip the note, blank to marked
or marked to blank; for blue, leave it. Now the note tells you the colour. Do the
same thing again while the card is still there, and the note goes back to blank.
Check all four card-and-note combinations and you'll see this rule undoes itself,
so no two combinations land together. Now erase the note regardless of the card:
for either card, blank and marked both land on blank. Arrows meet. The cards don't
measure anything about heat. What they show is which information each rule gets to
use.


Learning after the first look

A fair objection: the demon's watcher learned something by looking, but any
watcher learns something on the very first look, before the machine does
anything. So the better question is, after that first look, can a step teach you
more, at no cost?

Yes. The smallest machine that does it has three states in a ring: U goes to V, V
goes to W, W goes back to U. Say all you can see is one thing: whether it's on
W. Start with two candidates, U or V. Neither is on W, so the first look tells you
nothing. Take
one step. From U you'd be on V, not W; from V you'd be on W. One step told
them apart, and a ring never has two arrows meeting, so the price can be zero.

Two states can't do it, ever, with any arrows. If you can't tell two states apart
at the first look, what you can see is the same on both, and those two are all the
states there are. So what you can see is the same everywhere, forever.
Try to draw a counterexample with two dots. You'll draw the same two dots a few
times and give up, and giving up is the proof. Three is the smallest number of
states where two that look alike at first can come apart later.


Finishing together

One more count before the big picture, because it's about how much room learning
needs.

Run a machine from several different starts, and photograph its whole state at
every tick. Lay the photographs out in rows, one row per start, one column per
tick. Say every run finishes for the first time at the same tick. And say that in
every column up to the one just before the finish, no two states step to the same
state. That includes the last step, the one onto the finish: if two runs sat on
two different states just before the finish, they can't both step onto one
finished state.

Could two photographs on that sheet show the same state? Two in the same column:
walk both back a tick at a time, and since no arrows met, they were equal the tick
before, all the way back to the starts. But the starts were different. Two in
different columns: give them both the same remaining steps. The one that's ahead
would finish first, and it was supposed to finish at the same tick as everybody
else. So every photograph shows a different state. With N starts and T ticks, the
machine needs room for N times (T + 1) states. Running in step and finishing
together has a size.


The certainty count

Now I can put the whole path from not knowing to knowing on one page.

You don't know which state the machine started in. There are a few it could have
been, each with its chance. Run the machine. Take any two of those possible starts
and watch where they go. Only two things can happen. They land on the same state,
and the difference between them is gone from the machine: two arrows met, and
under the halving rule from chapter three the price covered it, at most one
halving per unit. Or they land on two different
states, and the difference is still sitting in the machine, kept as two states
held apart. There's no third thing a pair of starts can do.

So everything you didn't know about the start splits cleanly in two: the part the
run destroyed, which was paid for, and the part the end state still holds.

Now put a watcher outside, who can see some part of the machine and not the
rest. Whatever they see depends only on where the
machine started, so whatever they learn is a fact about the start. And the same
split holds for it: what they learned is either still held in the machine's end
state, or it's gone from the machine and two arrows meeting paid for losing it. A
run that costs nothing leaves everything the watcher learned still held in the
machine.

That's the exact sense of "looking borrows." The watcher's copy is a copy, and the
machine still holds the original. When the machine lets go of the original, two
arrows meet, and the bill comes due.

What that doesn't say: how much heat. That's for the heat chapter. It doesn't say
the watcher's own notes are free; they need a blank page too. And if the start is
known for certain, there's nothing to learn and nothing destroyed, so there's no
floor from any of this at all.


Who gets charged is partly bookkeeping

The physicists had this freedom on the books before me. Paul Fahn in 1996, doing
the accounting of Szilard's one-molecule engine step by step, argued that whether
you charge the looking step or the wiping step is partly a choice of how you keep
the books, and that the total is what's fixed. Takahiro Sagawa and Masahito Ueda in
2009 worked out a bound on that total, with the split depending on the memory. So
"a price list could charge MEASURE instead" is a known freedom, not a loophole I
found.

The other side is alive too. Ruth Kastner argued in 2025 that Brillouin was
essentially right after all: put the real physics of measuring back in, and it's
the measuring that pays and stops the demon, and Bennett's free copy fails as
physics. And John Norton argued in 2013 that at the scale of molecules, jiggling
from heat keeps any process that's supposed to be perfectly reversible from ever
finishing, and finishing it costs more than Landauer's amount. If either of them is
right, a real demon's look has a cost after all.

What's on the page here survives that, because it's about price lists: a price list
that follows Bennett's rule isn't forced to charge the copy, whatever a real device
spends. What wouldn't survive is the physics I've been hanging on it, that a real
demon can look for free. If Norton is right, the line between looking and keeping
keeps its counting and loses its physics. I can't referee that one.

And in 2010 a group in Tokyo, Shoichi Toyabe, Takahiro Sagawa, Masahito Ueda, Eiro
Muneyuki and Masaki Sano, ran a real demon: a tiny particle walked up a staircase by
feedback on what a camera saw. The energy it gained was paid for by the information
the camera took, and nothing was violated. The demon is real, it works, and it
pays. Where it pays is the part that took a century.


Somebody got there first, goddamn it

I'd been sitting on this idea, that making a result stay so it can't be handed
back is what pays, and finding out only borrows, and I thought: this one's mine.
Then I found Carlo Rovelli's 2024 paper, "The Thermodynamic Cost of Choosing." A
real physicist, with a real paper, saying that making a choice that sticks gives
off at least the heat Landauer charges for erasing a bit. He even quotes a German
saying, Wahl ist Leiden, to choose is to suffer, and at that point what are you
going to do but laugh.

It pissed me off. It's hard to have an original thought in this world. But it
didn't last long, because once I actually looked, his was a sentence on the
surface, and the machinery under it was different.

On its face he contradicts Bennett. Bennett says measuring doesn't have to cost;
Rovelli says any measurement costs. So look at what Rovelli calls a choice. A coin
in the air hasn't chosen anything; it has to hit the ground and stop. And then the
sentence I'd put on my wall: "stabilization must be irreversible, otherwise it is
not stabilization." Bennett's free look is one that can still be undone, which is
why it's free. Rovelli's choice is one that's been made to stay, which is why it
costs. The way I read them, they're standing on opposite sides of the same line:
looking, which borrows, on Bennett's side, and keeping, which pays, on Rovelli's.

That reading is mine, and I owe you exactly how much of it. Push on it with his
paper open and it gives in four places. He saves the word "choice" for an outcome
that's stable and not predictable, and rules out a thermostat because it runs on a
predictable mechanism; the settling move in this book is fixed in advance by a
rule, so by his own definition his result doesn't cover it. His choice is one
possibility branching into two, which he calls in a sense the opposite of erasing;
the toll comes from two arrows meeting, the opposite shape. His stability lasts a
while, not forever; mine is forever, by definition. And he doesn't stand beside
Bennett at all: he holds that any measurement costs, credits that to the
philosopher Hans Reichenbach, and doesn't cite Bennett. So what Rovelli and I share
is a sentence: a choice that sticks costs something. Push on it and his coin
hitting the ground, a fact nobody could predict, sits closer to looking than to
keeping. I still think it's the same instinct. You've got everything you need to
disagree.

And on copying, the nearest physics isn't Rovelli's. It's in biology. Thomas
Ouldridge and Pieter Rein ten Wolde worked out in 2017 the basic costs of making a
copy of a molecule that stays matched to its template after the two separate, and
of destroying one. A companion paper the same year, with Christopher Govern, does
the same kind of accounting for how a cell reads out its own sensors, which is a
measurement in all but name. The way I read them, the copy that has to stay is the
one that pays. Then Jenny Poulton, ten Wolde and Ouldridge in 2019 found the sharp
form: in their simple models, when a copy grows with the weakest possible push, its
advantage over random copying, and the efficiency of storing that information,
both vanish. Pushing harder, with chemical work, makes copies that stay matched
after the two let go. That's finding out against keeping, in chemistry, with the
cost attached, and biology had the distinction before I did. Theirs is a
correlation between molecules, with heat in it. Mine is a reading in a model of
computation, with no temperature anywhere.

Two more neighbours have "learning" and "commit" in their titles, so the line here
shouldn't be read against them by accident. Sebastian Goldt and Udo Seifert in 2017
did the physics of a neural network learning a rule, and argued that learning has a
cost: the entropy the network produces limits how much it can learn. That doesn't
contradict this chapter. Their learner isn't copying onto a blank page; it's a
driven, noisy physical system, and that's what they price. This chapter only says
one way of finding out, a copy onto a blank, is allowed to be free. Nothing here
says every way of learning is cheap, and theirs isn't. And from statistics, Aurélien
Garivier, Tor Lattimore and Emilie Kaufmann in 2016 compared strategies that
explore for a while and then commit to one choice against strategies that keep
adjusting as they go. In their setting, over a long run, the best strategies that
commit lose about twice as much reward as the best ones that keep adjusting. That's the closest published sentence I've found to "committing
costs something" with a number on it. It's lost reward, though, not a count on a
ledger, so it's a cousin, not a twin.


What the toll is for, said at last

Now I can say exactly what the toll charges. Not looking. Not copying. Not finding
out. A look can be done with no arrows meeting, on a price list that charges
nothing for it; the demon is a machine where that happens. Looking uses up a blank
page, and while the original is still there, the page can be handed back. What
gets charged is the one thing chapter two showed can't be done on a finite machine
without two arrows meeting: settling something so it stays, a record nothing hands
back.

That's what "No Free Insight," the name I gave the toll before I understood it,
really covers, and I don't want the name doing work it hasn't earned. Insight in
the sense of finding out can come free; it borrows a page. The insight the toll
prices is the kind made to stay. Whether that narrower thing deserves the name is
fair to argue about. I kept the name because it's the question I started with, and
because narrowing it down is the finding.

One more thing this tells you, for later. A later chapter counts what it takes to
narrow a list of candidates down to a shorter one, and puts a cost on it. Narrowing
alone doesn't force anybody to pay anything; the demon just narrowed two
candidates to one for free. So wherever this book puts a price on narrowing, the
payment goes in as an assumption, out in the open, and I'll keep calling it one.
