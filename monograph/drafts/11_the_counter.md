The counter

Back in chapter four you kept a tally beside the two boxes, the way you'd keep score
beside a board game. The tally lived in your hand. The machine never saw it. That's
fine for a game on a table. For anything that's going to run on its own, with nobody
keeping score, the total has to live somewhere the machine can reach, which means the
machine can, in principle, write it.

So this chapter is about what a running total inside a machine has to be before you're
allowed to call it a receipt. Here's the answer first, because it's short, and then
the chapter is about why each word is there: a receipt is a total that lives in the
state, that only climbs, that equals the sum of what was charged, and that nothing else
could have been.


A stick, split down the middle

The oldest receipt I could find that you can still hold is a piece of wood. From about
1100, under Henry the First, until 1826, the English treasury recorded what it was owed
on tally sticks: a strip of hazel, notched across with cuts of set widths, then split
lengthwise so each half carried the same notches. The treasury's own handbook from
around 1180, the Dialogue of the Exchequer, gives the widths: a thumb's width for a
hundred pounds, a swollen barleycorn for a pound, a bare cut for a penny. The payer kept
one half, called the stock, which is one story for where the word stockholder comes
from. The treasury kept the other. When the time came to settle, you laid the two halves
together, and only the two original halves fit, because wood splits along a grain nobody
can copy. Add a notch to your half and the other half shows a gap where the partner should
be. Try to take a notch away and you find that wood can't be uncut.

When they finally stopped using them, the clerks burned centuries of old tallies in the
furnaces under the House of Lords, overheated the flue, and burned down the Palace of
Westminster. I mention that because it's the best fact I picked up for this book, and
because it tells you how many of them there were.

Do it yourself. Draw a border around a strip of card, notch it once for every coin you hand
a friend, then split it lengthwise through the notches and keep half each. Don't trim the
edge or swap in a fresh strip. Now add a notch to one half and put them back together. You'll
see the mismatch straight away. And you can't put a cut back: a patch is just one more thing
to look at. The total is the notches, one per coin, and the count only climbs. Both halves
started with the same count, so if they disagree now, somebody changed one. The mismatch
won't tell you who. What the stick gives you is a comparison you can make, not an object
nobody can forge.

Economists read the same stick another way, and they're not wrong either. Alfred
Mitchell-Innes made the treasury tally his star witness in 1913 that money is credit: the
crown paid the people it owed by "raising a tally" on some branch of its income, a wooden
promise to pay. A receipt to me, money to him, and it's the same piece of wood. Narayana
Kocherlakota proved a version of his point in 1998: in a wide range of economies where
nobody can be held to a promise, anything money lets people do, a memory of everyone's past
dealings lets them do too. His title says it in three words: money is memory.


Why it has to climb

Page one already showed why there are no refunds: if a later move could pay you back, the
move that settles charges you one, the next move hands it back, and the whole run comes out
free. A total that can come back down is an accountant you can lean on to revise the books.
"This run cost at least one" would be true of a run that ended having cost nothing. So the
count only climbing isn't decoration. It's what makes "at least" mean something.

The same rule turns up in two places that have nothing to do with each other, pointing in
opposite directions, and that's a big part of why I trust it.

In 1978 Leslie Lamport asked how a set of computers passing each other messages, with no
shared clock, could ever agree on what happened before what. His answer is a counter on each
machine with two rules: add one before you do anything, and when a message arrives carrying
the sender's count, jump your own counter above it, never below your own. Those counters,
he showed, respect cause and effect: if this caused that, this has the smaller number. And
they do it, in his words, "with no actual timing mechanism." They're clocks only in name.

  [figure: Alice and Bob passing notes with stamps]

Try it with three people passing notes and you'll see it work in two minutes. Then let one of
them reset their counter to zero after reading a note, and watch a reply come out numbered
before the note it replies to. A counter that goes down can't be leaned on for order. The
other direction doesn't hold, though: two people can number two unrelated acts 1 and 2, and
the numbers alone don't say the first caused the second.

Where did Lamport get it? In the notes he keeps on his own papers, he says the timestamps came
from an earlier note by Paul Johnson and Bob Thomas on keeping copies of a database in step,
whose method wasn't quite right: it let things happen in an order that broke cause and effect.
What let him see the fix, he says, was special relativity, which teaches that the one order of
events everybody agrees on is the order of what could have caused what. And he passes on a line
from Jim Gray, the database man whose wedding you met in chapter eight: Gray had heard two
opinions of the paper, that it was trivial and that it was brilliant. Lamport says he can't argue
with the first and isn't inclined to argue with the second.

Now the other direction. In 1949 Alan Turing, and in 1967 Robert Floyd, each asked how you prove
a program stops. Both times the answer was to find a number that goes down on every step and
can't go down forever, like a whole number that can't go below zero. If every step lowers it,
the steps can't go on forever. Up-only gives you order, and down-only gives you stopping. They're
the same shape, seen from the two ends: a number that only goes one way is something you can
build on.

And there's a real case where a counter was allowed to go down and got gamed exactly there.
Ethereum, one of the largest blockchains, charges "gas" for every step of a program, and for
years it gave gas back when a program freed up storage. Someone noticed you could fill storage
when gas was cheap, hold it, and cash the refunds when gas was dear, and a token was built to do
exactly that. The real work in a block could reach nearly twice the block's stated limit. In 2021
a change called EIP-3529 cut the refunds sharply and capped them at one fifth of the gas used. The
written reasons are the token and those overfull blocks. I read both as the same lesson: a counter
that goes down was being leaned on at the place where it went down. Gas comes back in a later
chapter, as the one real system of five that charges at the moment of the write.


The total is the charges and nothing else

The next property is the plainest. The counter after a step is the counter before, plus what
that step was charged. Add up a whole run, and all the middle values cancel out, the way a sum of
differences collapses to last minus first. The total is the sum of the charges.

Why say it? Because it's the property that fails quietly. Say a machine charges one for raising
its record, and somewhere in its error handling forgets to add the charge when the step fails
halfway through. Or it charges two on one path and one on another for the same move. Or it has one
step that writes the counter directly. Then the counter is mostly the sum of the charges, and
"mostly" is the whole gap between a receipt and a note that says "trust me, about this much."
The rule is that there's no "mostly": every step, every outcome, every error, adds exactly its
charge, and a step that fails is charged the same as one that succeeds, because the charge is on
the attempt. For a machine built that way, the rule can't fail. What can fail is the claim that a
real machine is built that way, and checking that means going through every move it has, the
failure branches included, one at a time. It's dull, and it's the whole job.

One thing it doesn't say is that every unit bought something. The total is exact about what was
spent. What the spending was worth is a later chapter's question.


Only one honest count

The next property surprised me by being provable at all. Fix the price list: this move costs one,
that one costs zero. Now say somebody else keeps their own books: their own total for every state,
starting at zero, and going up on every step by exactly what the price list says. Could their books
disagree with the machine's counter, on some state you can actually get to?

No, and the proof is the tally stick. Both totals start at zero. On every step, both go up by the
same amount. So on every state you can reach from the start, they're equal. Agreement at the start
survives the first move, then the second, then every move after it. Given the price list, the count
is forced. It's the arithmetic, not a second opinion.

It only says that about states you can reach. On a state nothing reaches, it says nothing, which is
the right thing for a receipt to say.

And one thing follows that's easy to miss. If the counter is part of the state, then a run that
comes back to a state it's already been in has the same counter both times, so the moves on that loop
cost nothing in total. A machine that keeps its counter inside its state can only go round a loop that
costs nothing. Every paid move lands it on a state it's never been in, because the counter is higher
there than anywhere before. So a counter that only climbs is itself paid for in fresh paper. On a
finite machine, that means no move can be priced above zero at all: play any move over and over, the
states come back around, and a loop costs nothing. A machine that keeps its own receipt, with even one
paid move, needs endlessly many states. That's chapter two again, coming up from underneath.

Here's a puzzle that shows where the "only one" stops. Take the one-switch machine whose set costs
one and whose reset costs zero. Set it once and it's up. Reset it and set it again, and it's up again,
the same state. Now picture a second machine that keeps the whole list of moves. To it, "set" and
"reset, set" are different. So you can always walk a list of moves into the second machine, one way
and one way only. But you can't always walk the first machine's states into it, because two lists that
land the first machine on the same state can land the second on different ones. You can do it exactly
when the second machine never tells apart two lists the first one treats the same. Joseph Goguen put
that as a general rule in 1972, in a paper whose title says it outright, "Realization is universal,"
and Thomas Colcombet and Daniela Petrişan redid it in 2020. None of that uses the toll at all.

The nearest relative in physics is in thermodynamics. Elliott Lieb and Jakob Yngvason showed in 1999
that once you fix which states can be reached from which, and that follows a short list of rules,
there's a quantity that goes up exactly along it, and it's the only one once you pick where zero is
and what one unit is. Their order goes in and their count comes out forced. Here the price list goes
in and the count comes out forced.


The toll is an old trick with a new name

It would be nice to have a new kind of cost argument here. This isn't one. The toll is a case of a
technique computer scientists have used since 1985, and that a mathematician studying whether things
settle down had, in another form, in 1892.

It's called the potential method. Give every state a number, the potential, that measures how much is
stored up in it. Then look at each step and ask: does the step's cost, plus the change in potential,
ever come out negative? If it never does, then any run costs at least as much as the potential dropped
from start to finish, because the drop had to be paid for along the way. Robert Tarjan set it out in
1985, crediting the potential view to Daniel Sleator. Tarjan used it the other way round, to show a run
costs at most so much.

Do his stack example with coins. Every operation takes some coins off the top, maybe none, then puts
one on, and costs one for each coin it moves. Let the potential be the number of coins. An operation
that takes off k coins and puts one on costs k + 1 and changes the potential by 1 minus k, so its cost
plus the change is exactly 2, every time. So any run from an empty stack costs at most twice the number
of operations, which is twice the number of pushes, however many coins some of them take off.

The decreasing number underneath it is Aleksandr Lyapunov's, from his 1892 doctoral thesis on whether a
moving system settles down. It was in Russian. A French translation came out in 1907, made by a French
naval engineer, Édouard Davaux, and corrected by Lyapunov himself. The English one came out in 1992, a
hundred years after the original, translated from the French. A translation of a translation. Did the
computer scientists of 1985 get it from him? I can't tell you, and nothing here needs them to have. What
I have is a picture: the same idea, a number that only goes one way along a run, in a thesis about
whether a moving system settles down and in a paper about data structures, close to a century apart.

Now point it at the record. Let the potential be one when the record says not done and zero when it
says done. A step that takes not done to done drops the potential by one, so for the step's cost plus
the change in potential not to come out negative, that step has to cost at least one. That's the toll,
exactly. And "any run from not done to done costs at least one" is just the method's usual conclusion,
the potential dropping from one to zero.

Ask for the other direction too, that a step's cost is never more than the potential it drops, and the
two together pin every price exactly: one on a step that settles something, zero on every other step,
and nothing ever going back to not done. One catch: that only works if the price can depend on where
the step starts. With a single price per button, like the stamp, a button that settles once still costs
one when it's pressed again on done, so no price list per button can meet both directions.

Two more tools sit next to this. Run a list of moves inside a wrapper that adds up a number as it goes,
and you get back the final state and the run's total; Norman Danner and Daniel Licata built cost
reasoning for programs on exactly that, in 2015 with Ramyaa Ramyaa and in 2022. And give each move its
price ahead of time, as a tag that adds up as the moves do; that's Shin-ya Katsumata's grades from 2014,
which Dominic Orchard, Vilem Liepelt and Harley Eades put into a working language in 2019. The potential
method itself went into the checking of programs before any of those: Martin Hofmann and Steffen Jost in
2003, and Jan Hoffmann, Klaus Aehlig and Hofmann in 2011. The difference with this book is when the number
gets written. A cost checked ahead of time gets checked before the program runs, by whoever checks it. A
cost kept in the state gets written while it runs, by the step itself. The number is the same. The moment
of truth is different. For a program with loops whose cost depends on its input, a fixed tag can only
bound the cost, while the counter holds the exact number; cost-aware type theories like calf, from Yue
Niu, Jonathan Sterling, Harrison Grodin and Robert Harper in 2022, reason about such costs with proofs.

And there's one more neighbour, closer than any of those. A number the step keeps up to date and nothing
else ever reads is what people who prove programs correct call ghost state. Susan Owicki and David Gries
used it in 1976, crediting the first use they'd found to Maurice Clint, because some true facts about a
program can't be proved without it. Their rule lets it appear only where it's being updated itself, so
it never steers the program. Jean-Christophe Filliâtre, Léon Gondelman and Andrei Paskevich
worked out in 2014 when ghost code can be removed without changing what the program computes. By that
test the counter is ghost whenever no step reads it. So what does putting it in the step buy? Two things.
The number is there while the machine runs, where somebody looking through a window can see it, not only
inside a proof written afterwards. And the rule that keeps it covers every move the machine has, so every
run.

Two last relatives. Chapter four's floor, "any run from not done to done costs at least one," is the
cheapest-path bound in a system with weights on its moves: every path from the not-done states to the
done ones crosses the line between them, and every step across that line weighs at least one. Weighted
machines like that go back to Marcel-Paul Schützenberger in 1961. And the physicists who study what you
can turn into what, when some operations are free, have the same shape: Bob Coecke, Tobias Fritz and
Robert Spekkens gave the general setup in 2016, Fritz worked out its algebra in 2017, and Tomáš Gonda and
Spekkens catalogued the numbers that never go up under free operations in 2023. Read with "done" as the
thing you're after and one unit of cost as the currency, the not-done potential is the simplest of those.
It's a neighbour to know about, not a result of mine.

So what's new, if the method isn't? Only where it's pointed. Tarjan and Sleator's method proves things
about costs. What this book adds is which potential, the one that drops when something settles, and what
happens to that when you can only see part of the state through a window.


What the counter is, said once

A receipt is a total that lives in the state, only climbs, equals the sum of the charges on every path
including the failures, and is the only such total, on every state a run from the start reaches, for
its price list. Each of those had a home before this book: the stick for a total that lives in the
state, Lamport's clocks for climbing, Turing's and Floyd's numbers that only go down for the same rule
run backwards, the cancelling sum for adding up, the step-by-step argument for the one honest count.
None of them is physics, and none of them says what the charges should be. Once you've chosen the
charges, the counter is the arithmetic.

There's one thing a counter can't do just by existing. The stick works because you can lay the two halves
together. What if all you're ever shown is one half, through a window that doesn't show the notches? Then
you're back in chapter seven. Take two states that differ only in their count, one at 1 and one at 2, and
let nothing that comes through the window depend on the count. The window gives the same view for both,
any reader gives the same answer for both, and one of the answers is wrong. So a window that leaves out
the count can't give it back. To read the count, the count has to come through.
