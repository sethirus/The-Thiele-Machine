Keeping without the heat

The last chapter was heat, and every line of it leaned on an assumption with a name. This one
doesn't need it. It's the counting that holds whether or not anybody ever measures a joule:
what keeping takes when the steps are noisy, or quantum; how much room a memory needs to keep
a history without any merge at all; what a machine's counter has to do with heat; and, at the
end, a plain list of what you've earned so far and what you haven't. Then one last section that
isn't counting at all, kept apart so you can check none of it leaked in.


A cell that's written once

Start with the smallest memory that keeps something. A cell has three states: blank, zero and one.
The question is "is the cell written?", no on blank and yes on the other two, and a written cell
stays written. The move is "write a 0": blank goes to zero, and a written cell is left alone.

Draw the arrows. Blank lands on zero. Zero lands on zero. Two arrows meet, so writing a 0 on nothing
is, by itself, a merge. The history where the cell was blank and the history where it already held a 0
now leave the same cell behind.

The obvious way round it is a fourth state that remembers: "0, and it was blank before." Now blank lands
on a state nothing else lands on. But the remembering state has to go somewhere on the next write too, and
it's written, so it has to stay written. Count. There are three written states now, zero, one and the
remembering one, and each of them lands on a written state. Blank lands on a written state too. That's four
starting places and three places to land, so two share. It's chapter two's chairs, and adding a fifth state,
or a fiftieth, only moves the problem along: as long as finitely many states are written, the written ones
plus blank are one more than the room they land in.

The only way to write with no merge, once every state has a next one, is a supply of fresh states that never
runs out: a new cell of an endless tape for every write, forever. Or a tape that stretches both ways, with the
machine stepping one cell along it each tick. Every cell has one before it and one after, nothing ever shares a
landing, "past the start" goes up on the first step and never comes down, and the machine never returns. That
pays at every step by taking a cell it has never used.

The argument leans on one thing, and I want it in the open: the write is a move defined on every state of the
cell, written ones included. A write defined only on blank, with the machine simply stopping when it meets a
written cell, merges nothing. That's the machine that stops, from chapter one: it buys the 0 by having no next step
at all.

And notice what it takes to start. A blank handed to you is a starting condition, not proof that somebody paid
heat to make it blank. If a device has to reset an unknown cell so it can be used again, the last chapter's floor
can apply to that reset. Precise versions of that floor, like David Reeb and Michael Wolf's from 2014, assume a
reservoir that starts thermal and untangled from the memory and a combined motion that merges nothing; their heat
bound holds under exactly those conditions. Reading a past or future payment off a known blank would need more
assumptions than a known blank supplies.


Noisy steps

Real states are noisy: the bead hops on its own. So take the step to be a table of chances. From each state, there's
a chance of landing on each state next, and every row adds to one. A permanent reading is a set of states you never leave
once you're in. And "nothing merges" has an exact noisy meaning: start with the chance spread evenly over the states, take
one step, and it's still spread evenly. In the table, that's every column adding to one, as well as every row.

Can a step like that raise a reading that stays? No, and the count is the chairs again, with chances in place of people.
Add up all the chance flowing into the yes-states from everywhere, one column at a time. Each column adds to one, so the
total is the number of yes-states. But the yes-states alone already send exactly that much, because they never leave: each
of their rows puts all of its one into the yes side. There's nothing left over for any outside state to send in, and chances
can't be negative, so every outside state sends in nothing at all. Not a small chance. None.

And it runs the other way. A step that can carry an outside state in can't keep the even spread, so one step from the even
spread leaves the chance more bunched than it was. Here's a way to measure bunching. Draw a state twice, independently, using
the same chances, and ask whether the two draws match. For two equally likely states the matching pairs have chances a quarter
and a quarter, so a match comes up half the time. Put three quarters on one and a quarter on the other, and the matching chances
are nine sixteenths and one sixteenth: ten sixteenths. Bunching made a match likelier. Each state contributes its chance squared;
add those up and call it the collision weight. The even spread has the least of it, one over the number of states.

Why does a step that lets anything in raise it? Say there are N states and column j adds to c_j. Starting even, the chance at j
after the step is c_j over N. The columns add up to N, because the N rows each add to one. Now add up (c_j minus one) squared over
all the columns. Multiply it out and use that total, and it comes to the sum of the c_j squared, minus N. At least one column isn't
one, so that's more than zero, so the sum of the c_j squared is more than N, and dividing by N squared says the new collision weight
is more than one over N. The spread got lumpier. Shannon's uncertainty drops too, by the line from the last chapter: the even spread
is the only one that holds the full log of N.

And a step that keeps every column at one never makes any spread lumpier. Each new chance is an average of old chances, weighted by a
column that adds to one, and an average of squares is never less than the square of the average. Add over the columns, and each old
chance squared gets weighted by its whole row, which adds to one. So the new collision weight is at most the old.

The first of those needs only the yes side to be finite; the rest of the machine can be as big as you like. The last needs no finiteness
at all. The middle one needs the even spread, so it needs finitely many states. A lopsided memory that keeps its own lopsided spread can't
raise a reading that stays either: weight each state by its chance and the same sum comes out.


Quantum steps

The quantum version needs a different picture. Draw a sheet through the middle of a room. Call every direction along the sheet YES, and the
direction straight through it NO. Now turn the whole arrangement without stretching it. Can the sheet stay in its own plane while the direction
through it turns into that plane? No. A turn keeps right angles. If the sheet still fills its plane after the turn, the direction that was at
right angles to all of it is still at right angles to all of it.

Here's what carries over. A quantum state is described by a direction, an arrow with a length. A reversible quantum step keeps lengths and
keeps the overlaps between arrows; that's called unitary. The YES part is a flat slice of directions that includes every mix of its own
directions. The directions with no overlap with any YES direction are the NO states. And permanence means a YES arrow is still YES after the
step.

One detail has to be settled before the right-angle argument works: the old YES directions have to fill the whole YES slice after the step, with
nothing missing. Pick a finite list of YES directions that build every YES arrow, none of them built from the others. A unitary step keeps that list
independent, because any way of building one image from the others could be run backwards to build the original from the others. The images are
still inside YES, there are just as many, so they still fill it.

Now take a NO arrow. Before the step it has no overlap with any YES arrow. After the step those overlaps are still zero, because a unitary step keeps
overlaps, and the stepped YES arrows still fill the whole YES slice. So the stepped NO arrow is still NO. Step again and the same holds. A unitary step
can't raise a reading that stays.

Finite size was used exactly once: a full finite list of YES directions still fills the slice after the step. Drop it and the endless ladder from the
cell above, one rung along each tick, is a unitary step that raises "past the start" on the first tick and keeps it forever, taking a rung it has never
used every time. So in finite size, keeping a quantum reading takes a step that isn't unitary. Not every step that fails to be unitary squeezes, though.
One that keeps the even spread, as pure dephasing and an unread measurement do, can't raise a reading that stays either, by the same column count as the
noisy steps. Which way a quantum measurement pays when its outcome is kept isn't settled here. The collapse models people test keep the even spread too,
so the heat the experiments look for is the heat of the noise those models add, not a Landauer price on a kept outcome.

  [table: what has been measured]

Bekenstein's bound ties entropy to energy and size under its own physical assumptions. It doesn't hand you a finite list of a device's states. Every count
in this book takes finitely many states as an assumption, and nobody has measured where that ceiling is.


How much room keeping takes

So far, keeping meant a merge or fresh states forever. In between there's a question with an exact answer: how long can a finite memory hold off the merge?

Take an operation that sends every value to one fixed value and leaves that value alone, the way a reset does. Hand it N different starting states, one of which
already holds the fixed value. Ask it to be repeated T times without any two of the states it passes through landing on the same next state. How many states does
the memory need?

Walk it. Each of the N minus one starts that isn't already fixed, followed through T repetitions, passes through T plus one states, and none of them twice: a repeat
would walk back, the way chapter two walks back two meeting arrows, to the start being equal to a later state of its own path, and every later state holds the fixed
value while the start doesn't. Two of those paths can't share a state either: walk back to the earlier time, and either two different starts are one state, or a start
is a state that already holds the fixed value. That's (T + 1) times (N minus 1) states. The start that's already fixed needs one more, and only one: every state on its
own path holds the fixed value, so walking back along it finds no contradiction, and its path can fold onto a single state. So the memory needs at least 1 plus (T + 1)
times (N minus 1) states.

And that's enough, so the number is exact. One state for the start that's already fixed; the operation leaves it there. For every other start, a row of T plus one states:
the first reads the way that start reads, the rest read the fixed way, and the operation walks the row, sending its last state to the common fixed state. For as many
repetitions as you asked for, nothing lands together. On the next one, the last state of a row and the fixed state both go to the fixed state: the merge, delayed exactly as
long as you paid room for.

With L of the starts already resting, the same count gives N plus T times (N minus L). In bits, a memory of B bits has at most 2 to the B states, so holding off T repetitions
with one resting start takes B at least log2 of 1 plus (T + 1) times (N minus 1). The memory grows with the logarithm of how long the history is kept. A fresh state every step
isn't a fresh cell every step.

Charles Bennett showed in 1989 that a reversible machine can save room by undoing and redoing its own intermediate work, keeping only enough to get it back. That trades time for
space. It doesn't let a machine running on its own, under this count, reuse a state it has been in without a merge.


Two levers

Now a harder version of the same question. Put two reset levers on a box, and use three values on the tabletop: 0, 1 and 2. The first lever wipes only 1 to 0 and leaves 2 alone.
The second wipes only 2 to 0 and leaves 1 alone. On the tabletop it doesn't matter which you pull first. Start one full state above each value, and allow every sequence of at most
T pulls. Each lever has to keep different states apart, through the promised horizon. How much room does the box need?

Count the zero states first. At each depth, the first lever takes every state already reading zero, and also the start that reads 1, into zero, and keeps them apart. So the zero states
grow by at least one per pull, and with the two other starts there are at least T plus 3 states. A single line of zero states reaches that: walk the line with either lever and stop at its
end.

But try the levers in opposite orders on that box and the hidden states disagree. Ask for more: the order of the levers must leave the whole machine the same, not just the tabletop. Then
the count goes up, to 2T plus 2. Take the simple case first, where the second lever leaves the start above 1 standing still, and the first lever leaves the start above 2
standing still.

Start above 1 and pull the first lever T times. That walks a chain of T zero states, all different: if two were the same, walking back would make the start above 1 equal to a later
state that reads 0. Now ask what the second lever does to a state on that chain. Commuting says pulling it after the first lever lands where pulling it before would, and before, you were at
the start above 1, where the second lever stands still. So the second lever holds every state on the first chain still. The same reasoning with the levers swapped walks a second chain of T
zero states from the start above 2, and the first lever holds every one of those still.

Can the chains share a state? Everywhere on the first chain but its last state, the first lever moves you on; everywhere on the second chain, the first lever holds you still. No state does
both, so nothing on the first chain except its end can be on the second, and the same with the levers swapped. The most they can share is their two ends, as one state. If they don't share
it, that's 2T zero states, and with the starts above 1 and 2, 2T plus 2. If they do, that's 2T minus 1 zero states, and now the zero start can't be on either chain: if it were, pulling from
it would reach the shared end within the horizon, and the lever that walks that chain would send both the end and the state just before it to the end, two states landing together before
the promise ran out. So the zero start is one more, and with the starts above 1 and 2 it's 2T plus 2 again.

When the idle lever moves the hidden state instead of holding it still, the path it traces above 1 or 2 costs states of its own. It runs for a while and then, if it repeats, falls into a loop.
Switch levers there, and every pull spent getting into the loop is one pull fewer for that chain, so the trade is one state for one. Commuting still pushes any sharing between the two chains
out to their far ends, because a shared state would have to come back to itself after a full turn of the other loop. The count comes out at 2T plus the longer loop, and when both loops are a
single state, the zero start adds the last one, as before. Either way, 2T plus 2, and the exhaustive search on the small horizons agrees.

There's a box that reaches it. At horizon one it has four places, and you can write every arrow down:

  [table: the four-place box]

On the three starts each column lands on three different places. On the whole four-place box each column has a repeat. And both orders of the levers agree on every row. So the promise
that holds through a horizon and the promise that holds everywhere really are different promises: ask each lever to keep states apart everywhere, forever, and the count goes up once more, to
2T plus 3, which two separate arms running on forever reach at every horizon.

Change the tabletop and the room can fit differently. Give it two bits, with one lever clearing the first and the other clearing the second. Lay out a grid of points (i, j) with i and j
whole numbers from zero up, plus one separate blank state. One lever adds one to i, the other to j, and both leave blank alone. Read a grid point as whether i is zero and whether j is
zero. Start at blank and at the three grid points (0, 0), (1, 0) and (0, 1).

  [figure: the grid square]

Both orders reach the very same grid point, not just the same reading. Each pull adds one to i plus j, so after t pulls you can reach exactly the triangle of points with i plus j at most
t plus 1. Its rows hold 1, 2, up to t plus 2 points. Add them and the blank: 1 plus (t + 2)(t + 3) over 2. And that's the least any box with this tabletop can do.
Here's why. Each reading with exactly one bit cleared starts with one state, and every pull its lever sends that reading's own states, plus at least one state with
both bits set, into it, kept apart: so it gains at least one state per pull, and after t pulls holds at least t plus 1. The reading with both bits cleared starts
with one state too, and at the pull after depth j, one lever sends its own states and a whole one-cleared group of at least j plus 1 into it, kept apart: so it
gains at least j plus 1. Add those gains from the first pull to the t-th and it holds at least 1 plus t(t + 1) over 2. Add the one state with both bits set and
the two one-cleared groups, and the total is 1 plus (t + 2)(t + 3) over 2: the grid's own count. The three-value box
needed extra room to commute. This one fits its best count with commuting built in.

All of those counts are checked by exhaustive search on the small horizons, where a computer can try every box.


Keeping every history

There's one way to make every step merge nothing, and it's the first way out of chapter two, put inside a machine. Keep the previous state on a list: each step, push where you were onto the
front of the list. The step you can see is the same as before, but the whole state now carries its past. Two different whole states can't land on the same one, because popping the list takes
you back. And the list gets one longer every step, so the run never comes back to a whole state it's been in. That's the fresh-state way of keeping, and on any memory you can build, the list
fills it, and then the merge is back.

So "this step merged, so it gave off heat" can't be said of the step you can see by itself. It's a sentence about the whole state, including whatever history is kept, and a physical model has
to say what's kept.


The counter and the heat

Does a machine's counter track heat? Here's the one test I think is good discipline, and it's a test of whether two assumptions can even hold together. Say you want both of these: every step
you've chosen to count gives off at least one unit, and nothing gives off more than its charge. Can both be true at once? Exactly when every step you've chosen to count is charged at least one.
If one is, take the heat to be the charge itself: both hold. If a counted step is charged zero, it would have to give off at least one and at most zero.

I should say how little that shows. The model that passes the test just takes the heat to be the charge, so it only shows the two assumptions don't contradict each other. It doesn't show the
counter tracks anything real. Still, it bites. Point it at a machine that computes at no cost underneath and counts every step that collapses some yes-or-no question, and it fails: such a machine
has free moves that merge, and no heat can be at least one and at most zero. A machine that prices the moves that raise its record and leaves its other merges free has both assumptions for the toll's
steps, and not for the rest. The hardware can give off heat on those free merges, off the ledger. The ledger counts the record and nothing else. A unit of cost is not a joule.

Three statements are in play here, and each points its own way. Energy at a scale, a unit of cost times so many joules, is a conversion; it points nowhere. "Nothing gives off more than its charge"
puts the charge above the heat: an upper bound. Landauer puts the heat above a loss of uncertainty: a lower bound. The test above says the assumptions can live together. That's compatibility, not
evidence.

Is there a heat prediction the permanent record makes that Landauer alone doesn't? No, and the reason is short. The smallest case, one state already yes and one flipping in, is "set a bit to one
whatever it held," which is the reset Landauer described and Bérut's group measured. The general bound, for squeezing m plus k equally likely states into m, is what Landauer's assumption gives for that
squeeze. What the counting adds is the structural half: on a finite machine, a reading that stays forces the raising move to merge. It doesn't say the state coming in is one of the two that meet, and it
doesn't supply the spread or the physical conditions a heat bound needs. Supply those and Landauer prices the uncertainty actually removed. The counting and the physics do different jobs.

There's one more way to put receipts next to merges, and it's exact. Draw the arrows of one run, and put a receipt beside each state the run leaves from: charge on entry into a parked state, and let the
parked state idle for free. Now mark every landing place that two different states in the run lead to, and count each mark once. Ask for one thing: whenever two different states the run leaves from land
together, at least one of them pays. Then the marks never outnumber the receipts. Every marked landing has a paid state behind it, and one paid state can't stand behind two marks, because it only goes one
place.

Try it with no going to yes and yes going to itself. Charge one at no and zero at yes. Entry pays the one, and every idle step after pays nothing: the merge is covered and the parked machine stays parked for
free. Now ask that parked yes-state how many merges you've watched. After one step you've seen only no leave: no merge yet. After two you've seen no and yes both lead to yes: one merge. The state in your hand
is yes both times, and it can't tell you which. Add a clock, and the two endings become yes at 1 and yes at 2, so you can read off the count. But draw the new machine, with the clock in it, and the clock keeps
those states apart. Keep both drawings on the table so you can see which arrows you're counting.


What you're entitled to

Let me total it up: what you've earned the right to conclude, and where there's still a way out.

You've earned this, with nothing but one next state for every state: on any machine run by one rule, finite or endless, a run that raises a reading and keeps it up either merges two of its own states or never
repeats one. You've earned this: on a finite machine, a move that raises a reading either forgets something or takes a reading down somewhere else. That's chapter three's merge or take back. You've earned this:
on a finite machine where a reading, once up, stays up, raising it makes two arrows meet, and if it raises several no-states at once, the yes-states together with the newcomers land on that many fewer places than
there are of them. That doesn't say each newcomer shares. And you've earned this: if two arrows meeting is charged, the toll follows, and if it's charged per halving, the size of the toll follows too. That's chapter
three's rule, derived, with every assumption named.

Now what you haven't earned, so you don't assume it. You haven't earned that forgetting costs anything in the world; that's Landauer, measured for beads and argued over in general, and here it's an assumption with
a name. Even granting it, it asks no heat of a run whose state is known, so what the physics forces is a floor on a device that has to work whatever it's holding. You haven't earned that any machine you'd want to
build is of this kind, either, and there are two easy ways to miss. A machine that keeps its running total inside its own state, as a number with no ceiling, has endlessly many states, so the finite argument fails for
it as a whole. And you can't patch that with a ceiling: a total that only climbs, in finite memory, either stops at its top, and then two different histories leave the same top value, which is a merge, or rolls over to
zero, and then it doesn't only climb. So any running total a finite machine keeps for itself is honest up to its width and no further. And a machine whose price list charges the raise but lets some other step merge two
states for free raises its box honestly and still doesn't charge for forgetting in general. Either one puts a machine outside these arguments as they stand, though a finite piece of it can still sit inside.

The smallest finite piece I could build where every condition can be seen to hold is this. Four slots, each with a flag: eight states. Three kinds of move. Stamp sets the flag and goes to the next slot, cost one. Jump
goes to a chosen slot, cost two. Next goes to the next slot, cost zero. Check it with me. It's finite. The flag never comes down on any move. Next forgets nothing: every state lands somewhere different. Stamp lands at
most two states together, a flag up and a flag down from the same slot, so one halving, and it costs one. Jump lands all four slots with the same flag together, two halvings, and it costs two. So every move's price is
exactly the number of halvings in its biggest pile.

And you haven't earned anything about what the flag means. Chapter two's chairs don't know what they're counting. The cost is for raising a flag that stays up. Whether raising it ever amounts to standing behind a real
fact was the subject of chapters eight through twelve.

One more thing, because it should nag at you. "Permanent" was chosen, by me. Why should a flag stay up? Merge or take back is the start of an answer: on a finite machine that charges for every merge, a flag that goes up
for nothing is a flag the same move takes down somewhere, and a record that can be silently taken back is exactly what the clay ball, the write-once disk and the hash chain were all built against. That's durability, one of
chapter four's five jobs, and it's the one I chose.

And "permanent" is an idealization, which I should say before a physicist does. No physical record lasts forever. A bit behind an energy barrier leaks over it at some rate, however slow, and a closed finite system comes
back around, which is Zermelo's point from chapter two. The arguments that start from a flag that stays up need it to stay up on every state the machine can reach, including states a given run never visits, forever. Weaken
that to "it stays up on the states that actually turn up, for as long as anyone cares," and merge or take back says what goes wrong: the move could take the flag down somewhere the machine could go and never does, and then
it isn't forced to merge at all.

One piece of a time-span version I can hand you. Take one move and repeat it from one start, forever. On a finite machine the states that run passes through are finitely many, so it falls into a loop. If the move forgot
nothing on those states, it would just shuffle them, and a shuffle brings every one of them back around, the start included, where the flag was down. So if the flag goes up along that run and stays up from some point on,
the move merges two states the run itself visits. No permanence is used anywhere in that.

Runs that mix different moves split two ways. If the moves are picked from outside, in any order, the answer is no. Take two states, one reading no and one reading yes. One move swaps them; the other does nothing. Run the swap
once and then the do-nothing move forever: the flag goes up at the first step and stays up for good, and neither move merges anything anywhere. The swap would take the flag down from yes if it ever ran there; on this run it never
does. But if the machine is closed, picking its next move from its own state, the run is one map repeated, and the single-move argument applies as it stands. And if the moves come in a pattern that repeats, one phrase played over
and over, treat the whole phrase as one move at the states where each playing of it begins, as long as the flag was down somewhere after the repeating started. It merges two of those, and the first move where their paths meet
merges two states the run visits.


The shape of the second law

Here's a comparison that's easy to read as more than it is, so I'll say first what it doesn't do. It doesn't give entropy's numbers. It doesn't derive Landauer. It makes no physical claim. It puts two drawings side by side and
points at the parts that line up, and every paragraph says which kind it is.

Shown, and only about the model. A window groups states: every state gives one picture, and the states that give the same picture form that picture's pile. A physicist calls the picture a macrostate and the states under it its
microstates; the word is different and the drawing is the same.

Shown, and only about the model. A Thiele machine's record never falls; that's in the definition. And it never climbs for free: the toll charges every climb, and the counter that adds the charges never goes down either. So a Thiele
machine carries two quantities that only climb along every run, the record and the counter, and the first can't move without the second moving too.

Shown, and only about the model. Keeping something costs room or a merge. On finitely many states a reading that rises and stays rises by a merge, and when each unit of price pays for one halving, the bits a run squeezes out are
bounded by what it paid. A noisy step that keeps the even spread can't raise a reading that stays.

A thesis, not shown. Put those beside the second law of thermodynamics and the shapes line up: a coarse description, the many fine states under each coarse one, a quantity that only goes one way, and a rule that the one-way change
has a price. My guess is that this isn't a coincidence, and that the second law, read as a statement about what a coarse description can keep, is the toll seen from the physics side. I can't prove that. The model has no temperature,
no energy and no probability unless an argument puts one in, and the bridge from a unit of cost to a joule is an assumption with critics, named in the last chapter. If the match is real, somebody has to show it with physics, and that
somebody isn't this book.


At the bottom: what I suspect and can't prove

This is underneath the arguments, so read it with the lights on. None of it is shown, and I'm not going to dress it up. It's why I care, and it's here, after the arguments and apart from them, so you can check that none of it got into
them.

Physics has a word for the moment a question closes: measurement. And the people who thought hardest about it keep describing it in this book's shape. They ran together for me until I put them on one picture. Flip a coin in a crowded
room. Before it lands, it could go either way. After, it's settled, somebody chalks it on a board, and the result gets copied out into the world, the light and the air, so many times that it can't be taken back and everybody who looks
agrees. Five pieces: the question, the landing, the chalk mark, the copies, the agreeing. Each person leans on a different one. Zurek, in chapter nineteen, leans on the copies. Rovelli's coin, in chapter six, has to hit the ground, so his
piece is the landing.

Niels Bohr, the Danish physicist whose institute in Copenhagen was where quantum mechanics got argued into shape, leans on the mark. In a talk at Columbia University's bicentennial in October 1954, printed in his 1958 book Atomic Physics
and Human Knowledge, he said "every atomic phenomenon is closed in the sense that its observation is based on registrations obtained by means of suitable
amplification devices with irreversible functioning such as, for example, permanent marks on a photographic plate": a door that swings one way. I first
found that line quoted in a 2026 paper by Mauro Dorato and Jan Faye, and their quotation runs on into a clause about water drops forming in a cloud chamber
that isn't on Bohr's page. The page is worth reading yourself. John Wheeler, the Princeton physicist who made the name "black hole" stick, went further in
a 1989 talk in Tokyo and leaned on the question: "every it," he said, "every particle, every field of force, even the spacetime continuum itself," gets
"its function, its meaning, its very existence" from "the apparatus-elicited answers to yes or no questions, binary choices, bits." He boiled it down to
"it from bit." As I read him, the coin has no face until something asks and something writes the answer down. How literally he meant that, I can't tell. And Peirce,
from chapter nine, long before any of them, leans on the agreeing: the settling worth trusting is the kind that has to answer to everybody. Laid out like that, they pair up. Bohr and Rovelli lean on a step that only goes one way, in the plate
and in the coin. Zurek and Peirce lean on many onlookers who agree, one with light and one with people.

Lay that next to everything in this book and the parts line up: a check that could have come out either way, a result that's now settled, a price paid in forgetting or in fresh states, a record that stays. I suspect that isn't a coincidence.
I suspect the event this book prices on a machine is the same kind of event physics calls a measurement, turning up in a different place. The forgetting is my step: Bohr only says irreversible, and getting from a record that stays to a merge or
to fresh states is chapter two's counting. Push on it and it gives at Zurek, for the reason chapter nineteen gave: copying onto fresh light merges nothing and uses up fresh states, which is chapter six's look that owes no floor. So physics' own
word lands on both sides of the line: the chalk on the paying side, the copies on the borrowing side. The landing I'd put with the chalk, and when chapter six pushed on Rovelli's paper it slid toward the borrowing side, the side of finding out.
So two pieces already stick out, and I'll leave them sticking out. That's as far as I'll take it: a suspicion.

John Bell asks for precision in those words. He was the Northern Irish physicist at CERN, and in 1990 he wrote a short, furious essay called "Against 'measurement'," with a list of words he said have no place in a physics that wants to be
precise. On the list: system, apparatus, environment, irreversible, information, and measurement, which he called the worst of all. I used half of them in the last few paragraphs. To turn the suspicion into a physical claim, each of those words
would need a stated meaning and a tie to the device. The arguments in this book work with the machines I've defined; anything physical says which further assumptions it uses.

That's the whole of it: what's counted, what's assumed, what's chosen, and one suspicion kept apart. The last chapter lays those out side by side.
