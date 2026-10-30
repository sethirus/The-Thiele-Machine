A box over any machine

For the whole book so far I've been building up a box and a tally, and you'd be right
to suspect that the whole thing is special pleading for one little board. So this
chapter answers that suspicion with no particular machine in it at all. Take any
machine that steps, anything with states and one next state for each. Put a box over
it that watches it, under rules I'll spell out. Then ask: what can the box be?

The answer is one shape, and it's a shape you can build from a cup and a die.


A cup and a die

Put a cup upside down on the table. The rule is: the first time a six comes up, turn the
cup right side up. There's no rule for turning it back over. Now roll a die twenty times.
If a six comes up, the cup turns over on the first one and stays turned over. Write down
which roll did it. That number is where the record happened, and the cup afterward is the
record. If no six comes up, the cup stays down.

To make the die part of a machine with one next state, write the twenty rolls down first and
read them off one at a time. The machine underneath is the list and a finger pointing at the
next entry; each step moves the finger one place, whatever the cup is doing. The question the
cup asks at each step is: is this entry a six? Nothing about the cup changes which entry comes
next.

The cup is a latch, the same thing you built with two boxes in chapter four. Electrical
engineers have had the circuit since 1918, when two British physicists working in London,
William Eccles and Frank Jordan, applied for a patent on a two-valve arrangement that
holds whichever state you last put it in. Their 1919 paper calls it a trigger relay. It became
the flip-flop, and the memory inside the device you're reading this on comes from it. Cut its
reset wire and what's left has one input, "set," and one rule: the new state is the old state, or
set. Once set, it stays set. The cup is that circuit with its reset wire cut.

Did anybody ever build a whole memory out of cups with no reset wire, on purpose? Somebody did, and
for a reason close to this book's. In the mid-1950s Wen Tsing Chow, an engineer at the Arma
division of the American Bosch Arma Corporation in Garden City, New York, was asked by the United
States Air Force, according to the Wikipedia history of the programmable read-only
memory, for a safer way to hold the fixed
numbers, the targeting constants, inside the guidance computer of the Atlas missile. What he and
his colleague William Henrich patented, filed in 1957 and granted in 1962 under the plain title
"Storage matrix," was a grid with a connection at every crossing, where you set the numbers by
taking out the connections you didn't want, or burning them out with too much current. The word
burn is right there in the patent, and people still say they burn a chip. A fuse blown in one stays
blown. That proves nothing here, because nothing below cares what a cup is made of. But it's good
to know the shape wasn't invented for a sheet of paper. Somebody needed it, for higher stakes than a
die.

Here's the claim, loosely first: every box that answers only to what the machine is doing, and never
comes back down, is a cup with no reset wire, turned by some event the machine passes through.


What "answers only to the machine" has to mean

The content is in the rules, so here they are.

Call the machine underneath the base: the part the box watches. Now build a bigger machine that has
the base inside it, plus whatever else you like, plus the box and a tally. The bigger machine has to
run the base faithfully: start where the base starts, step when the base steps, and stop when the base
stops. It can carry as much extra hidden stuff as it wants. The base doesn't get to see any of that,
and the extra stuff doesn't get to change what the base does.

Now the five rules for the box and the tally.

The box's next position depends only on what the base is doing right now and where the box is right
now. "What the base is doing" means the state it's in and, when it has more than one move from there,
the move it's making, like the stamp and the WORK move on the board from chapter thirteen. Nothing else. No clock on the wall, no hidden dial, no outside hand. I'll call that answering to
the machine.

The tally never goes down.

The step that turns the box up costs at least one. That's the toll.

Once up, the box stays up.

And some run, from a place the machine can start, actually turns it up. Otherwise the box is
decoration.

Here's what follows. Ask the bigger machine what it would do with the box down, above each state of
the base, and each move when it has a choice: does the box go up on the next step, or not? Call that
answer the event. Since the box answers only to the base, that's one answer per base state, or per
state and move; no hidden stuff can change it. Now take any
actual moment. If the box is down, the event is exactly what happens to it. If the box is up, it stays
up, whatever the event says. Put those together: the box's next position is "already up, or the event
holds right now." That's the cup's rule. The cup turns over the first time the event holds and never
turns back.

Look at which rules that used: only two of the five. Answering to the machine, and staying up. The
tally, the toll, and the reachable turn played no part. A cup is what you get from "answers only to the
base" and "never comes back down," all by themselves.

The other three rules matter for the other direction. Pick any base and any event the base can actually
reach. Build the cup on that event, price the turn at one, everything else at zero. Check the five rules:
the cup only looks at the base and itself; the tally only goes up; the turn costs one; the cup stays up;
and the run that reaches the event turns it. So every cup is a box like that too. Put the two directions
together: boxes that answer only to the machine and never come down are exactly cups, nothing more and
nothing less, over any machine at all.

The closest relatives are in proving programs correct, and they're old. Martín Abadi and Leslie Lamport,
in 1991, added "history variables" to descriptions of systems: extra state that records what has
happened and never steers the system. A history variable that only ever turns on is the cup. And there's
a logic for talking about the past, set out by Orna Lichtenstein, Amir Pnueli and Lenore Zuck in 1985,
with an operator "once": "once h" is true now exactly when h has been true at some point so far. A
program watching a running system keeps "once h" in a single bit with exactly the cup's rule, and Klaus
Havelund and Grigore Roşu built watchers like that in 2002. What this chapter adds is the other direction:
a box that answers to the machine and never comes down can't be anything else.

One thing about that argument cuts both ways: it never asks what the base is. You decide that, by deciding
what goes in the base and what goes in the extra stuff. Draw the line low, with the base being only the
machine's own working state, and "answers only to the base" is a real demand. Draw it high, put every
table and every rule into the base, and it's easy to meet. The cup comes out the same either way. So the
argument holds wherever you draw the line, and that's exactly why it can't tell you where a record's
meaning lives. The meaning lives in what the event looks at, and that's in the base, by how you drew it.
When you meet a real machine, ask it first what it puts below the line.


A base that never merges

What about a base where no two arrows ever meet? Can it carry a cup?

It can, and you can see exactly what it pays. Keep every earlier position of the cup on a strip that grows
by one entry each step, newest first. Then the whole machine still never has two arrows meeting: if two
whole states land in the same place, the strips are the same, so the old cup positions were the same, and
the base parts were the same because the base never merges, so the states were the same. But the strip gets
longer every step, so the machine never comes back to a state it's been in. That's the fresh-paper column
from chapter two. And on a machine with finitely many states, there's no fresh paper to be had, so a box
that stays up can't be turned on by a move where no two arrows ever meet. That's the chairs, again.

People who study processes that talk to each other ran into the same thing from the other side. Vincent
Danos and Jean Krivine, two computer scientists in Paris, wanted to pin down what a transaction is. In 2004
they built a version of Robin Milner's calculus of processes where every step can be rolled back, and in 2005
they modelled a transaction in it as a process that wanders freely through everything that can be undone,
until it does something declared impossible to undo: the commit. As I read it, they start from steps that
all come undone and ask what has to be added before anything sticks. This chapter starts from a box and asks
what the step under it has to be. Theirs is declared. I thought mine was forced by counting, since on a finite
machine the first turn of the cup makes two arrows meet whatever anyone calls it. Push on that and it gives: I
choose the event, and on a base that grows its history forever, nothing merges at all, so there my staying
up is declared too.


The clean start

There's an arrow of time in this, and I should say where it came from, because I put it there by hand. The cup
starts down. That's the only reason a turned cup means the event happened: it was down at the start, and only
the event turns it. Turn the cup up before the first roll and it tells you nothing about the die. So the clean
start is assumed. It's a small version of what the philosopher David Albert, in 2000, named the past
hypothesis: an assumed low-entropy beginning of the universe, an idea that goes back to Boltzmann. Several
accounts of why records point to the past lean on it. Whether every trusted record leans on it is their
argument, and I'm not settling it. Every result in this book that reads a turned cup as news that the event
happened assumes a clean start and starts from there. The cup argument above doesn't need it, and that's
exactly why, on its own, it can't say the event happened.

When I went looking for who else had found the arrow hiding in the start, I got five papers that read like
five unrelated answers. They lined up once I asked each the same question: what does the cup being down at the
start rest on? There are two places to put it. At the beginning, as a fact about how things started. Or in the
structure of what causes what.

David Wolpert, a physicist, sorted memory systems in 1992, and one of his kinds works only because it begins in
a prepared state, set up by a process that runs one way. That's the cup put down by somebody before the game.
Wolpert and Jens Kipper, a philosopher, put that sorting on firmer footing in 2024, and they say plainly that
they have no formal proof this kind can only remember the past. I trust them more for that sentence.

Aram Ebtekar and Marcus Hutter built a toy world in 2024 where every step can be reversed, imposed a clean start
on it, and got records of the past and none of the future. As I read their route, the clean start goes through
cause and effect first, and the arrow comes out of that. Thomas Blanchard, a philosopher, got the same
lopsidedness of knowing out of a condition on cause and effect, also in 2024. So he starts in the middle of
Ebtekar and Hutter's road. One is a toy world and the other is philosophy, and the fit between them is my
reading.

And Carlo Rovelli, two years before his paper on the cost of choosing from chapter six, studied traces in a 2022
paper called "Memory and Entropy," and concluded that a memory turns a low-entropy start into information you can
use. He's at the first place, and he says what the beginning gets spent on. Read next to the cup: that's the
blank the record uses up. The cup can say yes once because it started at no.

So does the cup explain why records point backwards? It doesn't, and I'll say that plainly. The step runs forward
and the runs start clean, and anything built on those two can only hand the arrow back. Even the strip that grows
forever starts empty, so it leans on the same blank. On the map, this book sits at the first place, with Wolpert
and Rovelli, and it sits there by assumption.

Constructor theory, David Deutsch and Chiara Marletto's way of writing physics from chapter two, has a 2025 paper on
time saying that laws stated as which transformations are possible can't mention time at all, so duration has to
come from a second system you count, a clock. This book is in that position by construction: the only time in it is
the machine's own steps. The hidden clock in the next section gets thrown out by the first rule, which read next to
them is a rule about which system is allowed to be the clock: the one being recorded. But their laws have no step in
them, and I put a step into the base by definition. So I'm in their position only at the far end of their argument,
where a clock already exists. The base is my clock, and I assumed it.

Physicists have built this cup on paper in quantum mechanics too, and it behaves the way the reversible base above
says. The question that sorted them for me is where the cup puts what it forgets. Klaus Hepp, in 1972, wanted a
measuring device inside quantum mechanics itself, and studied a particle that flips spins in a long chain as it
passes, now called the Coleman-Hepp model. I haven't read Hepp's paper itself; I know it from John Bell's,
which took it apart in 1975: the record is exactly definite only in a limit that's never reached, an endlessly long chain and an endless time. That's the fresh-paper column, a history
that never ends. Jonathan Halliwell, in 1999, used a two-state detector that flips once when a particle passes and is
kept from flipping back by a large surrounding environment, and his summary calls it "effectively irreversible." I
like that he puts the word "effectively" right there where you can see it. And Murray Gell-Mann, who named the quark,
and James Hartle gave the property a name in 1995: the permanence of the past, past alternatives that stay settled as
the story goes on. Hepp's chain had to be endless. Halliwell's had to live in an environment. Mine stays up, and the
toll writes a unit on a tally. That's fine in a model of computation, and it's exactly where this stops being physics.


Both rules do work

A result with two conditions should have two counterexamples, one for each condition dropped. It does, and they're the
two ways a record goes wrong in the world.

Drop "stays up." Take a base that just counts, and a box that flips at every step: up, down, up, down. It answers to the
machine. It doesn't stay up. And it's not a cup on any event. That's the coin from chapter three, the toggle: working
state dressed up as a record. If a take-back has to stick, it's a second cup, "withdrawn," which is how lists of revoked
web certificates actually work: you add an entry; you never delete the certificate. Alin Tomescu and his coauthors built
add-only lists like that for public logs in 2019, and a revocation fits exactly: it goes in once and stays. Two cups can
also look at each other: try it with two cups where the second only turns on an even roll if the first is already up, and
you'll see the second can never turn before the first. Each is still a cup; its event just gets to look at the other one.

Drop "answers to the machine." Take a base that counts, and a box that turns up at the fifth tick of a hidden clock, whatever
the base is doing. It stays up, and it doesn't answer to the machine. That's a timestamp. A timestamp says when, not what
happened. A record switched by an outside party or a clock records that party or that clock, and leaves the computation
out. Try it with the written-down die rolls: keep a second, hidden tally beside the list, and turn the cup when that tally
reads five, then move both the tally and the finger. Start two runs at the same place on the list with the cup down, but one
with the hidden tally at five and one at zero. The next cup positions disagree, although everything about the base agrees.

One more thing about the timestamp, because it's sneakier than it looks. Start it in step with the base, hidden tally and
finger together. Then, on every state its runs actually reach, the hidden tally equals the position in the list, and the
timestamp is exactly the cup on "this is position five." The first rule only throws it out because the rule looks at every
state, including the out-of-step ones no run from a clean start ever reaches. So the honest version is: a timestamp with its
clock free to start anywhere fails even on the states its runs reach. Started in step, it's a cup on the runs it has.

Permanent but not answering to the machine is a timestamp. Answering to the machine but not permanent is a toggle. A record is
the thing that's both. That's the most useful single sentence in this book for looking at systems other than the ones I build.


Arguing with cups

People who study arguments built the two-cup rule for debates. Give each speaker a row of cups, one for every claim they've made.
Everybody I read in this field is answering two questions about those cups: whose hand turns them, and can they come back down?

C. L. Hamblin, an Australian philosopher and logician who also came up with reverse Polish notation for early computers,
wrote Fallacies in 1970, and it has a chapter where each speaker has a store of what they're on the hook for, and the rules of the
debate update it, not the speaker. I haven't read that chapter itself. That's "answers to the machine," for
arguments: the speaker's hand is kept off the cup. Henry Prakken, who works on AI and law, built debate games in 2005 on stores like
that and made the claims sticky: a claim can be taken back only after it's been challenged, and taking back has a cost. He also floats
a rule that once a speaker takes a claim back, they can't take it on again, which is a revocation that stays revoked. Erik Krabbe, an
argumentation theorist, names the awkward part in 2001: taking things back is frowned on, and yet settling a dispute takes somebody
taking back a doubt. A store that never gives can't settle anything, and a store that gives whenever asked isn't a store. This book
answers Krabbe with a price: a take-back is a second cup, "withdrawn," and turning it costs at least one like any other turn. Where mine
gives is Prakken's first condition: nothing in my cup asks why the second cup turned. Its event can look at the base and the first cup,
and nothing requires a challenge.

The same field has something that looks a lot like earning. In Phan Minh Dung's 1995 setup, arguments attack each other, and the most
careful way of accepting them starts from the arguments nobody attacks and keeps adding the ones they defend. Things go in and never come
out: a row of cups turned one at a time. Pietro Baroni and Massimiliano Giacomin in 2007, and Martin Caminada in 2014, worked out a
stronger version where every accepted argument is defended by others that don't lean back on it, so the support bottoms out. That's an
earned claim, in argument form. Notice the bottom, though: an argument nobody attacks gets in on a check that can't fail, and chapter
eight says a check that can't fail establishes nothing. Turn that on my own cups, because it lands. My first turn needs only that the
event holds, and I charge one for it, and a charge isn't a check. So my earned records bottom out the same way Dung's do, in something let
in without an argument. The one difference is that mine pays to get in.


A box that can change its mind

A box that's allowed to change its mind isn't lawless. It's somebody else's subject. Count how many times the cup may be turned. Once,
from down to up, is the cup. More than once and you're somewhere else, and the people who went there sorted it by how many turns are
allowed, and by how long the game runs.

The philosopher Hilary Putnam and the computer scientist E. Mark Gold, in back-to-back papers in 1965, looked at questions a machine
answers by guessing and revising, where the answer is whatever the guesses finally settle on. Putnam's paper says outright that you're
never sure you've got the right answer. What kind of answer can't you ever be sure you have? The way I read it: the cup's position at any
moment is the current guess, the answer is where it ends up, and nobody watching can tell when it's done moving. Yuri Ershov, a logician in
Novosibirsk, sorted those in 1968 by how many changes they're allowed. That's how Rod Downey, Carl Jockusch, Timothy McNicholl
and Paul Schupp describe his ladder in a paper printed in 2015; I haven't read Ershov's paper.
Allow one change, from no to yes, and you get exactly the sets a program can list, the bottom rung. That one you can check yourself. If a
program lists the set, guess no for every number and switch to yes when the number shows up on the list. Going back, if every guess flips
at most once, from no to yes, run all the guessing side by side and write a number down the moment its guess says yes.

Now put Putnam's worry on the cup, because it lands. On the bottom rung, a yes is final the moment it shows up, and a no never is, since
down means "not yet." A single cup can establish that something happened, and can never establish that it didn't. A final no would take a
second cup, turned by finding a reason, and that's the two cups again. That's what the bottom rung costs. This book stays on the bottom rung.

The ladder doesn't stop at endless time either. A definition that only ever adds, stage after stage, and keeps everything at each limit, is
a cup run through the infinite; Wayne Richter and Peter Aczel set those out in 1974. Let it take things back and keep only what stays put from
some stage on, and you have what John Burgess, in 1986, called quasi-inductive definitions, which he met in theories of truth that grew up
beside Saul Kripke's 1975 theory of truth built up in stages. And Joel Hamkins, the same set theorist as in chapter one, and Andy Lewis let a
Turing machine keep running past endless time in 2000. At each limit, a square keeps its value if it settled, and reads 1 if it kept flipping
forever. Their favourite trick is the toggle: flash a flag every time a guess changes, and at the limit the flag is on exactly when the guess
changed endlessly often. Past infinity, the toggle is the clever one, because a cup can only tell you a thing happened at least once. I threw
the toggle out anyway, and I'd do it again, because before the limit its reading can't be leaned on, and nobody using a real machine gets to
wait for a limit.

One finite-time fact belongs beside that, so nobody reads too much into permanence. Hao Wang, in 1957, described a machine whose only write is
to mark a square and which can never erase one, and it computes everything a Turing machine does. Permanence of a machine's own memory costs
it no computing power, given an endless tape: each mark goes on a square nobody marked before, which is fresh paper again. What this book prices
is a box raised by a step that has to work whether or not the box is already up. So the cost is in what a box can claim, not in what the machine
can compute.


One shape, two choices nobody forces

"There's only one way to carry a record" packs three different claims into one sentence, so take them apart.

Given the toll and a fixed price list, is there only one way to keep the books? Yes, on every state you can reach: that's chapter eleven's one
honest count, and it assumes the price list.

Is every box over a base the same machine, charges and all? No, and the counterexample is embarrassingly simple. Take any box over any base, and
give it a new tally that adds each step's old cost plus one more, whatever the step is. Walk the five rules. The box still answers only to the base
and itself. The tally still only goes up. The turn still costs at least one; the toll is a floor and a surcharge only raises it. The box still stays
up, and the same run still turns it. So the surcharged machine passes, and it isn't the one you started with. Do it with the cup and the die: charge
one for every roll, six or not. The cup turns on the same roll as before. You've changed the cost and nothing about the record. A machine that charges
for running time passes, and it isn't the one that doesn't.

And the second choice nobody forces, the one that still surprises me: which event is the record? Nothing in the five rules picks it, beyond the
demand that some run reach it. You saw that above: for any event the base can reach, the cup on that event, priced at one, passes. Do it with the
die. One cup turns on the first six. Another turns on the first one. Both pass. Roll a one first, and until a six shows up, the two cups disagree about
whether anything has happened. So which permanent box counts as "the record" is a second thing nobody forces on you. The price list is one free choice
and the event is the other, and that second one is what a later chapter is about: what, if anything, makes "a check passed" the event worth recording.

Now let the cup wobble. Say whatever turns it over sometimes does and sometimes doesn't, with chances you could write on a card. Does fixing the price
list fix the chances? No: two cups with the same possible moves and the same charges, one turning with a fair coin and one with a two-to-one coin, pass
the same rules and aren't the same. And a cup that, from down, can either stay down or go up, depending on chance, isn't a cup on any one event at all.

And is there one set of states, up to renaming, that every box machine has to have? No, because the bigger machine can carry any hidden stuff it likes.


What leaving the base open buys

So here's the answer to the suspicion I started with. The box isn't special pleading for one board. Over any machine that steps, a box that answers to
the machine and never comes down is a cup on some event, and the argument doesn't care what the machine is. What a particular machine adds on top of the
cup is a price list and an event, and both are choices. The surcharged cup shows the first: the price can change and the record doesn't notice. The two
cups on one die show the second: the rules are happy with either event. That's also why the chairs in chapter two never needed the word "check": they force
two arrows to meet in whatever stays.

And chapter five already showed what happens when a box has more than two positions: it's a row of cups, one for each line, each one a cup like this one,
where each cup's event may look at where the row already is.
