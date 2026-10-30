Which box is worth keeping

Everything so far leaves one choice open. Chapter fourteen showed that a box that answers to
the machine and never comes down is a cup on some event, and that the event is a choice: the
two cups on one die were both happy under the same rules. Chapter seventeen found five real
systems that each picked a different event. And in this book I picked one too: the established
record from chapter eight, a box that goes up only right after a check of the very claim it
records has passed. So I owe you an answer to the obvious question. Is that just my choice, or
is there something about how people and machines lean on records that picks that event out?

What I have is a thesis, in the same sense the Church-Turing thesis from chapter one is one: a
claim tying things I can define to the world, which no proof can settle. Nothing before this
chapter depends on it. The cups, the windows and the counting hold whichever event a system
records. What follows is where the idea came from, what exactly it claims, and how you'd catch it
being wrong.


A dial and the light off it

The shape comes from physics, and I want to tell you exactly where, because I borrowed a word and
didn't get to keep all of it.

Quantum mechanics has a famous problem. A system can be in a blend of states, and when you measure
it you find one definite state, and nobody agrees on what measuring did. In 1981 Wojciech Zurek
asked a sharper question: of all the ways a measuring device could end up, why does it end up
recording one particular kind of quantity, the position of a pointer on a dial, say, and never some
blend? His answer, built up over twenty years and summed up in a 2009 paper called "Quantum
Darwinism," is that the environment decides. The air, the light, the table, everything the device
touches, keeps interacting with it, and only certain states of the device survive that; those are what
he calls the pointer states. More than that, the environment picks them out and then copies them. The
light bouncing off a dial carries the dial's reading to every corner of the room, over and over, so a
thousand people can each catch a different scrap of that light and all agree on where the pointer is,
without any of them touching the dial. On his view, being objective is being copied like that: a
property is objective when many separate pieces of the world each carry it.

Zurek isn't the only one behind it. Fernando Brandão, Marco Piani and Paweł Horodecki in 2015 proved an
approximate version: for most small pieces of a large environment, what each piece carries can be
matched, up to a small error, by measuring the system in one common way and handing each piece the
result. The error and the share of exceptions are part of their theorem, and agreeing on outcomes also
needs the pieces to carry enough about them. Xiao-Liang Qi and Daniel Ranard in 2021 tightened the bound
on the exceptions. Neither says every observer gets an exact record, or any useful record at all.

What I borrowed is the shape. Take a machine together with everything around it that reads, stores and
relies on its records. The established record is to that crowd what the pointer reading is to the room:
the thing that gets copied everywhere. It's a good shape, and I think it's the right hunch. But I'll be
exact about what survived the trip, because my word "copied" does less work than his.


The claim

Here's the claim, said plainly. Of all the events a machine could put on its bill, the ones its price
list charges for and its counter adds up, the established record is the one whose marks get copied and
relied on by parties who didn't make them: checked, stored and acted on in separate places that share
nothing else.

Copying alone can't be the test. A system run as many copies, like chapter seventeen's chains, copies
everything it holds to every copy: the gas a block used, as faithfully as the word final. So rival events
get copied too. Reliance doesn't split them apart either. On Ethereum, since a 2021 change called
EIP-1559, the gas the last block used sets the next block's base fee: aim for a block half full, and if
the last one came out completely full, the base fee goes up by an eighth, so 800 becomes 900; if it came
out empty, it drops by an eighth, to 700. Every copy reads that number and acts on it. That's an event
nobody would call an established record, copied and relied on by parties who didn't make it.

So examples can't show that only the established record gets copied and relied on. What the thesis has to
ask is narrower: whether some kind of reliance, picked out for its own reasons, selects that event, and
whether that selection gives a reason to charge for it. Any exact test fixes its readers and their actions
in advance. It can test those choices, but it can't choose the real readers for me.

There's a second handle on the same question, from chapter three. On a finite machine, every move that
settles something for good is a move Bennett's rule charges, and that argument never used the word "check."
So it points at a narrower candidate: the events worth pricing are the ones that write a record no later step
can take back. The established record is one of those. As an exact answer, though, that candidate is wrong,
because the three cards in chapter three showed a charged move that takes a star back. Whether the records
that get copied and relied on are the permanent ones, and whether being copied and relied on picks out
anything the merging doesn't, is what the two handles have to settle between them.

I can see two holes in this from here, so you don't have to find them for me.

The first is a missing step. Even if the world copies established records more than any other kind, "copied"
doesn't give you "priced" by itself. Something has to connect them, and the best candidate I have is about
incentives: a record that many separate parties copy and lean on is exactly the record worth forging, so it's
the one where a price buys the most protection. That's reasonable, but it's an assumption. The thesis states the
connection as something to test. It doesn't explain it, and nothing in this book does.

The second is a circle. If "established record" just meant "the record other people rely on," then of course it
would be the one that gets relied on and copied, and the claim would say nothing. So the event has to be picked out
without mentioning reliance, and it is: a box going up for good right after a check of the same claim passed. You
can find that in a run without asking who reads it. Whether the world copies that event more than its rivals is then
a real question, and it could come out no.

Now the word. Fix, for some crowd of readers, a test for whether an event is copied and relied on by parties who
didn't make it. That test has to come from somewhere other than the established record, or the whole thing repeats
a definition. Call an event a pointer, after Zurek's dial, if it passes that test and, on every state the machine can
actually reach, every other event that passes holds wherever it does. There may not be one. But there can't be two
that disagree: if two events both pass and each holds wherever anything that passes holds, then each holds wherever
the other does, so on the reachable states they're the same event.

So here's the thesis, which I call the pointer thesis. Take record-keeping the way people actually run it, modelled
faithfully. Then two things. First, the established record is the pointer: it gets copied and relied on by parties who
didn't make it, and every event that gets copied and relied on that way holds wherever it does. Second, every record
the system puts a price on gets copied and relied on by parties who didn't make it.

It's a thesis and not a theorem because of two words: "faithfully" and "actually run." Those are what tie the definitions
to the world, the way "everything a person could do by following rules" does for Church and Turing, and no definition can
do that job. The other thing it needs does have an exact meaning. Readers have separate carriers when each reader's view
depends only on its own part of the world, and any two readers' parts could be set independently of each other. The states
the machine reaches can still tie those parts together; the thesis asks for agreement there. Everything else, which systems,
which states, which event, which prices, goes in as input. The thesis proves nothing about which real systems fit it.


How much of the borrowed shape survived

Zurek's copying comes in degrees: each piece of the environment carries almost all of it, with a little lost. And it needs
the pieces to be separate: different people reading different parts of the light.

My first try at writing this down had neither. It was the no-loss case with no separateness at all: a crowd of readers, one
yes-or-no each, and an event counted as copied when every reader's yes matched it exactly. Nothing in that says two readers
draw on different parts of anything. Picture three readers all looking at the same single switch. They agree perfectly, and
they're one reader three times. So I'd kept the word and dropped the separateness that makes his version mean "objective."
That's why the thesis above asks for separate carriers, and it's also why separate carriers aren't enough on their own: three
separate switches can be set any way at all, so something, a copying process, has to put them in step before they agree.

The separateness I dropped is exactly what the thesis's closest published neighbour keeps. Jess Riedel, Zurek and Michael Zwolak
in 2016 took histories of a closed quantum system, the story a whole run of events tells, and asked which of them the world keeps
records of in many separate pieces of the environment. As I read their paper, records kept in many separate pieces make a history
behave, so ordinary yes-or-no reasoning about it works, and they pick out a small set of histories from the huge number that merely
behave: in their words, an objective past. That's "what gets copied is what counts," in quantum form, with the separateness in it,
and it came before this book. Jonathan Halliwell, in a 1999 paper called "Somewhere in the universe," had already carried the link
between records and well-behaved histories from the simplest starting states to messier ones, where the records still exist but
can't be perfect.

There's a deeper mismatch in the borrowing, and it runs against this book, so it goes here. In Zurek's picture the whole thing,
system and device and environment together, follows quantum mechanics' rule for a closed system, and that rule never lands two
states on one. Every step can be run backwards. So seen from the whole, the environment's copying is just copying: the dial's
reading gets written onto fresh light, and no two states anywhere meet. That's chapter two's way out, fresh paper, and chapter six's
blank page. It isn't a claim that a closed system goes on to new states forever; a finite closed system can come back around.

Look at the dial alone and it's different, because you've thrown away how it's tied up with the light. Quantum states carry a phase,
a part that only turns up when things interfere. Take two states of the dial that are as different as two states can be, differing only
in that phase. Let the environment wash the phase out completely, and the dial on its own ends up exactly the same from either start. Two
arrows met, in the dial's own description. If the washing out is gradual, they only get harder to tell apart, and never exactly equal at any
finite time. So an exact merge in a part of the picture, a slow loss of what you could tell apart, and a flow of heat are three different
claims. Getting a heat cost out of any of them needs more: how the thing was prepared, what the change in disorder was, and the conditions
that make heat the right word. Copying by itself supplies none of that.

So the thesis points at copies being kept and used, and the quantum account explains particular ways information spreads and becomes
readable. It doesn't attach this book's toll to the copying.

A published no-go cuts closer still. Philippe Allard Guérin, Veronika Baumann, Flavio Del Santo and Časlav Brukner gave an argument in 2021
that, under assumptions that look natural in quantum mechanics, an observer's own record of an outcome at two different times can't share one
reality: no joint chance for the two, depending in the simple straight-line way on the starting state, matches what quantum theory predicts for
each. A record that lasts, for the one holding it, is exactly what gets into trouble once the whole is treated as never merging anything. It
isn't a theorem about my machine, which isn't quantum. It's still the strongest published reason I know to hold the word "permanent" loosely
when a physicist is in the room.

Which leaves the question to ask of any borrowed shape: has anybody checked the original? For a long time quantum Darwinism was a theory
without a lab. Then, in 2018 and 2019, three groups working separately, in Italy, China and Germany, went looking for its fingerprint, as
Philip Ball's 2019 report in Quanta Magazine tells it. The German one, at Ulm, with Zurek among the authors, watched the spin of a single
defect inside a diamond and the carbon atoms around it, and saw the copying the theory predicts: the defect's state turned up copied in its
surroundings, and it didn't take much of the surroundings before more of them told you nothing new. The other two did it with light. Is that
the bottom? Not by a long way, and the people involved said so. Zurek himself pointed out that the experiments with light make their copies
artificially and that the diamond's environment is small, and others noted that all three are sketches of a real environment and don't rule out
rival accounts. So the shape I borrowed has passed some first tests in a lab, at the scale of a handful of atoms or bits of light, with those
cautions written on it. None of that touches the thesis here, which is about machines and never rested on quantum physics. It changes how I hold
the picture: what I borrowed is a lead somebody is checking. It isn't settled, and I don't get to lean on it as if it were.


What the thesis asks of the examples

Three comparisons would test it, and each one could come out against it.

First, look at a record a real system puts a price on. Do parties who didn't make it copy it and rely on it? A priced record that nobody else
relies on breaks the second half.

Second, put the established record next to its rivals. If some event the established record doesn't cover gets copied and relied on to the same
standard, the established record isn't the one pointer. The base fee from a moment ago is a candidate: on Ethereum it's read and acted on
everywhere. Whether it passes a test of reliance that was picked for its own reasons, and not to let it in or keep it out, is exactly the kind of
thing the thesis has to face.

Third, give the readers separate carriers in a faithful model, and ask whether the established record itself passes. Each reader has to be able to
recover the event from its own view. A reader whose view stays the same whether the event happened or not can't; that's chapter seven's wall,
where nothing about the box comes through. Naming a crowd of readers isn't enough. The model has to say what each one can read and what each one
relies on.

Those comparisons are the evidence the claim about the world asks for. The exact test only turns into a definite question once the model and its
readers are chosen.


Where the argument has got to

This is the last choice the book has to own, so here's the whole road behind it, with what was shown kept apart from what was chosen.

Chapters one and two showed that on a finite machine, settling something for good makes two arrows meet, unless the machine uses fresh paper on every
tick. Chapter three chose a price on two arrows meeting, Bennett's rule, and showed that with it, every move that settles something for good costs at
least one. Chapter four built the smallest machine where that happens. Chapter five showed that a record with more than two positions is a row of cups,
that a straight line of stages needs exactly one cup fewer than it has stages, and that the toll on the row charges at least one on any step that turns
up a cup. Chapter six showed that looking can be free: a look uses up a blank page, which can be handed back, and owes no floor. Chapter seven showed that
a window with a clash can't price exactly. Chapter eight chose what "established" means: up only right after a passing check of the claim. Chapter nine
drew what settling looks like, a sorting with a door that only swings one way. Chapter ten said what structure is and which ruler I chose to measure it.
Chapter eleven showed that once the price list is fixed, the counter is arithmetic, and that a counter that goes down gets leaned on where it goes down.
Chapter twelve showed what a ticked box lets you lean on, and no more. Chapter thirteen chose the meaning of insight: a distinction made to stay, with
price and depth kept apart. Chapter fourteen showed that over any machine, a box that answers to it and never comes down is a cup, with two choices left
open, the price list and the event. Chapter fifteen showed what the toll pays for when the machine is finite, the record only grows and the uncovered
machine forgets nothing: crushing two states of one pile. Chapter sixteen showed that a machine's own shortcuts can't be judged from inside it, and that the
commitment can still be recorded. Chapter seventeen found that of five real systems, read through my copies, one charges a fee at the write. And this chapter
proposes the event, and says how the proposal could fail.


Does the list of requirements pick out the toll?

One question about the price itself is still open. Do the requirements I've put on a price pick out the toll and nothing else? If a short list of them
left only one price standing, that would settle it. The lists I tried don't, and the no is small enough to check on three states.

Call them blank, once and twice, with once and twice reading yes. Two moves. The flip takes blank to once and leaves the other two where they are. The
smooth takes once to twice, and leaves twice and blank alone. Draw the arrows. The smooth lands once and twice both on twice: two arrows meet, so Bennett's
rule charges it. The flip lands blank and once both on once, so the rule charges it too. But only the flip raises anything, and only from blank. The smooth
goes from yes to yes.

Now try requirements that never mention the reading. No charge on a move that changes nothing. No charge on a move that forgets nothing (both moves here
forget, so this one asks nothing). The same cost if you rename the states (the only renaming that keeps both moves the same is leaving every name alone, so
this asks nothing either). A total that adds up along a run. A cost that depends only on the state and the move. And a cost of one on the flip from blank.
Let the price depend on the state as well as the move, the way chapter seven's clerk was allowed to. Go through the six steps one at a time. The flip from
once and the flip from twice change nothing, so they're free. The smooth from blank and the smooth from twice change nothing, so they're free. The flip from
blank costs one. That leaves the smooth from once, and nothing on the list says a word about it. Charge it nothing, and you have the toll: one on the raise
and nothing else. Charge it one, and you have a price on merging. Charge it two, and that passes too. The list can't choose.

What chooses is a requirement that names the record: over any run, the total is never more than the number of times the reading went up. The smooth from once
raises nothing, so it has to cost nothing. With the floor from the toll, that leaves exactly one price, one per raise and nothing else, which is chapter seven's
step price again. So the uniqueness is real, and it's small. It holds once you've said which reading you're charging for. And which reading deserves the charge
is the pointer thesis, which is still a thesis.

The uniqueness results that do exist are about pricing information lost, and they're worth a look because they say what kind of charge a price on merging is.
John Baez, Tobias Fritz and Tom Leinster in 2011, mathematicians who work in category theory, the mathematics Lawvere's diagonal from chapter sixteen came from,
asked what a measure of information loss has to look like. As I read their paper, they proved that for maps that keep track of the probabilities, Shannon's
entropy, up to a constant factor, is the only measure of information loss with three natural properties: it adds up along a chain of maps, it mixes the way
probabilities mix, and it changes smoothly. János Aczél and Bruno Forte, mathematicians at the University of Waterloo who worked on functional equations, and Che
Tat Ng, who had taken his doctorate there under Aczél in 1971, asked in a 1974 paper which entropies deserve to be called natural, and proved, by their account,
that the ones with a short list of natural properties are exactly the mixtures of Shannon's and Hartley's, where Hartley's is just the log of the count. So even
for merges, the choice between the average and the count is a real choice. Both price merges. Neither prices raises, so neither picks out the toll, and that's
the three states again, at a larger size. On the other side of the fence, Luciano Pomatto, Philipp Strack and Omer Tamuz in 2023, economists at Caltech and Yale
who asked what learning something should cost, proved, by their account, a uniqueness result for what it costs to get information, when running the same
experiment twice costs exactly twice as much as running it once. That prices producing a signal, which is a different matter from chapter six's copy onto a blank page; the copy owes no
floor and borrows fresh paper.

Most of that isn't a machine. The arguments in this book are about any states and any moves, and chapter seventeen's five are small copies of somebody else's
systems. The smallest machine is the box from chapter four, with every part named and every price written down. That's where everything above has something to
bump into. If a statement up there doesn't mean what I think it means, the box and the five copies are where it shows.

Every price in this book so far is one I wrote down. Whether the world charges anything like it, in heat, is a question for physics, and it's the next chapter.
