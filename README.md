# The Thiele Machine

The Thiele Machine is an abstract mathematical model of states, moves, a reading of each state, and the price of each move.

In plain terms, a Thiele machine is a thing, the directions it can move in, and a price on each direction. A direction turns the thing into the next thing. Look at the thing and you can read off how much is settled in it. A direction that makes a distinction stay is never free. From where the thing starts, some run of directions makes one stay, and no direction undoes it. This repository contains the monograph that argues it, a plain-text introduction, a compact specification, and a formal check of the same statements.

[Monograph](monograph/monograph.pdf) · [Mathematical specification](monograph/thiele_machine_math_spec.pdf) · [Plain-text introduction](THIELE_MACHINE.txt)

## The point

Take anything that can be more than one way and isn't yet any of them for good: a bead that could sit in either of two dips, a square of paper with nothing on it, a question nobody has closed. Now let it settle one way, and keep it there. Something is the case now that wasn't a moment ago. That is a distinction that stays. Nothing becomes something for free: under a rule that gives every state exactly one next state, keeping something settled takes a merge somewhere in the run, two states landing on one, or an endless supply of fresh states.

Structure is made of exactly this. The smallest distinction there is sorts the ways a thing could be in two and holds one side: a bead in the left dip and not the right, a mark on the page and not off it. A grouping, an order, a relation a later move leans on, a fact somebody found out and wrote down: each is a distinction that stays, paid for the same way as the bead in its dip. Insight, in the sense the model can price, is a kept distinction. The toll requires a charge when it's raised; merely remaining up requires no further charge. Repeating a priced move still pays that move's price. That is what No Free Insight names: the toll on making a distinction stay.

Established is the sharpest case. Two computers can end with the same answer, and only one of them checked it. The difference between them is a distinction one of them never kept. A record that a claim was checked and closed is a distinction that stays, with a check in front of it, and it's paid for the same way. The point is the distinction that stays, and what keeping it takes.

## What keeping takes

Sort the ways a thing can be into two piles: the states where it hasn't settled yet, and the states where it holds the answer. Say there are three states that hold it. Once the thing enters any of them, every later tick must leave it in one of those three. Now include the unsettled state that first enters them. Four sources have their next states among three places. At least two arrows meet.

Nothing depends on the number three. With $K$ holding states and one unsettled entrant, there are $K+1$ sources and only $K$ landing places.

Suppose instead that the rule always gives different successors to different states. Its holding run cannot revisit a state. If it did, walk backwards from the two equal visits. Their predecessors must agree too, because different predecessors never land together. Keep going until the earlier visit reaches the unsettled state. The later visit is still holding the answer, so it cannot be that same unsettled state. Avoiding the merge therefore requires an endless supply of distinct holding states.

For a finite holding interval the count is sharp. Line up $K$ held states after the unsettled state and fix the last one. The first $K$ sources have distinct successors. Include the next source and the final two arrows meet. The merge need not involve the state that just came in: a chain can run through the held states before it meets.

That is counting, and it needs no price and no physics. The definition below is where the price goes.

## The definition, exactly

Give the pieces names. $S$ is the set of states, $I$ the set of moves, and the step $S\times I\to S$ turns a state and a move into the next state. Each move has a price $c:I\to\mathbb N$. A reading $r:S\to R$ sends each state to a place in an ordered set $R$: for any two places you can ask whether one sits at or below the other. A move makes a distinction stay when it carries the reading somewhere not at or below where it was. The one rule is the toll: such a move costs at least one. That much is a priced record system.

A **Thiele machine** is a priced record system whose reading no move ever lowers, and that some run, from a start you designate, raises. A reading that never falls is what I call a **record**. Nothing else is assumed of the order, and nothing says what the record is about. A ledger that only climbs, and a window onto what an outside observer sees, come in when a result needs them.

The smallest record has two positions, no and yes. Then the reading is a yes-or-no question about the state, making a distinction stay is turning no into yes, and the toll says that move costs at least one. This smallest case is one you can point at: a lamp beside a box, a stamp on its side, a flag that goes up. The flag is not the record. It is the smallest question you can ask of one. The book states the general case first and derives the flag as its two-point instance.

## The smallest machine

The smallest Thiele machine has two states, no and yes, and one move that costs one. The move sends no to yes and yes to yes. The reading is the state. It can rise, it never falls, and the rise is priced. Nothing smaller meets the definition: one state has a constant reading, and on two states read as themselves every member has this very move, since a move on two states that merges nothing either changes nothing or toggles, and a toggle turns yes back to no.

Notice what is already inside it: two states land on one. The merge that keeping takes is forced at the smallest size there is. A fuse, a bead that drops into a dip, a stamp on a box, are this machine.

The Thiele Machine is that definition. It is a machine the way Turing's machine is one: an abstract model you can reason about. I named it after myself, on purpose. I wanted to call it the meta machine, and in 2021 a company took that word, so I went one level up and put my own name on it, half a joke and half a stake in the ground. Turing got a machine; here's mine.

## What the definition asks, and what it doesn't

One theorem comes with the definition and nothing else. A run that starts with the reading at no and ends with it at yes pays at least one. That is the universal floor. It holds for every Thiele machine, and for anything at all that obeys the toll. The toll on its own is nearly empty on purpose: a clock that charges one for every move obeys it whatever reading you give it. That's why the toll isn't the whole definition. The theorems with teeth come when the record has to stay, when the states run out, or when a window is added.

Read a machine through a reading its moves never raise and the reading is **flat**: the toll asks nothing of it, because nothing is kept. A clock read by where its hand points is no Thiele machine: the hand comes back around, so that reading falls. Read through anything its moves never raise, a clock is flat. So is a reversible process. So is ordinary computation, read through anything its moves never raise. A flat reading is not a Thiele machine, whatever start you name. Flat is a property of the reading, not of the machine. Read a computer that halts through whether it has halted, and that reading climbs and never falls, and the halt merges two of its states, the last running one and the halted one, which steps to itself. Price its step and it is a Thiele machine on its own states, with nothing added. What Turing's formalism leaves out is the price, not the record.

The definition has to name the reading its toll belongs to. Slide a tile to the right without paying and ask whether it is in the place it just reached: the answer was no and is now yes, and if the toll charged every question, no move could be free. And a free move cannot touch a reading that stays. It cannot raise it, because a raise costs at least one, and it cannot lower it, because a yes stays yes. It must leave it alone.

The price stays on the move. It does not disappear when you press the same button with the reading already up, and on finitely many states the least price list is the plain one: one on every move that can raise the reading from somewhere, zero on every move that never does. Nothing smaller meets the toll. That is a minimum in the definition's units; measuring a device's heat requires a physical account of the device.

A ledger adds up the prices of the moves that ran. It does not count merges, fresh states or heat, and its total need not equal the number of raises. An injective run can visit fresh states at every step while raising its reading only once. The toll sets a lower bound on the charge.

Put the price rule beside the arrows of the counting above. A run from no to yes contains a move that raises the reading, so with nonnegative prices its total is at least one. Under the stronger premise that every merging move pays, a permanent raise into a finite held region incurs a toll by the count. Heat needs one more premise, a physical one, separate from the counting.

## The window and the shadow

**Put two boxes on the table. The tiles on top spell the same answer. One box has a stamp on its side. The other does not. A camera looking straight down gives you the same photograph.**

Hand me that photograph and ask which box was stamped. Enlarging the tiles will not bring the side into view. The difference is in the boxes. The picture leaves it out.

Gather every box that gives the same photograph. Their tops agree. Their insides and their side stamps can still differ. Now give the pieces names. $S$ is the collection of full states, and $B$ is the collection of pictures they give. Taking the photograph is a map called $\pi$:

$$\pi:S\twoheadrightarrow B.$$

The arrow says every picture in $B$ comes from some full state. Choose one picture and call it $b$. All the full states that give that picture form its **fibre**, written $\pi^{-1}(b)$. The tiles can agree while the boxes differ in a retained mark, a grouping, an earlier ordering, or a record of an event. A yes-or-no stamp reads one distinction in that collection. It does not measure the whole collection.

There is no fixed ceiling on the number of states a fibre can contain. To force it to be infinite, give one machine an unlimited obligation: after any number $n$ of stages, it must return to the same picture $b$ and still answer exactly which stages had an event, with each choice independently available. One stage gives two choices: the event happened or it did not. A second doubles the lists to four; a third doubles them to eight. After $n$ stages there are $2^n$ possible answer lists. Two different lists cannot end at the same full state, because that state would have to give opposite answers to one stage's question. Every finite allowance is eventually exceeded.

To ask what a computation hides, split the moves in two. A **sliced** Thiele machine is a Thiele machine on the two-position record with an onto view $\pi:S\to B$. The tabletop $B$ is the flat part, what the window shows. Horizontal moves cost nothing, move the view by a rule that uses only the view, and leave the reading alone. Vertical moves leave the view alone and can raise the reading, never lower it. The toll still holds, and from a start I designate some vertical move raises the reading.

Put a dial with four positions beside a slider with three stops. ROTATE moves the dial one position around for free and leaves the slider alone. ADVANCE moves the slider toward its last stop, leaves the dial alone and costs one. At the last stop the reading is yes; at the other two it is no. ADVANCE pays when it first reaches yes, and still costs one when pressed at the last stop. The price belongs to the button. Look only at the dial: ROTATE moves the picture and ADVANCE leaves it alone.

Give two states the same picture and the same horizontal moves: their pictures agree after every step, even if their records differ throughout. Equal pictures and the same first move give equal next pictures; apply that sentence again for each remaining move. A reader allowed only those pictures never receives the missing distinction. The view cannot see the record or the ledger, and no function of the view recovers either: two runs can end on the same picture with the record up on one and down on the other, and the ledger apart by the price of the raise. An account that prices a raise exactly cannot compute the price from a window that shows a raising step and a quiet step the same way.

That gives the shadow. Look at a Thiele machine through a window that drops its record and what's left is an ordinary machine, computing away, blind to what was kept. It runs the other way too: any machine whose states I can tell apart, with a run that ends somewhere other than where it started, is what some Thiele machine looks like through such a window. The proof builds one: a bit beside the state that goes up the first time the run reaches a chosen state and never comes down, with every move priced, and every state with the bit down a start. That chosen state with its bit down and the same state with its bit up are both states runs reach, and they give one picture, so the window can't tell them apart even on the runs that happen. Read through a flat reading, the ordinary machine is the shadow, not a member. The record adds no computing power; what it adds is distinctions within a fibre, which the window cannot see.

## A record has to be earned

Give a worker a whiteboard. Ask for an answer and the words “CHECKED = YES” underneath. The worker can write both without checking anything.

A variable with a reassuring name has the same problem. To make acceptance mean that a check happened, the machine's permitted operations must close the unchecked route into the accepting state. If a checked and an unchecked history can reach that same state, its verdict cannot tell them apart. The toll requires payment for a raise; it does not say what the record means. The rules of a particular machine are what give it one.

Suppose a good earlier value and a bad one give exactly the same remaining observation. A final verifier receiving only that observation must give both the same answer. If the question is known while the value is live, inspect it then and keep the answer. For a succession of known checks, start an indicator at YES. Leave it there when a check passes and turn it to NO when one fails. Once down, keep it down. At the end it says YES exactly when every check passed. If the questions arrive only later, more information may have to survive, and how much depends on the questions the observer is entitled to ask.

## What I found, what I assumed and what I chose

Most of the time I had the hunch first and found the names later. Over and over, somebody had been here before me. Sometimes that made my day. Sometimes it pissed me off. Here is the line between what nothing let me choose, what I had to assume, and what I did choose.

**Found, which counting forces on any machine.** Run a machine that gives each state exactly one next state. It takes fresh states until it first comes back to one it has used; that return lands on its start or is a merge, two states with one next state; and after it the run only repeats steps it already took. There is no fourth thing a step can do. A run reveals at most one pair of distinct visited states with the same successor; later laps can repeat that transition. So a reading that goes from no to yes and never comes back is paid for in a merge or in fresh states, and when only finitely many states read yes, the move that raises it merges. Over any machine at all, a record that the computation drives and that never comes down is a latch on one event. That is counting, and the pigeonhole in it is older than the computer: Dedekind's finiteness, Zermelo's recurrence objection to Boltzmann, Landauer and Bennett on merging, and the floor Tarjan's potential method puts under a run.

**Assumed, what the found list is taken to stand on in the world.** Landauer's principle: a merge of states the machine really could have been in has a floor under its heat, however slowly it is done. That is the premise from thermodynamics, named and never proved here; the monograph names its critics. A real device can tell apart only finitely many states in a bounded place, so its fresh states run out; nobody has measured where that ceiling sits. And the clean start: a raised record means the event happened only because the record was down at the start, and that start is put in by hand. It is a past hypothesis in miniature, Boltzmann's idea under David Albert's name.

**Chosen, what the model adds, each of which could have gone another way.** To put the account inside the step, as part of what a step is. The reading is part of the definition, and a reading that some run raises and none lowers is what makes a system a member. A computing part that cannot change the record is a further restriction chosen for the machines that need it; the toll on its own requires neither it nor permanence. A rule preserved by every permitted step holds of every program built from those steps. A log maintained by one program needs that program's correctness argument. The toll itself is a choice: a whole unit, at least one, on the move that climbs. So are which readings matter, which event gets a record, what price list it pays, and, on any particular machine, where its flat part ends and its record begins.

## The wider argument

A growing record can be followed through its threshold readings: each threshold asks whether a particular level has been reached. Further results treat the recursion theorem and its input conventions, and compare accounting through cost-framework correspondences with the premises stated beside each comparison.

The protocol examples, including RFC 9162, study specified pieces of their rules. An observer model determines which distinctions a particular window hides. Moving from those models to a claim about every deployed system needs another argument.

The counting, the floor, the window results and the flat reading results are theorems under the hypotheses they state. The interpretations have a different status. The general pointer criterion is a thesis. It carries no proof. It proposes certification as the event worth recording, because certified records get copied and relied on by parties who did not produce them. A separate interpretive argument treats the record and its price as part of computation itself, with one thesis about physical processes: that every physical process which computes with final answers has an exact description as a machine run by one rule, with a next state for every state, on which the answer is a reading no run ever turns off. No proof settles that, because a physical process is not a mathematical object. These interpretations are separate from the counting theorems.

## Follow the argument

Start with the bead in its dip. Follow the holding count, put the price beside the arrows, and see the merge already inside the smallest machine. Then add the window: ask what can remain settled while the visible state changes, which events remain recoverable, and how many distinguishable histories must still fit above one picture.

Each construction gives you something to follow one move at a time. Start with the state, follow the reading through the moves, and add every move's price along the run. [Running and reproduction instructions](docs/REPRODUCTION.md) cover the development environment, and the [mathematical specification](monograph/thiele_machine_math_spec.tex) gives a compact reference for the definitions and results.

## Where things live

Here is the drawing, and where in the [monograph](monograph/monograph.pdf) each part of it is argued.

- **The thing, its directions and the price.** The member, the flat reading, the smallest machine and the shadow: Part I, *A record and a toll*. Why the toll isn't arbitrary, the price of a merge and the room it saves: Part I, *Why the toll isn't arbitrary*.
- **What stays.** Latches, the record over any base and growing records: Part II, *Records over any base: the latch*.
- **The room a kept distinction needs.** Merge or fresh states, the step law, and the noisy and unitary forms: Part I, *A distinction that stays*.
- **What a window forgets.** Windows, fibres and shadow pricing: Part II, *Windows and shadows* and *The shadow, exactly*.
- **What no inside procedure decides.** The shortcut wall and the recursion theorem: Part II, *The diagonal*.
- **The world.** Heat, the five real systems and the pointer thesis: Part III, *Five small models*, *The pointer thesis* and *The counter against physics*.

The arguments are on the page, and each one stands or falls there. The repository also carries a formal check of the same statements, kept as a tool for catching mistakes; it isn't the reason to believe any of them.

For a sustained exposition, the [monograph](monograph/monograph.pdf) develops the model, with the flat reading stated beside the definition. Its [LaTeX sources](monograph/) are included.

## Publication and license

The monograph that develops the model: Devon Thiele, *The Thiele Machine: No Free Insight* (2026).
[Publication record](https://doi.org/10.5281/zenodo.17316437) · [Tagged releases](https://github.com/sethirus/The-Thiele-Machine/releases)

The publication consists of the monograph PDF and the matching tagged repository snapshot. Both belong in the same Zenodo version.

The software is licensed under [Apache 2.0](LICENSE). The monograph and `THIELE_MACHINE.txt` are licensed under CC-BY-SA-4.0. The [patent pledge](PATENT_PLEDGE.md) states the non-assertion commitment; the [technical disclosure](TECHNICAL_DISCLOSURE.md) records the published concepts and earlier embodiments.

Questions, objections and corrections: thethielemachine@gmail.com, or [open an issue](https://github.com/sethirus/The-Thiele-Machine/issues).
