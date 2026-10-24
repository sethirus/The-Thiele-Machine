# The Thiele Machine

The Thiele Machine is an abstract model of computation, a short definition. This repository is the work of finding out what follows from it.

The model is developed in a monograph: [Read the monograph](monograph/monograph.pdf) · [Plain-text introduction](THIELE_MACHINE.txt) · [Monograph source](monograph/monograph.tex) · [Mathematical specification](monograph/thiele_machine_math_spec.pdf)

## The definition

A Thiele machine is five things and one rule: a set $S$ of states, a set $I$ of moves, a step $S\times I\to S$, a cost $I\to\mathbb N$ on each move, and a yes-or-no reading $S\to\{\text{no},\text{yes}\}$. The rule is the toll: a step that turns the reading from no to yes costs at least one unit. A ledger that only climbs, and a window onto what an outside observer sees, come in when a result needs them.

The Thiele Machine is that definition. It is a machine the way Turing's machine is one: mathematics you can reason about, not a device, not an instruction set and not a book. The book is where I work out what follows.

To ask what a computation hides, add a window. A **sliced** Thiele machine is a Thiele machine with an onto view $\pi:S\to B$, what an outside observer sees, and its moves split in two. It sits over an ordinary deterministic machine, the tabletop $B$. Horizontal moves cost nothing, move the view by a rule that uses only the view, and leave the reading alone. Vertical moves leave the view alone and can raise the reading, never lower it. The toll still holds.

## What follows from it

It is one story, in four parts, and each part says what it rests on.

**1. The definition is more general than any mechanism.** It assumes no tape, no head and no counters. Every deterministic machine is already a Thiele machine: let the reading never rise and every move cost nothing. Add a latch on any event the machine reaches, charging one unit when it sets, and you have a Thiele machine with a real record that does not change which functions the machine computes. A run that starts at no and ends at yes costs at least one. That universal floor holds for every machine, and the bar is nearly empty on purpose: a clock that charges one for every move meets it. The theorems with teeth come when you add one next state for every state (part 2) or a window (part 3).

**2. Keeping costs something on every machine.** This is counting, with no premise and no physics. On any machine with one next state for every state, every step lands on a fresh state, merges two states, or returns to its start. So a run that raises a reading and keeps it up either merges somewhere or uses endlessly many distinct states. A machine with endlessly many states can avoid the merge on paper by paying in fresh states. A machine with finitely many states cannot: when only finitely many states read yes, the raising step itself merges. Whether a real device has finitely many distinguishable states is a physical assumption, and the book names it as one. When a coarse description of a machine merges, the fine machine merges too, unless its step leaves the described states or there are endlessly many of them. The toll is where the model writes a price on that step, and the price is a choice: if every merging instruction costs at least one, the toll on a finite machine follows from the merge. A heat bound needs one more premise, a named physical one, and the book keeps it apart from the counting.

**3. The ordinary machine and the full machine, in both directions.**
- In a sliced machine, the view $\pi(S)=B$ with its horizontal moves is an ordinary deterministic machine. Any deterministic machine arises this way: put a bit beside its states. The view cannot see the record, because the free moves never touch it and the picture follows the computation step for step. That needs a raise to exist, and nothing else: no universal base and no premise about the control.
- Thiele-complete is stricter, and unlike the sliced machine it does ask for universality. It needs a universal base, so the machine can be read as one that runs every program, as a Turing machine can. On top of that it asks that computing cost nothing and never touch the record, that the record stay up once it is up, that starts have it down, that marks cost exactly one, and that some run raise it from one start and not another. Every machine that meets it hides its record and its ledger from its own window. Any machine with a universal base lifts to one by adding the record layer, and the ordinary computer is then the slice that is left when the layer is forgotten. An account that prices certification exactly cannot compute the price from a window that shows a certifying step and a non-certifying step the same way.
- Recovering which of $n$ editions were certified takes $2^n$ states above one picture.
- A small six-instruction machine and a universal program on it show these definitions can be met. They are examples and not the subject.

**4. What is argued and what is proved.** The counting, the floor, the window results, the lift and the slice are theorems under the hypotheses they state. The book has 206 numbered statements; 205 are closed by a proof on the page, and the one that is not is the pointer thesis. It proposes certification as the event worth recording, because certified records get copied and relied on by parties who did not produce them. Separately, and unnumbered, the book argues that the record and its price are part of computation itself and not something added afterwards, and states the Thiele thesis, a claim about physical processes. Neither is presented as a theorem.

## Where it starts

**Put two boxes on the table. The tiles on top spell the same answer. One box has a stamp on its side. The other does not. A camera looking straight down gives you the same photograph.**

Hand me that photograph and ask which box was stamped. Enlarging the tiles will not bring the side into view. The difference is in the boxes. The picture leaves it out.

That is where I start. I want a machine that can compute, establish a record, keep that record while the workspace changes, and count what its rules charge for doing so. The definition above is the model I built to ask what that takes.

## The tabletop and everything above it

Gather every box that gives the same photograph. Their tops agree. Their insides and their side stamps can still differ. I want to keep that whole collection in view, even when the photograph cannot tell its members apart.

Now give the pieces names. $S$ is the collection of full states, and $B$ is the collection of pictures they give. Taking the photograph is a map called $\pi$:

$$\pi:S\twoheadrightarrow B.$$

The arrow says every picture we are counting comes from some full state. Choose one picture and call it $b$. All the full states that give that picture form its **fibre**, written $\pi^{-1}(b)$. That notation names the collection we just gathered.

The tiles can agree while the boxes differ in which checks ran, which claims were certified, and what survived when an earlier page was wiped. A yes-or-no stamp reads one distinction in that collection. It does not measure the whole collection.

There is no fixed ceiling on the number of states a fibre can contain. To force it to be infinite, give one machine an unlimited obligation: after any number $n$ of editions, it must return to the same picture $b$ and still answer exactly which editions were certified, with each choice independently available. One edition gives two choices: certified or not. A second doubles the lists to four; a third doubles them to eight. Each further edition doubles them again. After $n$ editions there are $2^n$ possible answer lists. Two different lists cannot end at the same full state, because that state would have to give opposite answers to one edition's question. Every finite allowance is eventually exceeded.

That is where the infinity comes from: a task that keeps demanding recoverable distinctions above one unchanged picture.

## A record has to be earned

Give a worker a whiteboard. Ask for an answer and the words “CHECKED = YES” underneath. The worker can write both without checking anything.

A variable with a reassuring name has the same problem. To make acceptance mean that a check happened, the machine's permitted operations must close the unchecked route into the accepting state. If a checked and an unchecked history can reach that same state, its verdict cannot tell them apart.

## What the window can tell you

For the abstract sliced interface, horizontal moves evolve the tabletop by a rule depending only on its current picture and leave the record alone. Vertical establishment leaves the picture fixed and can raise the record. Give two states the same picture and the same horizontal instruction sequence: their pictures agree after every step, even if their records differ throughout.

Watch what happens one move at a time. Equal pictures and the same first move give equal next pictures. Apply that sentence again for each remaining move. A reader allowed only those pictures never receives the missing distinction.

## What keeping takes

Give the box three full configurations in which it holds the answer. Once it enters any of them, every later tick must leave it in one of those three. Now include the unfinished configuration that first enters them. Four sources have their next states among three places. At least two arrows meet.

Nothing depends on the number three. With $K$ held configurations and one unfinished entrant, there are $K+1$ sources and only $K$ landing places.

Suppose instead that the rule always gives different successors to different full states. Its holding run cannot revisit a state. If it did, walk backwards from the two equal visits. Their predecessors must agree too, because different predecessors never land together. Keep going until the earlier visit reaches the unfinished state. The later visit is still holding the answer, so it cannot be that same unfinished state. Avoiding the merge therefore requires an endless supply of distinct holding configurations.

For a finite holding interval the count is sharp. Line up $K$ held states after the unfinished state and fix the last one. The first $K$ sources have distinct successors. Include the next source and the final two arrows meet. Keeping the answer visible can hide that merger from the tabletop camera.

Now put a price rule beside the arrows. The abstract model's toll says that a move raising the chosen reading costs at least one unit. A run from no to yes contains such a move, so with nonnegative prices its total is at least one. Under the stronger premise that every merging instruction pays, a permanent raise into a finite held region incurs a toll by the count above. The price premise is written beside the count; a physical heat bound additionally needs a physical model.

## An example machine

This is an example and not the Thiele Machine. The model is defined over every machine that meets it. This small machine is here to show that the definition can be met, and to give the argument something to run.

The example has two natural-number counters, their edition numbers, a sixteen-entry fact table, a commitment channel, a trap, a permanent certificate and a ledger. Its instructions are INC, DEC, HALT, CHECK, COMMIT and CERTIFY. The last three each cost one unit; the counter moves cost zero in that ledger.

The book gives the transition rules, derives the earned chain, builds universal host programs, and follows how a guest's computation and accounting appear in its host. It also studies composition, observation, retention and the cost of preserving relations between instructions. The constructions and arguments are in the text.

The [Python implementation](thiele_small/) lets you explore the small machine. [Running and reproduction instructions](docs/REPRODUCTION.md) cover the development environment. The [mathematical specification](monograph/thiele_machine_math_spec.tex) gives a compact reference, while the book walks through why the definitions and arguments fit together.

### Its earned chain

It enforces an order:

1. **CHECK** tests a claim and records the claim together with the edition of the counter it concerns.
2. **COMMIT** selects a matching fact only while that edition is still current.
3. **CERTIFY** requires a commitment and raises the permanent flag.

A counter write advances its edition. An old check cannot then be presented as a check of the newly written counter. Starting with an empty table, empty channel and flag down, any run that raises the flag must contain the three successful acts in order: only CERTIFY raises it, only COMMIT fills its channel, and only CHECK supplies the fact COMMIT requires.

Storing a representation is part of implementing this machine. Preserving those rules through every allowed program is the part that makes the representation authoritative.

### Its trap

It also has a trap. A failed CHECK blows the fuse, and later free instructions cannot turn its gears. That effect matters to future computation. The book's computational slice follows live states; the failure leaves that domain. A view that hid every failed check on every state while predicting later free moves would have to make those moves look stationary too.

## Open the gauge wider

These counts are worked out on the example machine above. The counting is the point; the example gives it something to run.

Three measurements in the book ask different questions of their chosen windows:

- **Current checks.** Leave the working value fixed and choose which checks to run. One available successful check gives two histories to distinguish: ran it or did not. Two independently available checks give four choices; each further check doubles them. If $m(b)$ checks can succeed at value $b$, and the machine must report exactly which ran, it needs $2^{m(b)}$ full states above that value. Keeping the value and the chosen set of checks uses exactly that many. Do the count separately for every working value and add: the total minimum is $\sum_b2^{m(b)}$.
- **Completed editions.** Independently chosen, recoverable certification answers for $n$ editions require $2^n$ states at a common final working view. One machine meeting that task for every $n$ needs an infinite reachable fibre there.
- **The concrete publication file.** One entire native state can sit below **65,535** different nonempty sets of published claim/edition entries. Sixteen checked facts supply sixteen independent publication choices. Give every choice two instructions and the same charge, and all nonempty selections finish with the same native counters, table, channel, line number, ledger and flag. Sixteen extra bits beside the existing table distinguish the sets. Fifteen bits have only 32,768 values and cannot.

The last count looks through a different camera: it sees the entire native machine and forgets an added publication archive. The native Boolean flag says that some certification occurred. The archive says which claims and editions were certified.

## Look before the value disappears

Suppose a good earlier value and a bad one give exactly the same remaining observation. A final verifier receiving only that observation must give both the same answer. It cannot identify which earlier value actually occurred.

If the question is known while the value is live, inspect it then and keep the answer. For a succession of known checks, start an indicator at YES. Leave it there when a check passes and turn it to NO when one fails. Once down, keep it down. At the end it says YES exactly when every check passed. If the questions arrive only later, more information may have to survive. The book counts that information from the questions the observer is entitled to ask.

The machine can be implemented with ordinary computation. What matters is which information remains available and which operations are permitted to change an accepting record. A comparison of implementations has to give both sides the same task and access to the same evidence.

## The wider argument

The book also follows a growing record through its threshold readings: each threshold asks whether a particular level has been reached. It treats the recursion theorem and its input conventions, and compares accounting through cost-framework correspondences with the premises stated beside each comparison.

The protocol examples, including RFC 9162, study specified pieces of their rules. An observer model determines which distinctions a particular window hides. Moving from those models to a claim about every deployed system needs another argument. The pointer thesis is a thesis, and it carries no proof. The book gives its proposed connection to the world separately from the counting theorems.

## Follow the argument

Start with the boxes and the camera. Follow the holding count, put the price rule beside the arrows, and watch CHECK, COMMIT and CERTIFY earn the record. Then open the gauge wider: ask which checks ran, which editions were certified, and how many distinguishable histories must still fit above one picture.

Each construction gives you something to follow one move at a time. The book develops the objects first, names the pieces, and walks through why the result follows. The appendices carry the full host constructions and the conditions used by each argument.

## Publication and license

The monograph that develops the model: Devon Thiele, *The Thiele Machine: No Free Insight* (2026).
[Publication record](https://doi.org/10.5281/zenodo.17316437) · [Tagged releases](https://github.com/sethirus/The-Thiele-Machine/releases)

The software is licensed under [Apache 2.0](LICENSE). The monograph and `THIELE_MACHINE.txt` are licensed under CC-BY-SA-4.0. The [patent pledge](PATENT_PLEDGE.md) states the non-assertion commitment; the [technical disclosure](TECHNICAL_DISCLOSURE.md) records the published concepts and earlier embodiments.

Questions, objections and corrections: thethielemachine@gmail.com, or [open an issue](https://github.com/sethirus/The-Thiele-Machine/issues).
