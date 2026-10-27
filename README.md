# The Thiele Machine

A Thiele machine is a thing, the directions it can move in, and a price on each direction. A direction turns the thing into the next thing. A direction that makes a distinction stay is never free.

That is the whole definition. The book gives its consequences and instances, the counting that motivates it, and the argument for choosing it. A machine whose directions never make a distinction stay is the flat case, and the rule requires no charge from it: a clock is one, a reversible process is one, and so is ordinary computation, with a reading their moves preserve. This repository is the account of what an ordinary computational description can leave out.

The model is developed in a monograph: [Read the monograph](monograph/monograph.pdf) · [Plain-text introduction](THIELE_MACHINE.txt) · [Monograph source](monograph/monograph.tex) · [Mathematical specification](monograph/thiele_machine_math_spec.pdf)

## The point

Take anything that can be more than one way and isn't yet any of them for good: a bead that could sit in either of two dips, a square of paper with nothing on it, a question nobody has closed. Now let it settle one way, and keep it there. Something is the case now that wasn't a moment ago. That is a distinction that stays, and it is what the book is about. Nothing becomes something for free: under a rule that gives every state exactly one next state, keeping something settled takes a merge somewhere in the run, two states landing on one, or an endless supply of fresh states.

Structure is made of exactly this. The smallest distinction there is sorts the ways a thing could be in two and holds one side: a bead in the left dip and not the right, a mark on the page and not off it. A grouping, an order, a relation a later move leans on, a fact somebody found out and wrote down: each is a distinction that stays, paid for the same way as the bead in its dip. Insight, in the sense the book can price, is a kept distinction. The toll requires a charge when it's raised; merely remaining up requires no further charge. Repeating a priced move still pays that move's price. That is what the book's other name, No Free Insight, means.

Established is the sharpest case. Two computers can end with the same answer, and only one of them checked it. The difference between them is a distinction one of them never kept. A record that a claim was checked and closed is a distinction that stays, with a check in front of it, and it's paid for the same way. The two boxes in the next section are that case. The point is the distinction that stays, and what keeping it takes.

## Where it starts

**Put two boxes on the table. The tiles on top spell the same answer. One box has a stamp on its side. The other does not. A camera looking straight down gives you the same photograph.**

Hand me that photograph and ask which box was stamped. Enlarging the tiles will not bring the side into view. The difference is in the boxes. The picture leaves it out.

That is where I start. I want a machine that can compute, establish a record, keep that record while the workspace changes, and count what its rules charge for doing so. The definition above is the model I built to ask what that takes.

## The definition, exactly

Give the pieces names. $S$ is the set of states, $I$ the set of moves, and the step $S\times I\to S$ turns a state and a move into the next state. Each move has a price $c:I\to\mathbb N$. The record is a reading $\mathrm{rec}:S\to R$ into an ordered set $R$: for any two records you can ask whether one sits at or below the other. A move makes a distinction stay when it carries the record somewhere not at or below where it was. The one rule is the toll: such a move costs at least one. Nothing else is assumed of the order, and nothing says what the record is about. A ledger that only climbs, and a window onto what an outside observer sees, come in when a result needs them.

The smallest record has two positions, no and yes. Then the record is a yes-or-no reading of the state, making a distinction stay is turning no into yes, and the toll says that move costs at least one. Most of the book is stated on this smallest case, because it is the one you can point at: a lamp beside a box, a stamp on its side, a flag that goes up. The flag is not the record. It is the smallest question you can ask of one. The proofs state the general case first and derive the flag as its two-point instance.

The Thiele Machine is that definition. It is a machine the way Turing's machine is one: mathematics you can reason about, not a device, not an instruction set and not a book. I named it after myself, on purpose. I wanted to call it the meta machine, and in 2021 a company took that word, so I went one level up and put my own name on it, half a joke and half a stake in the ground. Turing got a machine; here's mine. The book is where I work out what follows.

Every machine whose moves never climb the order is a Thiele machine in the flat case, where the toll requires no charge: a clock, a reversible process, any deterministic machine with its record standing still. A reading preserved by undoable moves never rises; that does not forbid pricing those moves. The ordinary computer is one member of the flat case, and only one. Keep that direction in mind throughout. The computer is a shadow of the machine, not the floor it is built on.

One theorem comes with the definition and nothing else. A run that starts with the record at no and ends with it at yes pays at least one. That is the universal floor, and it holds for every machine that meets the definition. The bar is nearly empty on purpose: a clock that charges one for every move clears it. The theorems with teeth come when the record has to stay, when the states run out, or when a window is added.

The definition has to name the reading its toll belongs to. Slide a tile to the right without paying and ask whether it is in the place it just reached: the answer was no and is now yes, and if the toll charged every question, no move could be free. And a free move cannot touch a reading that stays. It cannot raise it, because a raise costs at least one, and it cannot lower it, because a yes stays yes. It must leave it alone.

The price stays on the move. It does not disappear when you press the same button with the reading already up, and the least price list is the plain one: one on every move that can raise the reading from somewhere, zero on every move that never does. Nothing smaller meets the toll. That is a minimum in the definition's units; measuring a device's heat requires a physical account of the device.

A ledger adds up the prices of the moves that ran. It does not count merges, fresh states or heat, and its total need not equal the number of raises. An injective run can visit fresh states at every step while raising its reading only once. The toll sets a lower bound on the charge.

To ask what a computation hides, add a window. A **sliced** Thiele machine is a Thiele machine on the two-position record, with an onto view $\pi:S\to B$, what an outside observer sees, and its moves split in two. The tabletop $B$ is the flat part, what the window shows. Horizontal moves cost nothing, move the view by a rule that uses only the view, and leave the reading alone. Vertical moves leave the view alone and can raise the reading, never lower it. The toll still holds.

Put a dial with four positions beside a slider with three stops. ROTATE moves the dial one position around for free and leaves the slider alone. ADVANCE moves the slider toward its last stop, leaves the dial alone and costs one. At the last stop the reading is yes; at the other two it is no. ADVANCE pays when it first reaches yes, and still costs one when pressed at the last stop. The price belongs to the button. Look only at the dial: ROTATE moves the picture and ADVANCE leaves it alone. That is a sliced machine before any checking or certification enters the story.

Every flat machine is the shadow of a sliced machine that keeps a record above it. The record adds no computing power; what it adds is distinctions within a fibre, which the window cannot see.

## What I found, what I assumed and what I chose

Most of the time I had the hunch first and found the names later. Over and over, somebody had been here before me. Sometimes that made my day. Sometimes it pissed me off. Here is the line between what nothing let me choose, what I had to assume, and what I did choose.

**Found, which counting forces on any machine.** Run a machine that gives each state exactly one next state. It takes fresh states until it first comes back to one it has used; that return lands on its start or is a merge, two states with one next state; and after it the run only repeats steps it already took. There is no fourth thing a step can do. A run reveals at most one pair of distinct visited states with the same successor; later laps can repeat that transition. So a reading that goes from no to yes and never comes back is paid for in a merge or in fresh states, and when only finitely many states read yes, the move that raises it merges. Over any machine at all, a record that the computation drives and that never comes down is a latch on one event. That is counting, and the pigeonhole in it is older than the computer: Dedekind's finiteness, Zermelo's recurrence objection to Boltzmann, Landauer and Bennett on merging, and the floor Tarjan's potential method puts under a run.

**Assumed, what the found list is taken to stand on in the world.** Landauer's principle: a merge of states the machine really could have been in has a floor under its heat, however slowly it is done. That is the premise from thermodynamics, named and never proved here, with its critics named. A real device can tell apart only finitely many states in a bounded place, so its fresh states run out; nobody has measured where that ceiling sits. And the clean start: a raised record means the event happened only because the record was down at the start, and that start is put in by hand. It is a past hypothesis in miniature, Boltzmann's idea under David Albert's name.

**Chosen, what the model adds, each of which could have gone another way.** To put the account inside the step, as part of what a step is. The record is one of the five parts, a reading of the state. Permanence and a computing part that cannot change it are further restrictions chosen for the examples that need them; the core definition requires neither. A rule preserved by every permitted step holds of every program built from those steps. A log maintained by one program needs that program's correctness argument. The toll itself is a choice: a whole unit, at least one, on the move that climbs. So are which readings matter, which event gets a record, what price list it pays, and, on the example machine, where its flat part ends and its record begins.

## The tabletop and everything above it

Gather every box that gives the same photograph. Their tops agree. Their insides and their side stamps can still differ. I want to keep that whole collection in view, even when the photograph cannot tell its members apart.

Now give the pieces names. $S$ is the collection of full states, and $B$ is the collection of pictures they give. Taking the photograph is a map called $\pi$:

$$\pi:S\twoheadrightarrow B.$$

The arrow says every picture in $B$ comes from some full state. Choose one picture and call it $b$. All the full states that give that picture form its **fibre**, written $\pi^{-1}(b)$. That notation names the collection just gathered.

The tiles can agree while the boxes differ in a retained mark, a grouping, an earlier ordering, or a record of an event. A yes-or-no stamp reads one distinction in that collection. It does not measure the whole collection.

There is no fixed ceiling on the number of states a fibre can contain. To force it to be infinite, give one machine an unlimited obligation: after any number $n$ of stages, it must return to the same picture $b$ and still answer exactly which stages had an event, with each choice independently available. One stage gives two choices: the event happened or it did not. A second doubles the lists to four; a third doubles them to eight. Each further stage doubles them again. After $n$ stages there are $2^n$ possible answer lists. Two different lists cannot end at the same full state, because that state would have to give opposite answers to one stage's question. Every finite allowance is eventually exceeded.

That is where the infinity comes from: a task that keeps demanding recoverable distinctions above one unchanged picture.

## What keeping takes

Give the box three full configurations in which it holds the answer. Once it enters any of them, every later tick must leave it in one of those three. Now include the unfinished configuration that first enters them. Four sources have their next states among three places. At least two arrows meet.

Nothing depends on the number three. With $K$ held configurations and one unfinished entrant, there are $K+1$ sources and only $K$ landing places.

Suppose instead that the rule always gives different successors to different full states. Its holding run cannot revisit a state. If it did, walk backwards from the two equal visits. Their predecessors must agree too, because different predecessors never land together. Keep going until the earlier visit reaches the unfinished state. The later visit is still holding the answer, so it cannot be that same unfinished state. Avoiding the merge therefore requires an endless supply of distinct holding configurations.

For a finite holding interval the count is sharp. Line up $K$ held states after the unfinished state and fix the last one. The first $K$ sources have distinct successors. Include the next source and the final two arrows meet. Keeping the answer visible can hide that merger from the tabletop camera.

Now put a price rule beside the arrows. The toll says that a move raising the chosen reading costs at least one unit. A run from no to yes contains such a move, so with nonnegative prices its total is at least one. Under the stronger premise that every merging instruction pays, a permanent raise into a finite held region incurs a toll by the count above. Heat needs one more premise, a physical one, and the book keeps it apart from the counting.

## What the window can tell you

For a sliced machine, horizontal moves evolve the tabletop by a rule depending only on its current picture and leave the record alone. Vertical establishment leaves the picture fixed and can raise the record. Give two states the same picture and the same horizontal instruction sequence: their pictures agree after every step, even if their records differ throughout.

Watch what happens one move at a time. Equal pictures and the same first move give equal next pictures. Apply that sentence again for each remaining move. A reader allowed only those pictures never receives the missing distinction. For that to happen a raise has to exist, and nothing else is needed: no premise about what the tabletop computes and none about the control.

The view cannot see the record or the ledger, and no function of the view recovers either: two runs can end on the same picture with the record up on one and down on the other, and the ledger apart by the price of the raise. An account that prices a raise exactly cannot compute the price from a window that shows a raising step and a quiet step the same way.

## A record has to be earned

Give a worker a whiteboard. Ask for an answer and the words “CHECKED = YES” underneath. The worker can write both without checking anything.

A variable with a reassuring name has the same problem. To make acceptance mean that a check happened, the machine's permitted operations must close the unchecked route into the accepting state. If a checked and an unchecked history can reach that same state, its verdict cannot tell them apart.

## The earned-chain counter example

This is an example and not the Thiele Machine. The model is defined over every machine that meets it. This small machine is here to show that the definition can be met, and to give the argument something to run.

The example has two natural-number counters, their edition numbers, a sixteen-entry fact table, a commitment channel, a trap, a permanent certificate and a ledger. Its instructions are INC, DEC, HALT, CHECK, COMMIT and CERTIFY. The last three each cost one unit; the counter moves cost zero in that ledger.

Its two-counter base computes everything a Turing machine can, under the encoding stated in Part III. That universality belongs to this example, not to the twelve-state dial and slider above. The model adds a place in the step for what a computation made the case and what that cost.

The book gives the transition rules, derives the earned chain, builds universal host programs, and follows how a guest's computation and accounting appear in its host. It also studies composition, observation, retention and the cost of preserving relations between instructions. The constructions and arguments are in the text.

The [Python implementation](thiele_small/) lets you explore the small machine. [Running and reproduction instructions](docs/REPRODUCTION.md) cover the development environment. The [mathematical specification](monograph/thiele_machine_math_spec.tex) gives a compact reference, while the book walks through why the definitions and arguments fit together.

### Its earned chain

It enforces an order:

1. **CHECK** tests a claim and records the claim together with the edition of the counter it concerns.
2. **COMMIT** selects a matching fact only while that edition is still current.
3. **CERTIFY** requires a commitment, preserves the channel, and raises the permanent flag.

A counter write advances its edition. An old check cannot then be presented as a check of the newly written counter. Starting with an empty table, empty channel and flag down, any run that raises the flag must contain the three successful acts in order: only CERTIFY raises it, only COMMIT fills its channel, and only CHECK supplies the fact COMMIT requires.

The toll requires payment for a raise; it does not say what the record means. The rules above are what give it one.

### Its trap

It also has a trap. A failed CHECK blows the fuse, and later free instructions cannot turn its gears. That effect matters to future computation. The book's computational slice follows live states; the failure leaves that domain. A view that hid every failed check on every state while predicting later free moves would have to make those moves look stationary too.

## Open the gauge wider

This count is a fibre of one projection on the counter example.

One entire native state can sit below **65,535** different nonempty sets of published claim/edition entries. Sixteen checked facts supply sixteen independent publication choices. Give every choice two instructions and the same charge, and all nonempty selections finish with the same native counters, table, channel, line number, ledger and flag. Sixteen extra bits beside the existing table distinguish the sets. Fifteen bits have only 32,768 values and cannot.

This count looks through a wide camera: it sees the entire native machine and forgets an added publication archive. The native Boolean flag says that some certification occurred. The archive says which claims and editions were certified.

The construction starts with counters $(16,0)$, both editions zero, line 1, ledger zero, empty table and channel, and trap and flag down. These are initial values. Sixteen CHECKs reach line 17 and ledger 16; sixteen blocks of COMMIT/CERTIFY or COMMIT/COMMIT reach line 49 and ledger 48. CERTIFY preserves the channel, so either final block leaves the same commitment. The [review audit](scripts/audit_root_review.py) reproduces all 65,536 choices using the Python implementation and checks the finite holding graphs separately.

## Look before the value disappears

Suppose a good earlier value and a bad one give exactly the same remaining observation. A final verifier receiving only that observation must give both the same answer. It cannot identify which earlier value actually occurred.

If the question is known while the value is live, inspect it then and keep the answer. For a succession of known checks, start an indicator at YES. Leave it there when a check passes and turn it to NO when one fails. Once down, keep it down. At the end it says YES exactly when every check passed. If the questions arrive only later, more information may have to survive. The book counts that information from the questions the observer is entitled to ask.

## The wider argument

The book also follows a growing record through its threshold readings: each threshold asks whether a particular level has been reached. It treats the recursion theorem and its input conventions, and compares accounting through cost-framework correspondences with the premises stated beside each comparison.

The protocol examples, including RFC 9162, study specified pieces of their rules. An observer model determines which distinctions a particular window hides. Moving from those models to a claim about every deployed system needs another argument.

The counting, the floor, the window results and the flat case are theorems under the hypotheses they state. Two things in the book are not. The general pointer criterion is a thesis. It carries no proof. It proposes certification as the event worth recording, because certified records get copied and relied on by parties who did not produce them. Separately, and unnumbered, the book argues that the record and its price are part of computation itself and not something added afterwards, and states one thesis about physical processes: that every physical process which computes with final answers has an exact description as a machine run by one rule, with a next state for every state, on which the answer is a reading no run ever turns off. No proof settles that, because a physical process is not a mathematical object. The book gives both separately from the counting theorems, and presents neither as a theorem.

## Follow the argument

Start with the boxes and the camera. Follow the holding count, put the price rule beside the arrows, and ask what can remain settled while the visible state changes. Then open the gauge wider: ask which events remain recoverable and how many distinguishable histories must still fit above one picture. The earned-chain counter machine gives one worked example of those questions.

Each construction gives you something to follow one move at a time. The book develops the objects first, names the pieces, and walks through why the result follows. The universal-machine appendix identifies the companion source files containing the complete programs and simulation proofs.

## Where things live

Most of the repository's volume is the example, because an example that runs needs a host, a universal program and a checker. That is not where the model is. Here is the drawing, and where each part of it lives in the proofs.

- **The thing, its directions and the price.** The definition over any order of records, its floor, and the flag as the two-point instance: `coq/kernel/foundation/AxCore.v` and `AxTwoPoint.v`. The one-bit floor, least prices, exact pricing and merge pricing: `coq/kernel/nfi/`, `coq/audit/LeastToll.v`.
- **What stays.** Latches, the record over any base, growing records, and the earned chain that makes a raised record mean a check happened: `coq/kernel/foundation/StructuralRecordAxis.v`, `AxLatch.v`, `GrowingRecord.v`, `minimal/CertifiedHistory.v`.
- **What a window forgets.** Observation contracts, the terminal lift, shadow pricing, and the window theorems: `coq/audit/`, `coq/kernel/foundation/AxWindow.v`, `minimal/ThieleCompleteWindow.v`, `minimal/SliceCore.v`.
- **The room a kept distinction needs.** Merge or fresh states, retention bounds, fibre counts, and the stochastic and unitary forms: `minimal/StepLaw.v`, `HeatOrRoom.v`, `KeptDistinction.v`, `EditionCapacity.v`, `NoisyChairs.v`, `QuantumChairs.v`, `coq/kernel/foundation/AxMerge.v`.
- **Computation as the flat case.** A flat part fitted with a record (the lift of every model), completeness over a two-counter flat part, composition, the universal machines U and U_P, the verified compiler, the recursion theorem and Rice: `minimal/LiftCore.v`, `NeutralComplete.v`, `ThieleComplete.v`, `coq/kernel/foundation/Universal*.v`, `Cmp*.v`, `Cz*.v`, `*Rice.v`.
- **The example running.** The small machine's programs, host layouts, blocks and arithmetic: `minimal/EarnedCore.v`, `coq/kernel/foundation/UniversalLayout.v`, `UniversalBlocks.v`, `Sm*.v`, `minimal/Tc2*.v`. In code: `thiele_small/`, a Python version of the example and nothing else.
- **The world.** Heat, entropy, the CHSH and Tsirelson mathematics, external systems, and the pointer thesis: `coq/kernel/thermodynamic/`, `coq/kernel/quantum/`, `coq/kernel/reductions/`, `coq/kernel/frontier/`.

In the book: the drawing is Parts I and II, with the flat case stated beside the definition; the example running is Part III and the appendices.

## Publication and license

The monograph that develops the model: Devon Thiele, *The Thiele Machine: No Free Insight* (2026).
[Publication record](https://doi.org/10.5281/zenodo.17316437) · [Tagged releases](https://github.com/sethirus/The-Thiele-Machine/releases)

The publication consists of the PDF together with the matching tagged repository snapshot. The snapshot supplies the companion Coq files for the 3,728- and 3,735-instruction universal programs; their full expansions are not printed in the PDF. Both belong in the same Zenodo version.

The software is licensed under [Apache 2.0](LICENSE). The monograph and `THIELE_MACHINE.txt` are licensed under CC-BY-SA-4.0. The [patent pledge](PATENT_PLEDGE.md) states the non-assertion commitment; the [technical disclosure](TECHNICAL_DISCLOSURE.md) records the published concepts and earlier embodiments.

Questions, objections and corrections: thethielemachine@gmail.com, or [open an issue](https://github.com/sethirus/The-Thiele-Machine/issues).
