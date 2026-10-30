Every assumption in one place

Every argument in this book says what it stands on, in the chapter where it's made. This appendix puts
all of those in one place, so you can see which result leans on what, and what walks through when a
condition is taken away. The ledger in chapter twenty-two sorts the claims. This sorts the conditions
under them.

Each one below is one of three things. A part of the definition: I chose it, and page one says so. A
condition a chapter puts on a machine: it holds for the machines that meet it and nobody else. Or an
assumption about the world: somebody's claim about physics, named, that an argument leans on and
doesn't prove.


The definition

A thing, moves that take it to a next thing, and a way to tell how settled it is, where settled never
goes back. Settledness can be yes or no, or a checklist of ticks that don't come off. Take away "never
goes back" and the coin walks through: a flip and a flip back, settled and unsettled, forever, and
nothing has to give. Chapter three's second door.

Some run, from a start you pick, that actually settles it more than it was. Take it away and a coin
that never settles anything counts as a Thiele machine for free. Page one.

A price on every move, nothing or more, never a refund. Take away "never a refund" and a move that
settles charges one, the next hands it back, and the whole run comes out free. Page one.

The toll: a move that settles something more than it was costs something. That's the one rule. Chapter
three shows it isn't only a choice: on a finite machine it follows from settled staying settled and
Bennett's rule together.


What a machine is

One next state for every state. That's what chapter one assumes of a machine, and it's all the step law
needs: every step lands somewhere new, makes two arrows meet, or goes round a loop. Nothing about size.
A machine with more than one move from a state has one next state per move; chapter twenty-two takes
steps that branch and shows that, after the raise, a single run still makes two arrows meet or never
repeats a state.

Finitely many states. This is the condition people most often think the book leans on, and it leans on
it less than it looks. Chapter one needs none of it. What finiteness takes away is the column of fresh
paper: on finitely many states, a run that settles something for good has to make two arrows meet,
because it can't land somewhere new forever. Take it away and Hilbert's hotel walks through: a move
where no two arrows ever meet can settle something, and nothing meets, as long as there's always another
room. Chapter two. And the finite set the count needs can be tiny. Chapter four's machine has two boxes.

Applying any of this to a real device takes one more step the arguments don't supply: a justified list
of the device's states that the device can actually tell apart. That's a fact about the device.


Prices

Bennett's rule: a move where two arrows meet costs at least one. It's the third of the three conditions
in chapter three. Take it away and the stamp at zero walks through: a move that sends both states to YES,
priced at nothing. Chapter three's third door.

The halving rule: each unit of cost pays for at most one halving of the places you could have been. It's
stronger than Bennett's rule, and it's what sizes the toll: a move that squeezes m + k states into m pays
at least the halvings between them. Chapters three, six and fifteen use it. Chapter twenty shows that
charging bits on every spread is the same rule.

A price list is always given. Nothing in the book says what the charges should be beyond the floors
above. Chapter eleven's counter is the arithmetic once they're chosen.


Conditions put on a machine

Established. A record that goes up only right after a passing check of the very claim it records, with
nothing the claim is about changed between the check and the raise. That's chapter eight. One more thing
it needs is a fact about the checker and not a condition on the machine: that the check means what it
says and could have failed. And every guarantee about an established record is about runs: any list of
moves, from a clean start, on a step that does what it says, one writer at a time. Whoever sets the
start, the wire that carries the report out, and the tools that built the step are outside that fence.
Chapter twenty-two.

Answering only to the machine. A box whose next position depends only on what the base is doing right
now and where the box is right now, with a tally that never goes down, a toll on the step that turns the
box up, a box that stays up once up, and some run that turns it up. Those are chapter fourteen's five
rules. Drop "stays up" and the toggle walks through. Drop "answers only to the machine" and the
timestamp does.

Covering the cups. Nothing in how the rest of the machine moves depends on the cups or the tally. Without
that, covering them leaves a machine that can't decide what to do next. Chapter fifteen's result also
needs the machine finite, the record only growing, and the uncovered machine forgetting nothing.

Editions never reused. The shortcut in chapter sixteen never answers wrong from a clean start as long as
every write moves to a fresh edition. Let the editions wrap around and four moves give a wrong answer.

The guard's two conditions. Its glance can't tell a passing value from a failing one, and the memory it
reads is made only of boxes that go up and never come down. Under both, there are four doors and no
fifth. Drop the first and you're at the fourth door, or doing the check over. Drop the second and you're
at the third. Chapter sixteen.

The diagonal's conditions. A procedure that decides a question about programs, where the machine has
Kleene's trick, the flip is something the machine can run, two programs that behave alike always get the
same answer, and there's one program that passes and one that fails. Under those, no procedure inside the
machine decides it. A procedure that answers only for some programs, or needs outside evidence, isn't
ruled out. Chapter seventeen.

Two levers that keep states apart. In chapter twenty-one each lever has to keep different states apart
for the states reached within the promised number of pulls. The room counts there are counts under that
promise. Receipts covering the merges a run shows needs one of every colliding pair to pay.

Steps that keep the even spread. A noisy step that keeps the even spread can't raise a reading that
stays. Chapter twenty-one. A step that can raise one makes the spread lumpier.


Assumptions about the world

Landauer's principle: lowering uncertainty about a device's state by a bit hands at least kT ln 2 of heat
to the surroundings, on average. It has critics, and chapter twenty names them. Every heat claim in the
book is "given Landauer," and nothing in the book derives it. On a state that's already known, the
principle sets no floor at all.

The fixed device. A fixed device that merges K inputs produces at least k ln K of entropy on one of them.
That leans on the second law for the device's average and on reading dissipated work as temperature times
entropy produced. It compares inputs to one device, not different devices for different inputs.

Local detailed balance: a forward step hands the surroundings kT times the log of the odds of going
forward over going back. Chapter twenty grants it for the walker, and only there. Under it, heat times
time is at least twice the distance squared.

Unitary steps. Chapter twenty-one's quantum result is about a closed system that moves by unitary steps
on finitely many directions. An open system, one that hands something to its surroundings, is a
different question.


Theses

A thesis ties a definition to the world, and no argument can settle one. The book has two, stated as
theses where they're made.

The pointer thesis: the established record is the event that gets copied and relied on by parties who
didn't make it. Chapter nineteen, with what would test it.

The Thiele thesis: every physical process that computes with final answers has an exact description as a
machine run by one rule, with a next state for every state, written down in a way a program can follow,
on which the answer is a reading that no run from any input ever turns off. Chapter twenty-two. Robin
Gandy's principles for mechanisms are one road to that kind of tie, with real assumptions about the world
in it; I don't assert them of every physical system.
