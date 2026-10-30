Things I had to learn first

None of this is the argument. It's the vocabulary I had to go look up before I could make the
argument, written the way I understood each word once I had it. If a word in the book stopped you,
it should be here. If you already know a part, skip it. And if one of these is wrong, I want to hear
it, the same as anywhere else in the book.

The first four parts are words other people built. The last part is the words this book builds, each
with the chapter where it's built properly; here they only get a reminder.


Counting

A bit is one place that holds 0 or 1. Two bits have four arrangements, 00, 01, 10 and 11, and every
bit you add doubles the count, so n bits have 2 to the n. A byte is eight bits, 256 arrangements.
Nothing in a byte knows whether it's a number, a letter or a colour. That's a convention laid on top.

A function is a rule that gives every input exactly one output. "One next state for every state" is a
function from states to states. A function is one-to-one when no two inputs share an output. In the
book's pictures that's a machine where two arrows never land on the same spot.

The pigeonhole principle: put more pigeons than holes and some hole holds two. Chapter two does it with
four people and three chairs, and chapter two also tells how old it is.

The logarithm base two of a number is how many times you can halve it before you reach one. Eight
halves three times, so log base two of 8 is 3. For a number that isn't a power of two it lands in
between: log base two of 3 is about 1.58. That's why an AND gate, which sends three of its four inputs
to 0, needs about 1.6 halvings in chapter three. The natural logarithm, ln, is the same idea with a
base of about 2.718 instead of two; ln 2 is about 0.693.

A spread, in this book, is a list of chances, one for each state, that add up to one. An even spread
gives every state the same chance. The usual word is probability distribution.

Shannon's entropy, for a spread, is roughly the average number of yes-or-no questions you'd need to pin
down the state. An even spread over n states has log base two of n bits of it, and that's the most any
spread over n states can have. One bit is one question.


Machines and programs

A Turing machine is a tape of squares, a head that reads one square at a time, a state, and a card of
rules. For each state and each symbol under the head, the card says what to write, which way to move,
and which state comes next. Chapter one builds one on a strip of three squares.

The lambda calculus is Alonzo Church's way of writing computation as functions handed to functions,
with nothing else in the language. It computes exactly what a Turing machine computes. That match was
proved by other people; chapter one says so.

The halting problem: no program decides, for every program and every input, whether that program stops
on that input. Chapter one tells what Turing actually proved and who first called it the halting problem;
chapter seventeen puts it beside the other walls.

A diagonal argument builds the one thing that does the opposite of what a list says about it, so the
list has to be wrong somewhere. Cantor used it on lists of numbers, Gödel and Turing on statements and
programs.

Kleene's recursion theorem: for any way of transforming programs that a program can carry out, there's
a program that behaves exactly as if it had been handed its own source code. Chapter seventeen uses it.

P versus NP. P is the yes-or-no problems a program can solve in time bounded by some fixed power of the
size of the input. NP is the problems where a proposed answer can be checked that fast. Whether every
problem in NP is in P is open, and the Clay Mathematics Institute will pay a million dollars for an
answer. Chapter twenty-two says why nothing in this book touches it.

A cache is a copy of a result kept close at hand so the work that made it doesn't have to be done
again. Keeping a function's past answers in a table is what Donald Michie called a memo function.
Chapter sixteen tells that history.

A hash is a short fingerprint of a longer piece of data, made so that finding two inputs with the same
fingerprint is supposed to be hard. A hash chain folds each new record into the fingerprint of the one
before, so changing an old record changes every fingerprint after it. A Merkle tree folds records in
pairs, then pairs of pairs, up to one fingerprint at the top.

A commit, in a database, is the one moment after which a pile of tentative work counts. It's written to
a log, and a mistake after it gets fixed by another transaction, not by erasing. Chapter eight tells
where the idea came from.

Compare-and-swap is an instruction that writes a new value into a memory cell only if the cell still
holds the value you read a moment ago. The ABA problem is its blind spot: the value went from A to B and
back to A while you weren't looking, so the check passes on something that changed. Chapter sixteen has
it from IBM's manual.

A potential, in counting the cost of a run, is a number given to every state that measures how much is
stored up in it. If a step's cost plus the change in potential is never negative, then a whole run costs
at least what the potential dropped. Chapter eleven has where it came from.


Heat

Temperature in physics is measured in kelvin, from absolute zero. Room temperature is about 300 kelvin.

A joule is a unit of energy, about what it takes to lift an apple one metre. A zeptojoule is a
thousandth of a billionth of a billionth of a joule; an attojoule is a thousand zeptojoules.

Boltzmann's constant, k, is about 1.38 times ten to the minus twenty-three joules per kelvin. It turns
counting into physics: one bit of entropy, written in physical units, is k times ln 2. kT is
Boltzmann's constant times the temperature, an amount of energy; at room temperature it's about four
zeptojoules, and kT ln 2 is about three.

Landauer's principle, from Rolf Landauer in 1961: lowering the uncertainty about a device's state by one
bit hands at least kT ln 2 of heat, on average, to the surroundings. It's a claim about the world, and
it has critics. Chapter twenty says what he actually wrote and who doubts it. In this book it's always
an assumption, with its name on it.

Maxwell's demon is James Clerk Maxwell's little being at a little door between two boxes of gas, letting
fast molecules one way and slow ones the other, so one side heats and the other cools with no work
done. Chapter six tells how the looking got separated from the wiping.

Reversible has two meanings, and chapter twenty pulls them apart. A step is logically reversible when no
two states land on one, so you can always run it backwards. A process is thermodynamically reversible
when it produces no entropy. Whether a device that erases counts as thermodynamically reversible depends
on whether you ask about one known input or about a spread of them.

The second law of thermodynamics says the entropy of an isolated system doesn't go down. Chapter
twenty-one compares its shape with the toll's and doesn't claim they're the same thing.

Local detailed balance is the standard assumption in the physics of small noisy systems that ties a
step's odds to its heat: if a step forward is more likely than the step back, the forward step hands the
surroundings kT times the log of the ratio of the two chances. Chapter twenty grants it for the walker.

A noisy step is a move that goes from each state to each other state with some chance, instead of to
one certain next state. A unitary step is how a closed quantum system moves: it turns the list of
directions the system can point in without stretching or squashing any of them, so it can always be run
backwards. Chapter twenty-one does both.

A macrostate is a description that groups many exact states, the microstates, under one picture, the way
a temperature groups countless arrangements of molecules. In this book's words, a macrostate is a picture
through a window and its microstates are the pile behind it.


Structure

A relation is a list of which things stand in some connection to which: who is taller than whom, which
number divides which.

An order puts things so that some come before others, in a way that chains: if a is at or below b and b
is at or below c, then a is at or below c. Ties are allowed in the orders this book uses. A checklist's
arrangements, ordered by which ticks one has that the other doesn't, are an order.

A partition is a sorting of a pile into groups, nothing in two groups and nothing left out. Chapter ten
calls it a sorting, and a sorting with a door between the groups that only swings one way is an order.

A category is a collection of objects and arrows between them, where an arrow from a to b and an arrow
from b to c always give an arrow from a to c, following one and then the other; following arrows doesn't
care how you group them; and every object has an arrow to itself that changes nothing. Morphism is the
formal word for arrow.

A functor is a map from one category to another that sends objects to objects and arrows to arrows and
keeps the following-one-then-the-other intact. It's a translation between two worlds of structure.

A monoidal product is a way to set two objects side by side and get one, like pairing, with an empty
object that changes nothing when you set it beside another, and rules that make the grouping not matter.

The Yoneda lemma is a result deep in category theory. One consequence of it: an object is pinned down,
up to a perfect match, by the arrows coming into it from everything else. The afterword says what it
did for me. No argument in this book uses it.

An invariant is something that stays the same under a chosen set of changes. Emmy Noether showed in 1918
that in physics every smooth symmetry of a certain kind comes with a quantity that's conserved. Chapter
ten has it.

Structuralism, in the philosophy of mathematics, is the view that mathematics is about patterns of
relations, and that what fills a pattern doesn't matter. Chapter ten names the people who hold it and the
people who push back.


Words this book builds

A thing, a move, a run, a price, and a way to tell how settled the thing is, where settled never goes
back: page one. The toll is the one rule: a move that settles something more than it was costs
something. A Thiele machine is all of it together, with some run from a start you pick that actually
settles it more than it was. A Thiele machine with the price left out is the ordinary computer.

Two arrows meet when two different states have the same next state; the usual word is a merge. Fresh
paper, or a fresh state, is a state the run hasn't used before. Chapter one shows that every step of a
machine with one next state does one of three things: lands somewhere new, makes two arrows meet, or goes
round a loop.

The chairs and the done room are chapter two's picture of the pigeonhole principle, aimed at states that
read done.

Bennett's rule: a move where two arrows meet costs at least one. The rule is Charles Bennett's, from a
sentence he wrote in 2003; using it as the price is my choice. The halving rule is stronger: each unit of cost
pays for at most one halving, so a move pays at least the halvings in its worst pile-up, the place where
the most arrows land. Both are in chapter three.

The box and the flag: chapter four's smallest Thiele machine, two boxes and one move that sends both to
YES. Covering the coin is how any machine with a move becomes what's left of a Thiele machine.

A row of cups is a record with more than two places: cups that only ever get turned up. Chapter five.

Looking and keeping: a look can use up a blank page that gets handed back, so looking can be free.
Keeping what you saw for good is what pays. Chapter six.

A window is anything that lets part of a machine through to you: a camera, a display, a printout. It
doesn't see anything. Behind one picture is a pile, every full state that gives that picture. A clash
is two steps that look the same through a window, where one turns up a cup and the other doesn't.
Chapters seven and fifteen.

Established: a record that goes up only right after a passing check of the very claim it records, with
nothing that claim is about changed in between. It's a condition you put on the machine. Chapter eight.

Settled isn't the same as true. Settling is a sorting with a door that only swings one way. Chapter nine.

Structure, in this book, is relations, kept under chosen changes, carried by any stuff, relative to a
frame. A split with a one-way door is the smallest start, by the ruler chapter ten states.

The counter is a number in the state that starts at zero and that every step raises by exactly that
step's charge. Read as a receipt, it's a total that lives in the state, only climbs, equals the charges
on every path including the failures, and is the only such total for its price list. Chapter eleven.

A grouping is sound when every two things inside one group agree on what's being tested. Standing behind a
sound grouping entitles you to exactly the groupings you get by cutting it smaller. Chapter twelve.

Insight, as this book prices it, is a distinction made to stay. The price doesn't measure depth.
Chapter thirteen.

The base is the machine a box watches. A box answers only to the machine when what it reads depends only
on the base's run. A cup over any machine is chapter fourteen's result: such a box that never comes down
is a cup turned by some event the base passes through. A clean start is a start with every box down. A
toggle is a box that flips up and down as the machine runs; it answers to the machine and doesn't stay
up, so it's no cup.

The uncovered machine is what's left when you cover a machine's cups and tally, if nothing in how the
rest moves depends on them. It's the ordinary computer. A shortcut is a move that answers from the
record instead of redoing the work, and it's sound when it gives the same answer the long way would.
Chapter fifteen.

An edition is a count of how many times something has been written, so a box can be about one edition.
The guard is whatever decides whether a shortcut may run. The four doors are the four ways a finite
machine that reads its box to skip work can pay for it: fresh editions until they run out, a box that
comes down, room for every value checked, or wrong answers. Chapter sixteen.

The pointer thesis: the established record is the event that gets copied and relied on by parties who
didn't make it. A thesis, stated as one. Chapter nineteen.

The ledger sorts every claim in the book into shown, chosen, assumed, cited, thesis, or not claimed.
The Thiele thesis says every physical process that computes with final answers has an exact description
as a machine run by one rule, on which the answer is a reading no run turns off. The blindfold is the
picture that every machine that steps is a Thiele machine with its record covered and the price of
settling set to zero. All three are in chapter twenty-two.
