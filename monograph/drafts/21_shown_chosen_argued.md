What's shown, what's chosen, what's argued

This is the last chapter, and it's the one where everything gets laid out on the table at once,
sorted into piles, so you can see which pile each piece came from. Page one promised that: found,
assumed, chosen. Every chapter since has said which pile it was adding to. Here they all are.

Start with the smallest machine, because it carries the whole book in three layers. Two boxes, one
move that sends both to YES. What I found is the merge inside it: two states landing on one, which
counting forces on anything that keeps a distinction on finitely many states, and which nobody chose.
What I chose is the price: one unit on the move that climbs, a choice that could have gone another way.
What I assumed, and only where an argument says so, is the heat: that a merge of states the machine really
could have been in costs something in the world. That's Landauer's, not mine, and not shown here.
Everything below is one of those three, or it's a thesis, which is a fourth thing, and I'll say which every
time.


What it is, and what it's for

You've had the model since page one: a thing, moves, a way to tell how settled the thing is where settled
never goes back, some run from a start you pick that settles it more, a price on every move that's nothing or
more and never a refund, and the toll. A counter and a window come in when an argument needs them. You can't
buy it in a box. It isn't a device, a chip or an instruction set; those are things you'd build to carry it.

So if it computes nothing new, and it doesn't, what's it for? The same thing other ways of counting a
computation are for. The random-access machine, in the form Stephen Cook and Robert Reckhow gave it as a way of counting cost in 1973,
computes exactly what Turing's does, and it's worth having because it counts steps the way real memory is used. Andrew Yao's
cell-probe model, from 1981, counts only how many times you look into memory and leaves all the computing in
between out of the count. Alok Aggarwal and Jeffrey Vitter's model, from 1988, counts only the blocks moved
between a slow memory and a fast one. None of them computes one function more than Turing's machine. Each is worth
having for what it counts. The Thiele Machine's own count is what a run made the case, and what that cost. Look
at a computer through a window that drops that, and you get the ordinary picture, chapter four's coin covered by
your hand. Read a computer through whether it has stopped, and it's already a Thiele machine, with the price left
out.


The objection a theorist makes in four seconds

The toll is a floor, and a floor is easy to meet. Charge one unit for every move, whatever it does, and the toll
holds for any reading you like, because every move that settles something is a move, and every move costs one. So
any computer with a step counter beside it obeys the toll, for every yes-or-no question you could ask about it. A
clock passes.

That's exactly why the toll isn't the whole definition. Charging every move doesn't make a machine a Thiele machine;
the reading still has to never go back, and some run still has to settle it. And it means the toll, by itself, only
puts a floor under the settling move. It doesn't tie the rest of the bill to anything kept. One thing in this book
does tie it down, and it's a ceiling: ask that a run's total never be more than the number of times the box went up.
Chapter eleven showed that with a price that can depend on where the step starts, the floor and that ceiling leave
exactly one way of charging: one unit per raise, nothing else. With a price per move name, the way page one defines it,
no machine whose box ever goes up meets both, because the raising move, played again from YES, raises nothing and still
costs what it costs. A clock fails the ceiling the first time it charges a tick that raised nothing.

Two more things fall out of the same picture. The toll doesn't care how strong the machine is. A machine is called
Turing-complete when it can imitate a Turing machine; the toll never asks. Stronger, weaker, exactly as strong: bring the
parts, charge the settling move, and you're in. It was never about what you can compute. It's about what a move is allowed
to do for free.

And nothing is in scope just for being a computation. A Turing machine's run isn't an example of anything in this book
because it's a run. It becomes one when somebody says what the states are, which ones read yes, what each move costs, and
checks the toll. Until then the arguments say nothing about it, and I won't pretend they do. What chapter two found has no
such condition, though: every run of anything with one next state for every state lands somewhere new every tick, makes
two arrows meet once, or goes round a loop through its start and keeps nothing.


Bolting two together

Put two Thiele machines side by side: each move is a move of one or the other, and the costs add. Is the pair a Thiele machine?
It depends on how you read the pair.

Read it as "either box is up," or "both are." Then the pair's reading can only go up when one of the boxes goes up, that move
is a move of that machine, and that machine's toll already charged it. So the pair obeys the toll. Read through "both are," a
run that starts with both down and ends with both up raises each box once, each raise is charged by its own machine, so the run
costs at least two. From a start with one box already up, one raise is enough, so two is a floor only from the clean start.

Now read it as "the first is up and the second is down." That reading comes down the moment the second box goes up, and a Thiele
machine's reading never comes down. The pair is out.

So some readings of a pair keep the toll and some don't, and you can tell which by asking whether the pair's reading can go up
without one of the parts going up. Whether every way of building one machine out of others keeps the toll is a bigger question than
this book answers.


Steps that branch

Everything so far gave every state one next state. Plenty of models don't: a machine that can guess, a lambda calculus term you can
reduce in whichever place you like, a system of rewrite rules, a proof read as one rule applied at a time. Nothing earlier was stated
for those, so here are the two arguments, both short.

The first is chapter two's chairs on one choice of next step. Say only finitely many states read yes, none of them can step to a state
reading no, each has at least one next state, and some state reading no can step into the yes side. Pick one next state for each yes-state,
and the step in from outside. That's one more step than there are yes-states, each leaving a different state and landing on a yes-state, so
two land on the same one. It needs the yes side finite; Hilbert's hotel keeps a reading with nobody sharing.

The second follows one run, however its choices fall. Take the step where the reading goes up, and say it stays up for the rest of that run.
If the run is in the same state at two times after the raise, step both times back together. They can't stay equal all the way back past the
raise, because the state just before the raise reads no and every later one reads yes. So at the first pair that differs, two different states of that
very run step onto one. After the raise, the run makes two arrows meet or never repeats a state, on any number of states. Before the raise it can
come back to a state and then leave it for good with nothing meeting, which one rule can't do. A state with no next step at all is chapter one's
machine that stops: a reading kept by stopping is kept with nothing meeting.

For branching steps the first argument says less than it looks. In the lambda calculus, any term N is one step away from two different terms: apply
"do nothing" to it, or wrap it in a function that throws its argument away and hand that function anything. Two different states sharing a next state
is no news there. The second argument is the one that carries weight.

Where it all stops. Steps in continuous time have no next state to count, and nothing here covers them. Noisy steps where endlessly many states read yes,
and quantum steps whose kept part has endlessly many directions, get none of the finite arguments; the endless ladder keeps a reading with nothing meeting,
a fresh rung every tick. What still reaches them is the single run: the second argument covers any one run of them. And a truth isn't a process at all.
That a statement is provable is a fact with no step in it; the arguments are about a run that derives it.


What doesn't follow

Some things look like they follow and don't. Here they are, so you don't carry them out of the book by accident.

The counter isn't a heat meter. Once you pick the start and the price list, the number is forced by arithmetic, and it isn't energy. To read it as energy
you'd need to say which states carry information, how the charge relates to what a device gives off, and that both of those can hold at once; chapter twenty
did the last part and showed it only means the two don't contradict each other.

No question about what computers can do in a given time follows. Whether P equals NP is one of the seven problems the Clay Mathematics Institute put a million
dollars on, at a meeting in Paris in May 2000. One of the seven has been declared solved since: the Poincaré conjecture, by Grigori Perelman, who posted his proof in 2002
and 2003. A second has a claim on it. On 8 September 2026 OpenAI announced that one of its models, run as about ten thousand agents for
about eighty-eight hours, had produced a proof, written out for a proof checker, that a three-dimensional fluid flow with a smooth force
pushing on it can break down in finite time. That's one of the four answers the official statement of the Navier-Stokes problem accepts.
As of October 2026 other mathematicians haven't finished checking it, there's a dispute over credit with Tristan Buckmaster and Levent
Alpöge, who were working on a closely related result, and the Clay Institute's own page lists the problem as active, not solved. P versus
NP has no such claim. If a two-state clash on my machine settled it, I'd be owed a million dollars. Nobody owes me anything. A window that loses a box is a
fact about that window. A question like P versus NP is about everything every possible program can do within a budget, and nothing in these clashes reaches that
far.

The choice of event isn't forced. The pointer thesis is a thesis. The cup over any machine is a theorem, and it says the event is a choice.

The two walls stay two walls. Chapter seven's is about what a watcher can't get back through a window; chapter sixteen's is about what no inside procedure can
decide. Linking them would take an argument of its own, and this book doesn't have one.

The entitlement count in chapter twelve is handed its groups and its covering. It doesn't dig them out of an arbitrary run.

Records with chances on them don't inherit the uniqueness of the counter. Two honest random records can have the same branches and the same charges and still give
those branches different weights, one choosing evenly and one two to one. The price list doesn't fix the chances.

Every guarantee about an established record is about runs: any list of moves, from a clean start, on a step that does what it says, one writer at a time. Whoever sets
the start, the wire that carries the report out and the tools that built the step are outside that fence.

The five real systems are copies of pieces, with their limits named in chapter seventeen. None of them is a check of the running system. And I looked for a result about
real systems that needs the record and is ready to use. I don't have one.


The ledger

Here's every claim the book makes, one line each, with what kind of claim it is and where it lives. If a line here ever says more than its chapter does, the chapter is right
and the line is wrong.

Ledger is a good word for it, and it's older than bookkeeping. Around 1400 a ledger was a big book that lay in one place, a large church breviary, from the old verb for to lay;
the account-book sense turns up in the 1580s. Staying put is the job here too. This is the one place where every claim lies still, so you can come back and find it where you left it.

There's a way to use it that takes five minutes. Pick the sentence in this book you trust least. Find its line. Read the kind before anything else. Then go to the chapter and check
that the line says no more than the chapter does. If it says more, you've found my mistake.

  [table: the ledger]

"Shown" means shown on the page, under the conditions the chapter states, and checked by machine on small cases where a computer can try them all. "Chosen" means I picked it and said
so. "Assumed" means it's somebody's claim about the world that an argument leans on, named. "Cited" means it's somebody else's result, sourced. "Thesis" means it ties a definition to
the world and no argument can settle it. "Not claimed" means it looks like it follows, and it doesn't.


Whose is what

None of the pieces is mine alone, so here's the short form of who did what, with the long form in the appendix.

The toll isn't only my preference: on a finite machine a reading nothing turns off can only be turned on by a step that makes two arrows meet, so if that's priced, raising it costs; and
a raise where nothing meets needs endlessly many yes-states. The counting under it is the finite cousin of the recurrence Zermelo threw at Boltzmann in 1896, and the price on a merge comes
from Landauer's reset. Others had already priced merges. Thomas Ouldridge and David Wolpert put a physical price on them for finite automata in 2023. Ming Li and Paul Vitányi in 1996 put a unit
price on each bit a computation erases, or takes in, irreversibly, and Erik Demaine and his coauthors in 2016 charged for instructions that destroy information. What's here is the toll that kind of price forces
on a reading that stays.

That a price worked out from a window can't tell apart two steps the window shows the same is a fact about functions far older than this book; what's here is the pricing form of it. That a box driven
by the computation that never comes down is a cup on one event, over any machine, uses old pieces too: latches and history-keeping variables are old, and the result covers only boxes that never come
down. And the move of guaranteeing something about every run, which an established record leans on, isn't mine at all. It's the reference monitor's: James Anderson's 1972 study for the US Air Force, which asked for a mechanism that is "tamper proof,"
"always invoked," and "small enough to be subject to analysis and tests." Fred Schneider made the idea
precise for monitors that watch a run in 2000, and it was proved for monitors checked at every instruction by Arthur Azevedo de Amorim and his coauthors in 2015. What I put under it is a definition,
and its idea isn't new either: a check tied to the claim it looked at, with the toll charged on top.

What's mine is the putting together, and the bet that it belongs in the step.


The Thiele thesis

One more claim ties the counting to the world, the way Church and Turing's ties computing to it, and I'll state it as what it is, a thesis. I call it the Thiele thesis: every physical process that computes
with final answers has an exact description as a machine run by one rule, with a next state for every state, written down in a way a program can follow, on which the answer is a reading that no run from any
input ever turns off, on inputs accepted and rejected alike.

No argument settles it, because "a physical process that computes" isn't something you can do mathematics on. A model of computation is, and for a model written down as states, a step and a reading that stays,
what keeping takes needs no thesis: it's chapter two. The thesis is the tie between the two, and it's about what a physical computation pays for what it keeps.

There's an established road to that kind of tie, with its conditions in the open. Robin Gandy in 1980 wrote down principles for mechanisms, and Pablo Arrighi and Gilles Dowek restated his argument in a simpler form in 2012: sameness
across space and time, finitely many local states, a bound on how fast anything travels, and a start that differs from a quiet background only in a finite region. From those, the evolution is computable. Those
are real assumptions about the world, and they don't pick an event or a price in joules. I'm not asserting them of every physical system.

What can be shown sits on either side of the thesis. On one side, chapter two applies to every such description: a run that raises the answer merges two of its own states or never visits a state twice. On the other
side, look only at which inputs it accepts, and the thesis says something you can check: every set a physical process accepts with final answers is one a program can list. Here's how. Run the description from every
input, a step at a time across all of them, taking turns, and write an input down the first time its reading says yes. Nothing ever turns an answer off, so a yes seen once is the answer. And the other way: a set a
program can list is accepted by a machine that searches the list for its input and then steps from its stopped state to itself forever, read through "stopped," which nothing turns off. That builds a machine with the
same accepted set. It doesn't build an exact description of the original process. And nothing about how the keeping is paid survives that view: the same search held at its stop by a step to itself, which merges,
or by a counter that keeps ticking, which takes fresh states, accepts the same inputs.

"Final" has to cover the rejected inputs too, and here's why. Build a machine that starts at no, reads yes while program n is still running, and falls to no for good if it stops. It reads yes for good on exactly the
programs that never stop. No program lists those: one that did, run beside the plain search for a stop, would tell you for every program whether it stops, and chapter sixteen showed nothing can.


What isn't settled

Four things, each with what would settle it.

Whether Landauer's critics are right. That would leave every argument standing and one assumption unowned by the world. What settles it is measurements of real devices, and an argument about what the principle
means in general that both sides accept.

Whether the established record really is the pointer event. What settles it is chapter eighteen's three comparisons, run on systems people actually use.

Whether the toll is the right thing to price at all. The five real systems mostly built a wall or a penalty for contradicting yourself. I can't prove a toll is better, and I won't pretend the five say so.

And whether anything sits below a split with a one-way door, by a ruler someone can state. The arrow road met mine at the bottom. If you find a smaller start, it would change this book.


Back to the warehouse

Walk the warehouse from chapter eight one more time. Two computers, the same sorted list on both. On the one with the established record, a different part of the state tells you a check happened and a matching
commitment followed it, and the rules keep that tied to the edition that was checked. Put your hand over that part of the machine and the difference between the two vanishes from where you're standing. Change
the list and you can watch the old check go stale. Those are different operations with different consequences, and you can follow each one with your finger.

Carry a report out of the warehouse and you've got another question: what connects the report to the machine? The box doesn't answer it. A window, a copy, a second machine and a reader each bring relations of
their own, and the chapters asked, one at a time, which of those hold.

At the bottom of all of it is one distinction made to stay: a bead in a dip, a cell written, a question closed. What that settling keeps, what it takes, and what the price I chose charges for it. What I'm arguing is
that keeping is part of computation, not something you bolt on afterwards, and that the price belongs in the step. The box and its toll are the part of that I've worked all the way through. The rest is yours to push on.
