More settled

Up to now everything has had two places: not done and done, NO and YES, the coin
in one box or the other. Page one promised more than that. It said settled
doesn't have to be yes or no, and to picture a checklist.

That promise matters to me more than it might look. The hunch this whole thing
started from was that there's another direction, one ordinary computing doesn't
look along. A direction isn't a switch. A switch is just the first line drawn
across it. So this chapter takes the switch and finds out what happens when
there are many lines.


A row of cups

Get four cups and a strip of paper. Write five stages of an experiment along the
strip, left to right: proposed, set up, run, read, recorded. Agree to do them in
that order. Put an upside-down cup between each pair of neighbours. The first cup
means "the setup happened," the second "the run happened," the third "the result
was read," the fourth "the result was recorded." When you finish a stage, turn its
cup right side up. Cups only ever get turned up. None of them ever gets turned
back down.

  [figure: the five stages as cups, 0000 to 1111]

Two things to notice with the cups in front of you.

Each cup on its own is the latch from the last chapter: down or up, and once up,
it stays up.

And four cups were enough for five stages. Try it with three. Turn them up one at
a time, never back down, and count how many different arrangements you pass
through. None up, one up, two up, three up. Four arrangements, and you needed five.
You can't do it. Every time the arrangement changes, at least one more cup goes up,
and with three cups that can only happen three times. So three cups give you at
most four stages, and in general a row of cups that only go up can tell apart at
most one more stage than it has cups. A straight line of stages needs one cup
fewer than it has stages, and no fewer.

An ordinary binary counter holds a thousand stages in ten bits. That doesn't
break anything here: a counter's bits go down as well as up. These cups don't.

Now a harder strip. Some checks don't line up. One person repeats the experiment.
Somebody else, separately, works through the calculation. Neither one includes the
other. Draw a diamond: "neither" at the bottom, "experiment repeated" on the left,
"calculation checked" on the right, "both" at the top. There are two ways up, and
the two middle points don't come before or after each other.

  [figure: the diamond]

Put a cup on each point except the bottom: one for the repeat, one for the
calculation, one for both. Each cup is still a latch. The cups tell you which
things have happened. They don't tell you whether the experiment was set up right
or the calculation started from the right place. That's a different question, and
it comes later.


Naming what's on the table

Now that you've seen the pieces, here are the names I'll use for them.

The set of places the record can be, whether it's a straight strip or a diamond or
something with a hundred points, I'll call the direction.

Each question of the form "has the record reached at least this place?" I'll call
a line across it. One line is one cup.

To say "at least this place," you need to be able to compare two places: is this
one at or below that one? The strip and the diamond let you see that by looking.
Said exactly, it's a test you can put to any two places, and it has to follow two
rules. Every place is at or below itself. And if one place is at or below a
second, and the second is at or below a third, then the first is at or below the
third.

There's a third rule you might expect: if two places are each at or below the
other, they're the same place. Every strip and diamond on the table follows it.
To see what a rule like that is doing, take it away.

So take two places, left and right, and say each one is at or below the other,
without them being the same place. Now there are two cups: "at least left?" and
"at least right?" Put the record on left. Both cups are up, because left is at or
below itself and at or below right. Put it on right. Both cups are up again.
Look at the cups and you can't tell where the record is.

Now let the record swap between left and right on every step, for free. Is that
allowed? It never goes below where it was, since each is at or below the other.
No cup ever moves, so nothing ever settles, so the toll never asks for anything.
The record moved on every single step, and nothing on the table noticed. It never
settles anything either, so it isn't a Thiele machine.

Put the third rule back, and the cups tell you exactly where the record is.
Suppose two places leave exactly the same cups up. The cup for the first place is
up when the record sits on the first place, so it's up on the second place too,
which says the first is at or below the second. The same goes the other way round.
Each at or below the other: by the third rule, they're the same place. Without the third rule, the cups can miss moves. Neither is wrong. Dropping
the rule just tells the cups not to care about moves between places on the same
rung, and they don't.


The toll on the whole direction

One cup had one rule: the step that turns it up pays. Now there's a row of cups,
or a diamond, and one step can turn up several at once. Here's the rule I'd guess
first, and it turns out to be the right one: a step that turns up any cup pays at
least one. Three cups at once still only has to pay one. The rule asks whether a
step turned something up, not how many.

Does that still give you what one cup gave you? Take any run where some cup is up
at the end that was down at the start. Somewhere along the run, one step turned
that cup up, and that step paid. So the run paid at least one. And every step that
turned anything up paid, so the run paid at least once for each of them.

Look at what that argument never used. It didn't care whether the cups sat in a
row or a diamond. It didn't care how many cups there were. It didn't even use the
fact that cups never come back down: if something could knock a cup back over, the
argument still works, because all it needed was the one step where that cup went
up.

There's a simple way to tell, from places alone, when a step turns up a cup. Say a
step takes the record from place x to place y. The cup at y is up afterwards,
because y is at or below itself. Was it down before? It was down exactly when y
isn't at or below x. And if y is at or below x, every cup that's up at y was
already up at x, so nothing turned up. So a step turns up some cup exactly when it
lands somewhere that isn't at or below where it started. That's the toll from page
one, written on any direction.

And checking it one cup at a time is the same as checking it on the whole thing.
If every cup on its own follows the two-box toll, the whole direction follows the
toll, and the other way round.


One cup isn't enough

Could one cleverer cup do the job of all four? Say you keep one latch and try to
read the record's place off the latch together with whatever else the machine
shows.

Take the smallest case: a machine with nothing else to show, and a record that
climbs through three places, bottom, middle, top. One latch gives you two
answers, down or up. Three places, two answers. Some two places get read the same.
One cup can't do it.

Try a second guess, closer to how a single cup works. A cup's rule is: the new
value is the old value, or the event that turns it up. For a whole row, the obvious
copy is: the new place is the lowest place that's at or above both the old place
and the event's place. Test it. Take the strip bottom, middle, top, with a cup at
middle and a cup at top, and a record that jumps from bottom straight to top in
one step, and stays put at middle. With nothing else for the event to look at, the
event has to be one fixed place. From bottom, it has to take the record to top, so
the event is top. But then from middle, the same rule takes the record to top too,
and the record was supposed to stay at middle. The rule breaks.

What works is giving every cup its own event, and letting each cup's event look at
where the record already is. A later chapter builds that out over any machine.

How many cups does a direction need? That depends on what you ask the cups to
do, so start with the smallest job: tell where the record is, using cups that only
ever go up as the record climbs. For that job a cup doesn't have to be "at least
this one place." It can go up at several places, as long as climbing never knocks
it back down.

A straight strip needs one fewer cup than it has stages; you counted that above.
A direction that branches needs at least as many cups as the steps in its longest
climb, and at least enough to tell all its places apart.

Put three places above a bottom, none of them above another. The longest climb is
one step, but one cup can't tell four places apart, so it takes at least two. Two
do it, if you let a cup go up at more than one place: one cup that goes up at the
first and third places, one that goes up at the second and third. Every place
gets its own pattern. But look at those two cups alone and the third place seems
to sit above the first, because every cup that's up at the first is up at the
third too. If you also want the cups to show which places sit above which, it
takes three: one "at least this place" cup for each of the three.

And sometimes just telling the places apart needs more than both of those. Take
two places, each below two others. One step of climb, four places, and two cups
still won't do it, because both upper places would have to keep up every cup
either lower place has up, and two cups don't leave room for that. It takes
three, and showing which sits above which takes four.


Somebody got here first, from the side

People got here before me, from a direction I didn't expect: programming for many
processors at once. Lindsey Kuper and Ryan Newton's LVars, from 2013, are memory
cells whose value only climbs, where a program can't ask for the value itself,
only whether it has climbed past some point. That's a cup. Two writers running side
by side can push the value up in different orders, and a point once passed stays
passed. Their programs come out the same every time partly because of which
questions the language lets you ask: a program allowed to ask whether the cup is up
yet could still see the other writer's timing.

Amin Timany and Lars Birkedal, coming at it from proofs about programs, show in
their 2021 paper, as I read it, that any order at all can be carried this way in a
logic for proving programs correct, as a value that only climbs and that the
running program never reads. That's the closest I've found to somebody else
cutting a direction into lines.

The two of them rest on the same shape, a value that only climbs and a question
that only asks whether it's past a point, and they use it for opposite jobs. In an
LVar the question steers the program. In Timany and Birkedal's logic, the value
lives in the proof and the program never looks at it. The shape is theirs first.
What I can't find in either is a price on crossing a line.


Why crossing a line has to cost

Chapters two and three got the toll out of the chairs: on a finite machine, a move
that settles something for good lands two states on one. Does that survive a whole row
of cups?

The chairs need one yes-or-no question to count with, and now there are many
cups. So which cup? The first one I'd reach for is the cup at the place where the
record starts. That goes nowhere: the starting state already has that cup up, so
there's no newcomer coming in from outside. The cup that works is the one the step
turns up, the cup at the place where the record lands. It's up afterwards and it
was down before. So put everybody who has that cup up in the done room, and the
state the step starts from is the person by the door.

Now it's the chairs again, once for that cup. If the move keeps everybody in the
room inside and never lands two of them on one chair, they fill every chair, and
there's none left for the newcomer. So one of two things happened: two arrows met,
or somebody inside got moved out, which means that cup went back down. If cups
never come back down, it has to be the first one. Two arrows meet.

And then Bennett's rule from chapter three does the rest. A move where two arrows meet costs at
least one, so a move that turns up a cup costs at least one. The toll on the whole
direction rests on the same three things as the toll on one cup: finitely many
states with each cup up, cups that never come back down, and a price on two arrows
meeting.

Each of those can be knocked out, and each one goes the same way it did for one
cup. Let the states be all the whole numbers and let the record count up by one on
every step, free: nothing ever merges, the price list has nothing to charge, and
every step turns up a new cup. That's the endless strip, paying in fresh paper.
Let a two-state record swap back and forth: nothing merges, and the cup it turns
up gets knocked back down. That's the coin. Let a two-state record stamp every
state up and charge nothing: the arrows meet and nobody asked them to pay. That's
the stamp at zero.

So nothing new got smuggled in when one cup became a row, and nothing the one cup
needed got left behind. You might expect the diamond to need some extra rule for
the two middle cups that don't come before or after each other. It doesn't. Every
cup gets its own room of chairs, and the argument in each room is the old one.
