Why charge for it

Everything so far has been counting, and the counting isn't mine. On a finite
machine, settling something for good means two arrows meet somewhere. On an
endless one, it can mean fresh paper forever instead. Nobody gets to choose
that. You drew it.

Page one also said something I do get to choose: I charge for the move where the
answer goes from not done to done. This chapter is about how much of a choice
that is. If it's nothing but my preference, then the whole machine is a long way
of telling you my favourite colour, and you should treat it that way. So I want
to find out what it rests on.


A rule you can refuse

I'm not going to ask you to believe a price. I'm going to write one down as a
rule, in the smallest form I can, and you can accept it or refuse it.

  Any move where two arrows meet costs at least one.

That's all it says. It doesn't mention done or not done. It doesn't mention
checking or settling. It puts a price on one thing: a move that sends two
different states to the same place.

It isn't my rule. Charles Bennett, who spent decades working out what computing
has to cost, put it this way in 2003: what has to cost is "the erasure
of a bit or the merging of two computation paths." Two arrows meeting is two
paths merging. I'm taking his rule as it stands and writing it on the move.

Now put it next to the chairs. The chairs said: on a finite machine, a move that
settles something for good is a move where two arrows meet. The rule says: a move
where two arrows meet costs at least one. Put those two sentences side by side
and read them together. A move that settles something for good costs at least
one.

That's the rule from page one, the one I said was my choice. I call it the toll.
That was my word for it before I could prove any of this: there had to be a toll,
a cost in the transition, in the step itself. And look at where it came from just now. Nobody
handed it to the machine. It fell out of the chairs and Bennett's rule together.

So it isn't only my preference. But it isn't free of choices either. Count what
went into it. There are three, and you can refuse each one.

The done states have to be finitely many, so the chairs run out.

Done has to stay done.

And two arrows meeting has to cost something.

Accept all three and you don't get to refuse the toll. It comes with them. Refuse
any one, and the toll goes back to being my choice. So the question "did I have
to pick it?" has turned into three smaller questions, and those are better things
to argue about. For each one there's a machine that walks out through that door,
and you should see each one, because a rule you can't picture breaking is a rule
you're taking on faith.


The first door: endless paper

You've already seen this machine. It's the strip from the last chapter that never
runs out. Each move writes a 1 in the next empty box. Done stays done, the first
move settles it, and no two arrows ever meet.

So Bennett's rule never charges it anything. Two arrows never meet, so there's
nothing to charge. The strip settles its answer at no cost on the price list.

But it didn't get out of paying. It pays in fresh paper, on every move, forever.
A price list that only charges for arrows meeting just isn't looking at that
column. And on any real machine, the paper runs out, and the chairs come back.


The second door: let it come back down

Take one coin. The only move is: turn it over. Heads is done, tails is not done.

Draw the arrows. Tails goes to heads. Heads goes to tails. Two dots, two arrows,
and they never meet. So Bennett's rule never charges it.

And it does settle something: tails goes to heads, not done to done. At no cost.

What it broke is the second condition. The same move that took tails to heads
takes heads back to tails. Done doesn't stay done. So it's not keeping anything.
It's flipping a switch back and forth, and the page-one definition already throws
it out: a Thiele machine's done never goes back.

Here's the part of this I found sharpest. Forget about done staying done
entirely, and keep only the finite chairs. Take any move that takes some state
from not done to done. Now go through the done states, one at a time, and ask:
does this move send any of them back to not done?

If it does, you've found the coin: the move takes something back somewhere.

If it doesn't, then this move keeps every done state done. That's all the chairs
needed, for this one move. So two arrows meet.

There's no third answer. On a finite machine, a move that settles something
either has two arrows meet, or it takes something back somewhere else. A move that
settles for free and never takes anything back doesn't exist.

That's narrower than "every record costs." It's still true, and I'll take it.

One more picture, so you don't think it's tidier than it is. Three cards, T0, T1
and T2, with a star on T1. The move sends T0 to T1, T1 to T2, and T2 to T1. Look
at what it does. T0 gains the star: something settled. T1 loses the star:
something taken back. And T0 and T2 both land on T1: two arrows meet. So Bennett's
rule charges this move, and yet it doesn't keep anything for good. Charged moves
and permanent moves aren't the same list. What's true is one direction: on a
finite machine, every move that settles something for good is a move Bennett's
rule charges.

And there's an exact way to say which moves Bennett's rule charges no matter what
the rest of the price list looks like. A move where two arrows meet gets charged
by every price list that follows the rule; that's what the rule says. A move
where they never meet doesn't have to be: price that one move at zero and every
other move at one, and the rule is still followed. So the moves the rule forces
you to charge are exactly the moves where two arrows meet. That one holds on any
machine, finite or not.


The third door: don't charge for it

Take a sheet of paper. It's either blank or stamped. One move: stamp it. Blank
goes to stamped, and stamped stays stamped.

Check the conditions. Two states, so the chairs run out. Stamped stays stamped.
Blank goes to stamped, so something settles. And draw the arrows: blank goes to
stamped, stamped goes to stamped. Two arrows meet. Everything the chairs needed
is here.

Now set the price of the stamp to zero.

Nothing in counting stops you. The stamp merges two states, and you just decided
merges are free. The answer settled, and the bill says zero.

Price the stamp at one instead, and every condition holds at once, so the three
can live together. That stamp at one is the smallest Thiele machine there is, and
it gets its own chapter. But the third door asks whether they have to live
together, and counting can't say so. The only thing that could close this door
is a claim about the world: that two arrows meeting really does cost something,
out there, in a real device.

The nearest such claim is Rolf Landauer's, from 1961: that forgetting gives off
heat. It's measured for a few devices and argued over for everything else, and
it gets its own chapter, with the people who doubt it named. I'll say one thing
about it now, because it matters here. Bennett's rule as I wrote it charges every
move where two arrows meet, whether or not you already knew which state you were
in. Landauer's heat, as that chapter will show, is only owed for what you didn't
know. The rule I'm using is the worst case on purpose: a move that has to work
whatever it's handed pays for the worst it could do.

So that's where the toll stands. Accept finite chairs, done stays done, and a
price on two arrows meeting, and the toll isn't a choice; it's what the three
say together. Each of the three is a choice, and I've shown you a machine walking
out through each door. The physics that would close the third door is a premise,
and I'll always call it one.


How much

The toll says at least one. Counting can say more, if you let it.

Take four cards and write A, B, C and DONE on them. Pick one without showing me.
Now cover its face with a label that says DONE. Whatever you picked, the face
now says DONE. Before the label, how many yes-or-no questions would it take me to
find out which card you had? Two: "Is it A or B?" and then one more. After the
label, I don't need to ask anything, because there's only one thing the face can
say. Two questions' worth of difference got squeezed out.

That's four states landing on one. Each question you no longer need halves the
number of places you could have been: four to two, two to one. Two halvings.

If you're willing to go one step further than Bennett's rule, and say each unit
of cost pays for at most one halving, then that move costs at least two. And two
is enough. In general: if m states were already done and the move settles k more,
all m + k of them land on the m done ones, and the move has to pay at least as
many halvings as it takes to get from m + k down to m. One newcomer next to one
done state is one halving: the toll again.

(The label can be peeled off, so the cards only show the squeeze on what the face
says. Whether anything physical got erased is a different question, for the heat
chapter.)

There's a plainer way to say what the halving rule asks for. Look at one move and
find the place where the most arrows land. Call that its worst pile-up. A cost of
one allows piles of two. A cost of two allows piles of four. A pile of three
already needs two. That's why the m + k states in the done room had to pay at
least that much: spread m + k arrows across m chairs as evenly as you like, and
the fullest chair still gets at least (m + k) / m of them. So the rule asks every move to pay for the worst it could ever
do, whichever state it's actually handed.

That worst case has a home in physics. Philippe Faist, Frédéric Dupuis, Jonathan
Oppenheim and Renato Renner worked out in 2015 the least work any logical step
needs when it has to succeed every time, on every input, with no averaging. It
comes to exactly that logarithm of the worst pile-up. An AND gate sends three of
its four inputs to 0, so it needs about 1.6 halvings' worth, two in whole units.
My rule counts the same thing in units of cost. Joules don't come into it.

You can also count the whole run this way. Write N different starting states on
cards. Run each card through the rule once, and stack the cards that land on the
same state into one pile. Do it again with the piles. Each tick, count how many
different states you're down to. The drops add up exactly: what you started with
equals everything lost along the way plus what's left at the end. If you end up
with fewer than you started with, some tick had two arrows meet. Turn the cards
over first, though. Two runs can show the same answer on the front and still be
different underneath, and those are different states.

A word about the k in all this. Physicists write kT for heat at a temperature,
and when the counting meets the physics in the heat chapter you'll see k with a
little B hung under it, for Boltzmann. That letter has a story I didn't expect.
Boltzmann's grave in Vienna has S = k log W carved on it: entropy is a constant
times the logarithm of the number of ways the parts could be arranged. The idea
is his. But the constant, and the equation written that way, came from Max
Planck, around 1900. In his Nobel lecture in 1920 Planck said the constant "is
frequently termed Boltzmann's constant, although to the best of my knowledge
Boltzmann himself never introduced it." So the most famous constant in this
corner of physics wears the name of a man who never wrote it down. Take the
constant away and what's left is the logarithm of a count, which is a number of
halvings, which is what the cards just gave you. The constant is the exchange
rate between halvings and heat. Whether the world honours that rate is the
premise.


Found, assumed, chosen

That's the place to sort everything so far into three piles, because the rest of
the book depends on where each thing falls.

I see it like this: I didn't invent a machine. I found one. That walks straight
into one of the oldest fights in mathematics, so here's a short trip into it.
G. H. Hardy, the Cambridge number theorist who wrote A Mathematician's Apology in
1940, came down on the found side about as hard as anyone ever has: he wrote that
mathematical reality lies outside the people who study it, and the theorems they
like to call their creations are really notes on what they saw. The German
mathematician Leopold Kronecker supposedly split the difference: God made the
whole numbers, and everything else is the work of people. Supposedly, because
push on that line and it gets thin fast. It comes down through Heinrich Weber, in
a memorial piece written after Kronecker died, pointing back to a lecture from
1886, and that's the only source I could find anybody citing. It's a great line
with one witness.

None of that settles whether I found the Thiele Machine or made it up, and a proof
wouldn't settle it either. So it's a conviction, and I'll call it one. What it
changes is how I hold the thing: like something that was already there, which
means I can be wrong about its shape and the shape won't care. And "found" only
covers what counting forced. Here are the three piles.

Found: what counting forces on any machine.

Every step of a machine with one next state for each state lands somewhere new,
circles back to its start, or has two arrows meet, and after it comes back it
repeats forever. You drew that in chapter one.

A run that settles something and keeps it can't circle back to its start, so it
has two arrows meet or takes fresh states forever. When only finitely many states
are done, the move that settles it has two arrows meet. You sat people in chairs for that.

A machine that stops, with no next state, slips past all of it, and gets caught
the moment you say what it does on the next tick.

Assumed: what the found pile is taken to stand on in the world.

That two arrows meeting in a real device, when the device really could have been
in either state, gives off heat. That's Landauer's principle, and it's an
assumption here, never proved, with its critics named in its chapter.

That a real device can only tell apart finitely many states in any bounded space,
so its fresh paper runs out. Nobody has measured where that ceiling is.

That the machine starts clean: if done means "this happened," that's only because
it started at not done. That start is put in by hand.

Chosen: what I add, each of which could have gone another way.

To put the price inside the step, as part of what a step is.

That done stays done. That's in the definition because I put it there.

The toll: at least one on the move that settles something. With finite chairs
and done staying done, it follows from a price on two arrows meeting, and that
price is a choice too.

Which thing gets to count as settling, and what the price list charges. Nothing
I've shown you forces either one.

Everything after this chapter is built on those three piles, and I'll keep saying
which pile each piece comes from.
