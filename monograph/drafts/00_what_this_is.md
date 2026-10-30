What this is

I think in shapes, so I'll start with one.

Take a thing. Anything. A coin on a table, a light switch, a page in a notebook.
Right now it's one way. It could be another.

Now do something to it. Flip the coin, hit the switch, write on the page. That's
a move: a direction that takes the thing from how it is to how it is next.

Here's a computer you can run with a pencil. Write 3 on a scrap of paper. The
move is: erase the number and write the next one up. Do it twice. 3, 4, 5. You
just added 2 and 3. Nothing happened there but a thing, a move, and the next
thing. Hold on to that picture; whether it covers every computer is something
I'll have to earn, and I will, later, with you watching.

Here's the part I couldn't let go of. Some moves just shuffle. Flip the coin and
you can flip it back, and nothing is different for good. But some moves make a
difference that stays. Write a word in pen. Blow a fuse. Check an answer and mark
it checked. After that move something is the case that wasn't before, and it
stays the case.

I figured there had to be a cost in that step. Not in the shuffling. In the step
where something goes from not settled to settled and stays there. That was a
hunch, so test it on the pencil computer.

Tell it when to stop: count up, and when you reach 5, stop. Ask one question of
each number: is it done? 3, no. 4, no. 5, yes. And once it says yes it keeps
saying yes, because the machine has stopped.

A machine that has stopped is still somewhere on the next tick. It stays where
it is: 5 goes to 5. Draw the arrows. 4 goes to 5. 5 goes to 5. Two different
starting places, one landing place. Standing on 5, you can't tell whether you
just got there or have been there all along.

Could you dodge that? Try letting the stopped machine rock back and forth
instead of sitting still: 5-tick, 5-tock, 5-tick, both of them saying done. Draw
the arrows. 4 goes to 5-tick. 5-tock goes to 5-tick. Two arrows land on 5-tick,
the spot where you came in. Rocking only moved the place where they meet. The
one way out is to never land anywhere twice: make every tick write something
new, a tally mark, the time, anything, so the paper never repeats. That works as
long as there's paper. On a finite sheet you run out, and two arrows land on one
spot again.

So whenever this machine settles its answer and keeps it, something gives.
Either two states become one, or it uses up fresh paper on every tick for as
long as it runs. That part isn't a hunch. You drew it. You drew it for one small
counter; the book proves it for any machine that goes from one state to a next,
and shows you where.

What I do with it is a choice, and I'll say so: I charge for the move where the
answer goes from not done to done. Charging for it is up to me. That something
has to give once it makes that move isn't. The two arrows don't always meet on
that very move. Give done two spots, 5a and 5b: 4 goes to 5a, 5a goes to 5b,
and 5b stays put. Now the arrows from 5a and 5b meet on 5b, a tick after the
answer settled. But after the move from not done to done, there's no avoiding
it: two arrows meet somewhere, or the paper never repeats.

Two more things have to be pinned down before the rule means anything, and you
can see both with what's already on the table.

First, take the coin again. Flip it, flip it back, forever, free. Ask whether
it's settled. It never is. A rule that says "a move that settles something has to
cost" never asks the coin for anything, because the coin never settles anything.
So the rule alone would let a coin that does nothing count. The machine has to
actually settle something, at least once.

Second, suppose a later move could pay you back. The move that settles charges
you one, the next move hands you one back, and the whole run comes out free. So
prices can be nothing or something, never a refund.

One last thing before the whole definition. Settled doesn't have to be just yes
or no. Take a checklist with three boxes. None ticked, one, two, all three: each
tick settles it a little more, and ticks don't come off. "Done or not" is the
smallest case, a checklist with one box. So when I say "more settled" from here
on, picture the checklist.

So here's the Thiele Machine, all of it. A thing. Moves that take it to the next
thing. A way to tell how settled the thing is, where settled never goes back to
unsettled. Some run, from a start you pick, that actually settles it more than it
was. A price on every move, nothing or more, never a refund. And one rule: a move
that settles something more than it was costs something.

That's the whole definition. The rest of the book works out what follows from
it, one step at a time, and tries to break it.

Now look back at the pencil computer with a stop in it. That's Turing's machine,
in miniature. Turing's machine, from his 1936 paper, is a tape and a table of
rules: from where it is, the table says where it goes next. A thing and moves.
It already has something that settles and stays settled: whether it has
stopped, the same question you asked of 3, 4 and 5. What Turing never put in
is a price on the move that stops it. Put one in, and a Turing machine that ever
stops fits every line above. So this isn't a rival to Turing's machine, and it
computes nothing his can't. His machine is one kind of Thiele machine, with the
price left out.

Now try this. Give two people the same messy list of numbers. The first sorts it,
then goes back down it checking that every number is no bigger than the next.
The second copies a sorted list off somebody else's sheet. Now look at the two
sheets. Same numbers, same order. Look as hard as you like: nothing on either
sheet tells you which one was checked. The difference was real, and neither sheet
kept it. It's the same thing you saw standing on 5: you can see where you are,
and not how you got there.

So put a box on each sheet that says checked. A plain Thiele machine charges for
ticking the box, but nothing in the rules above stops the copier from paying and
ticking it anyway. Paying for the tick doesn't make it true. So add one more
condition: the box can only be ticked right after a check of that very list
passes. Now the copier's tick is refused, and a ticked box tells you a check of
that list passed. I call a box like that established. It's a condition you put on
the machine. The bare definition doesn't hand it to you.

It's called the Thiele Machine. The afterword says why.
