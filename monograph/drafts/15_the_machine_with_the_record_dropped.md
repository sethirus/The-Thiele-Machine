The machine with the record dropped

Chapter seven put the machine behind a window and asked what gets through. Two states
can give the same view and differ in what matters, and a price worked out from the
window can't be exact if there's a pair like that. That was for one box. Now, with a
whole row of cups from chapter five and the cup over any machine from chapter fourteen,
I can ask the sharper version, which is also the one I care about. Take the ordinary
machine, the one with no cups and no tally, and look at what's missing from it. What's
the shape of everything it can't see, and what does the toll pay for, in terms of that
shape?


What's left when you cover the cups

Back in chapter four you covered a coin with your hand and watched the rest of the
machine run, move for move, as if the coin weren't there. Do that with everything: cover
the whole row of cups and the tally. What's left is a machine that steps the same way and
knows nothing about either.

That only works if covering them doesn't change how the rest moves. If some step of the
machine looks at a cup and goes one way or the other because of it, then covering the cups
leaves you with a machine that can't decide what to do next. So the honest condition is:
nothing in how the rest of the machine moves depends on the cups or the tally. Where that
holds, call what's left the uncovered machine. It's the ordinary computer.

Over any one state of the uncovered machine there's a pile: all the full states that look
like that one once you cover the cups, differing only in their cups and their tally. That's
chapter seven's pile behind one picture, with the window being "everything but the cups."

Every move has piles of its own too: the states that move sends to the same landing place.
Call those its landing piles. A pile behind a picture is everything that looks the same
before anybody moves. A landing pile is everything that ends up in the same place after one
move. Keep the two kinds apart, because this chapter turns on how they meet.


Pricing through a window, with a whole row

First the window question again, with a row of cups. Say a clerk prices each step from what
comes through a window before and after it. The price never misses if it charges at least
one for every step that turns up a cup. It's exact if it also charges nothing for every step
that turns up no cup. A clash is two steps that look the same through the window, where one
turned up a cup and the other didn't.

With one box, the fix in chapter seven was to put the box in the window. So you might guess,
for a row, that the window has to show some of the cups. Try the smallest case. Let the record
be a count that climbs: 0, 1, 2, and so on, with a cup for "at least 1," a cup for "at least
2," and so on. Let the window show only the first cup, "at least 1." Let the count go up on
some steps and sit still on others. Once it's past one, that first cup is up before and after
both kinds of step. So a step that turned up a later cup looks exactly like a step that turned
up nothing. That's a clash.

So, you might guess next, the window has to show every cup. That's wrong too, from the other
side. Same counting record, with two moves: one adds one, the other leaves it alone. Now let
the window show only whether the count is even. You can't read the count off that window: 0
and 2 look the same through it. But look at when evenness changes. It changes on exactly the
steps that add one, and on no other step. So "charge one exactly when evenness changed" is
exact, every time.

That changed how I think about windows. A window doesn't have to show the cups to price them.
It has to show them move.

The rest of the clerk's story carries over from chapter seven unchanged. If the window has a
clash, no price from it is exact, and any price that never misses has to overcharge at least
once for every step that turns up nothing but looks like one that does. That's the least it can
overcharge, and there's a price that overcharges exactly that much. If the window has no clash,
an exact price exists, and on a machine with finitely many states you can work it out.


What a paid move destroys

Now the piles. Chapter two showed that on a finite machine, a move that settles something for
good makes two arrows meet somewhere. Chapter five showed the same for a step that turns up any
cup, once cups only go up. Which two arrows? It matters a great deal.

If the two states that meet sit in different piles, the uncovered machine lost a distinction
too: two of its own states became one. If they sit in the same pile, the uncovered machine lost
nothing. What got crushed was only ever under your hand: two states that looked the same once the
cups were covered, told apart only by their cups or their tally, now made one.

You might guess it's always the second kind, because the cups are where everything happens. It
isn't always. It depends on whether the uncovered machine forgets anything on its own.

Here's the case where it's the second kind. Say the uncovered machine, for this move, never lands
two of its own states on one. Two full states meet. Cover the cups, and their uncovered parts land
in the same place too. But the uncovered machine keeps its states apart, so those two uncovered
parts must have been the same to begin with. So the two states that met sat in the same pile. In
that case every landing pile of the move lies inside one pile behind one picture.

And here's the case where it isn't. Take the stamp from chapter four, and let the window show the
box itself, so each state is its own picture. The stamp sends NO and YES to YES. Two states meet,
and they sit in different piles, because the uncovered machine is the stamp itself and the stamp
merges. Nobody ever had to cover anything.

One more fact about landing piles, and it ties back to chapter three. The halving rule said each
unit of cost pays for at most one halving. That holds exactly when no landing pile of a move has
more than two to the power of its price in it: a cost of one allows piles of two, a cost of two
allows piles of four. And that holds on a machine of any size.

So on a machine with finitely many states, a record that only grows, and an uncovered machine that
forgets nothing, the toll is a price on crushing a pile: on taking two states that look the same
once the cups are covered, told apart only by what's under your hand, and making them one.


What's left over is the ordinary computer

Put that together and you get the shape I've been circling since the night with the Flatland video
that the afterword tells about.

An ordinary machine, read through anything its moves never raise, is what's left when you cover the
cups of a machine that has them. Chapter four fitted the first cup. Over every state of the ordinary
machine there's a whole pile, states that differ only in their cups and tally, and the ordinary
machine can't tell them apart, as long as none of its steps looks at the cups. On a machine that obeys
the toll, a step that turns up a cup costs at least one, whichever cup and however many. On a finite
machine whose record only grows, when the ordinary machine forgets nothing, what that cost pays for is
exactly crushing two states of one pile into one. A window can charge the right price without showing
the cups, if it shows them move. And with the halving rule, the cost in halvings is never less than
what got crushed.

What I haven't shown is that any of this is out there in the world, that nature keeps a direction like
this over its own uncovered machines. That's a belief of mine, and nothing in this book proves it. What I
have shown, and you can check, comes with its conditions showing. A machine whose box answers to the
computation and climbs an order is a row of cups, one cup for each line. If it also has finitely many
states, never lets its record come down, and prices two arrows meeting, it has to pay this way. And when
its uncovered machine forgets nothing, what it pays for is exactly this. It's less than the Flatland
night promised me. It's also the part of it that held when I pushed.


Shortcuts

A box is worth turning up because something later can glance at it and not have to work the thing
out again, the way chapter ten's glance reads a block's bucket off a table without applying the rule from
scratch. Call any move like that a shortcut, and call it sound when it gives the same answer the long way
would have.

But everything in this chapter covered the box, and it could only do that because nothing in the machine
read it. A machine that reads its box to take a shortcut isn't the machine this chapter studied: cover the
box and the steps change. So what happens when the machine actually reads its box? That's the next chapter.
