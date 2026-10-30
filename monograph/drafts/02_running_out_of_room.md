Running out of room

The last chapter left one door open. A run that settles its answer and keeps it
either has two arrows meet somewhere, or it lands on a new dot every step,
forever. Endless fresh paper. On a sheet that never ends, that's a real way out.

But nobody has a sheet that never ends. So what happens when the paper is
finite?


Four people, three chairs

Do this one with real chairs, or with coins on a table. It takes about a minute.

Draw a box on the floor and call it the done room. Put three chairs inside it and
one chair outside, by the door. Sit four people down, one per chair. The people
are the states the machine could be in. The three inside are already done. The
one by the door isn't.

One move of the machine moves everybody at once: each person gets up and goes to
whatever chair the rule sends them to. There are two rules about where they can
go.

Nobody inside may end up outside. Done stays done.

The person by the door has to end up inside. This is the move that settles their
answer.

Now try to finish the move with one person in each chair.

You can't. The three inside have to stay inside, so they fill the three inside
chairs between them. The person from the door has to come in too, and there's no
fourth chair. Somebody has to share. Two people, one chair: two arrows, one
landing place.

Try it with more chairs. Ten inside, one by the door. Eleven people have to fit
into ten chairs. A thousand inside, one by the door: a thousand and one people,
a thousand chairs. It doesn't matter how big the room is, as long as it has a
size. The insiders take every inside chair, and the newcomer has nowhere to go
but somebody's lap.

Notice who ends up sharing. It doesn't have to be the newcomer. The rule could
send the newcomer to an empty-looking chair and send two insiders to the same
chair somewhere else. Page one already showed you that: 4 went to 5a, and the
arrows met a tick later on 5b. What's forced is that two arrows meet somewhere
in that move. Where they meet depends on the rule.

Two words I'll need from here on. A move is one-to-one when two different
starting places always end up in two different places: nobody shares a chair. A
move that isn't one-to-one is a merge: two arrows, one landing place.

Now say what the chairs showed in those words. Take any move that keeps done
states done and takes one state from not done to done, on a machine with K done
states. If the move were one-to-one, the K people already inside would fill all K
inside chairs with nobody sharing, and the newcomer would have nowhere to land.
So it can't be one-to-one. It merges.

That's the whole argument, and it's the chairs. The only thing finiteness did
was make "it fills all K done states" true: K people into K chairs with no
sharing leaves no empty chair. That's the one place the size of the room
mattered.


This is very old

The piece of mathematics doing the work there is old, and it isn't mine. Put more
things into boxes than there are boxes, and some box gets two. People call it
the pigeonhole principle. The earliest use of it I could find is Jean Leurechon
in 1622, arguing that somewhere two people must have exactly the same number of
hairs on their heads. The first name for it I could find came from Dirichlet, who
used it in 1842 and later called it the drawer principle. It's the kind of fact a
child accepts and a mathematician spends a whole career finding new uses for.

And the use I just made of it turned out to be old too. I found that out twice,
and the second time stung more.

The first time was physics. In 1876 Josef Loschmidt pointed out, against Ludwig
Boltzmann's account of how a gas settles down, that the laws of motion run just
as well backwards: reverse every molecule and the gas retraces its steps. Twenty
years later, in 1896, a young assistant of Max Planck's in Berlin pushed harder.
He used Henri Poincaré's recurrence theorem from 1890, which says a system like
that comes back as close as you like to where it started, again and again, to
argue that nothing in it can climb forever. Give it time and it comes back down.
The assistant was Ernst Zermelo, the same Zermelo who would put set theory on
firm axioms twelve years later. Boltzmann answered the same year, not very
politely, that you'd have to wait so long for a return that nobody would ever see
one. (Jos Uffink, who wrote the Stanford Encyclopedia's entry on Boltzmann's
physics, calls that reply drenched in sarcasm and bitterness, and calls
Zermelo's paper a careful logical argument.)

You can see Zermelo's point on the dots from the last chapter. Draw a finite
number of dots where no two arrows ever land on the same dot. Every dot has one
arrow in and one arrow out. Follow any run. Can it ever reach a dot it's been on
before, other than the start? No: that would take two arrows into one dot. So
since the dots are finite and it can't keep finding new ones, it has to come back
to its start. Every run goes around in a loop. Now color the start white and some
dots black, done stays done. Can a run go from white to black? If it did, it
would have to come back around to its white start, and black can't go back to
white. So it can't. A machine where no two arrows ever meet, on a finite sheet,
can never settle anything new for good.

That's Zermelo's objection, with the infinities taken out. On a finite set you
don't need Poincaré's theorem. And the wait isn't enormous; it's at most as many
steps as there are dots. Zermelo was aiming it at the second law of
thermodynamics, and settling an answer never came into it. A quantum version
came in 1957, when P. Bocchieri and A. Loinger proved that a closed quantum
system comes back close to where it started. That's a neighbour, not the same
proof: even a small quantum system has endlessly many states, and you'd have to
say how a record is read off it.

The second time was computer science, and that's the one that stung. Picture a
small machine that reads letters, one move per letter. If every letter just
reshuffles its states, no two arrows meeting, people call it a permutation
automaton, and the sets of inputs such machines can pick out are called group
languages. Jean-Éric Pin's 1992 paper on reversible automata sorts out exactly
what those machines can recognise, and in that world the chairs argument is
folklore: a machine like that can't recognise "has seen a b at some point,"
because recognising it would mean a done that stays done. Going quantum doesn't
get around it. Alex Brodsky and Nicholas Pippenger showed in 2002 that a quantum
version that only measures once, at the end, recognises exactly the same group
languages. One that's allowed to measure after every letter, and stop on what it
sees, does better, and "has seen a b" is one of the things it picks up. A
measurement that can stop the machine is a record that stays. That's the extra
thing that lets it in.

Then the closest one, and it's recent. In 2023 Thomas Ouldridge and David Wolpert
worked out the physics of a small machine built the way real computers are: the
same physical step run over and over. They sorted what such machines recognise
into two kinds. If the smallest machine for a job has a letter where two arrows
meet, every machine for that job does, and on their derivation running it gives
off entropy that no cleverer design can get back. If the smallest machine only
reshuffles, they find it can run with no unavoidable entropy at all. One of their
worked examples is exactly "has not seen a b," which is "has seen a b" turned
inside out. So the counting, and a physical price on it, were in their paper
three years before this book. Their price comes out of the physics of the device.
Mine, in the next chapter, is a choice I make and say so.

There's a cousin that speaks a different language. Constructor theory is David
Deutsch and Chiara Marletto's way of stating physics as which transformations a
device that runs in a cycle can and can't bring about, and in it a task is
irreversible when it's possible and its reverse isn't. Marletto, Vlatko Vedral
and their coauthors in 2022 built an irreversible task out of a machine of
quantum bits that swap a little with each other, and ran it with photons. Maria
Violaris and Marletto argued the same year that this machine, run in a cycle,
can turn a pure quantum bit into a mixed one and never back, even though every
piece of it can be reversed, and that this suggests erasing may cost more than
the usual bound. The chairs are a small, exact, classical relative of that:
a set of states the step can't leave, a task that's possible, and no way back.
Theirs is quantum and approximate and aimed at physics. Mine is counted. Deutsch
and Marletto's paper on information, from 2015, has another neighbour in its
section 8.6: measuring one quantity disturbs another for good, and nothing can
undo the disturbance while the result is still being kept. That's a second way of
saying that a record that stays makes the step impossible to run backwards.

And Morgan Rogers, in his papers of 2019 and 2021 on what mathematicians call
toposes of monoid actions, gives the general home for one more way to see it:
if every move can be undone by some other sequence of moves, you can never enter
a room you're not allowed to leave, because the undoing sequence would have to
take you back out. On a finite set, a move where no two arrows meet can always be
undone that way: repeat it enough times and everybody comes home.

So the counting isn't mine. It had homes in physics and in automata long before
me, and a physical price on it a few years before me. What I do with it starts in
the next chapter.


The hotel that never runs out

Now the way out. If the chairs run out, give the room more chairs. Endlessly
many.

Take a strip of paper that never ends. Each move writes a 1 in the next empty
box. Done means "there's at least one 1 on the strip." Check it against
everything so far. Done stays done: once there's a 1, there's always a 1. The
first move takes the empty strip to done. And no two arrows ever meet: two
different strips always become two different strips, because you can always
erase the last 1 and get back where you were. So here's a machine that settles
something, keeps it, and never merges anything.

It got out of the chairs. It didn't get out of paying. Look at what every move
does: it writes in a box nobody has used before. The first move does it, and so
does every move after that, forever. That's the other column from the last
chapter: fresh paper on every tick.

If the endless strip feels like a cheat, it's a famous one. David Hilbert told a
story in a lecture course in the winter of 1924 to 1925 about a hotel with
endlessly many rooms, every one of them taken, where a new guest still gets a
room. Everybody moves from room n to room n + 1, and room 1 is left empty. Nobody
shares. The one-to-one move leaves a gap. That's the strip.

The part worth checking is that Hilbert never published it. The hotel got famous
because George Gamow put it in a popular book in 1947, and for a long time it
wasn't clear Hilbert had told it at all. The historian of science Helge Kragh
first guessed that Gamow made it up. Then Tilman Sauer, who had helped edit a
volume of Hilbert's lectures, pointed him to Hilbert's lecture notes, which had
just been printed in 2013, and in 2014 Kragh took his guess back in a paper called
"The True (?) Story of Hilbert's Infinite Hotel." Keep the question mark. Even
Kragh's paper puts the lecture in January 1924 in one place and January 1925 in
another. Still, this time a story everybody repeated had a real lecture behind
it. I've learned not to count on that.

Bring it back to the chairs. In the closed room the person from the door had
nowhere to sit because the chairs ran out. In Hilbert's hotel they never do. So
the whole argument was about running out of room, all along.

You can run the chairs backwards to see exactly how much room. Take a move that
keeps done states done, settles one new state, and never lands two arrows on one
place. Everybody already in the done room moves to a different done chair. The
newcomer gets a done chair too, and nobody already inside is moving into it,
because that would be two arrows meeting. So everybody already inside got seated
in the done room with at least one chair to spare. With n chairs, that's n people
into n - 1 chairs, which can't be done. So a move like that needs a done room
with no end to it. Give the room any fixed size, and the move merges.

That's Hilbert's front desk run backwards. It's also exactly how Richard Dedekind
defined "infinite" in 1888: a collection is infinite when you can match it
one-to-one with a part of itself that leaves something out. So taking fresh paper
isn't a way out of paying. It's the other way to pay, and only a machine with
endlessly many states can keep paying it.


Cut the strip

Now cut the strip to eight boxes. Same rule: fill the next empty box from the
left, never touch the earlier marks. There are nine possible strips, from empty
to full. Write them down:

  0 marks   00000000   next: 10000000
  1 mark    10000000   next: 11000000
  ...
  7 marks   11111110   next: 11111111
  8 marks   11111111   next: ?

After eight moves the strip is full. What should the ninth move do? Try each
answer.

It stays full: then the strip with seven marks and the full strip both go to the
full strip. Two arrows, one landing. The chairs.

It stops: then it has no next state, and that's the stopping hole from the last
chapter.

It clears the strip: then done went back to not done.

Every answer gives up one of the things the chairs needed. None of them gets past
the chairs.

Keeping the whole history like this is the trick Charles Bennett used in 1973,
when he showed that any computation can be done without two arrows ever meeting,
if you let it keep a copy of everything it did. Rolf Landauer, back in 1961, had
already written that for a machine that runs a program that doesn't stop, the
space to hold every step "cannot be there." Keeping the history is a real way to
pay. It costs a memory that never fills, and every machine you can buy has a
memory that fills.

Bennett wasn't the first there, or the last. Yves Lecerf showed in a short note to
the French Academy of Sciences in 1963 that machines with no merging can imitate
any Turing machine, and hardly anybody noticed. Tommaso Toffoli in 1980, and
Edward Fredkin and Toffoli together in 1982, both then at MIT, built logic gates
and circuits that compute anything and lose nothing, by carrying extra inputs in
and extra outputs out. Their basic gate wasn't new even then: Landauer's own 1961
paper writes one down, calls it reversible and able to do an AND, and doubts
anything like it could be useful. What Toffoli added was the proof that it
computes everything. And Kenichi Morita proved in 1996 that even a tiny machine
with two counters can compute everything with no two arrows ever meeting. Every
one of them keeps what it doesn't forget somewhere: a history, extra outputs, a
counter that codes the past. They all pay in fresh paper.


How long can a finite machine hold off?

One more question, because the 5a and 5b example on page one hinted at it. If
the machine has a few spare done states, can it put off the merge for a while?
Yes, and you can count exactly how long.

At three o'clock a screen says 42. The program is finished. Leave the camera
running. At 3:01 it says 42. At 3:02 it says 42. The screen hasn't changed, but
the box behind it still has a next state every tick. It can stay exactly where
it is, or something inside it can move while the screen stays put: picture a
wheel turning from "first holding position" to "second holding position."

Say the box has K different ways of holding the answer 42. Start one tick
before it finishes, and see how many ticks it can go without two arrows meeting.
Can two of the holding ticks be the exact same state? If they were, follow the
arrows backwards from both, one tick at a time. Since no two arrows meet, being
on the same state now means they were on the same state a tick ago. Keep walking
both back. Eventually the earlier one reaches the tick before it finished, the
state that wasn't done yet, while the later one is still on a done state. A state
that isn't done would have to be the same state as one that is: impossible. So
every holding tick needs its own state, and with K of them, it can last at most K
ticks. Within K + 1 ticks of finishing, two arrows meet.

You can build one that lasts exactly that long: the unfinished state, then K
holding states in a row, the last one stepping to itself. The answer holds for K
ticks with nothing merging, and on the next tick the last two arrows meet. A
bigger memory puts off the merge. It doesn't make it go away.


What's being counted

One thing to keep straight before going on. Whether a move merges depends on what
you count as the state. The endless strip keeps its whole history in the state,
so nothing ever merges; cut it to eight boxes and the same rule merges. Keep a
list of every earlier state alongside the current one, and any machine's moves
become one-to-one, because two different histories never look the same; a later
chapter proves that. Keep only the state one step back, and it isn't enough: two
states that differ only in what came before them still land together.

So "this move merges" is always a fact about a move on a stated set of states.
Every merge in this book is counted on the whole state the machine says it has,
and nothing outside that state is counted.

What I've got now is counting and nothing else: on a finite machine, settling
something for good means two arrows meet. The next chapter is about what I do
with that, and which parts of it are my choice.
