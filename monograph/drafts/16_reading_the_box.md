Reading the box

The last chapter ended on a sentence I didn't follow up: a box is worth turning up because something
later can glance at it and not have to work the thing out again. Every chapter so far kept the box as a
passenger. Chapter twelve said nothing in the bare machine makes a later step read it. Chapter fifteen
asked, as its condition, that nothing in how the rest of the machine moves depends on the cups. Under
that condition, cover the box and you get the ordinary computer back, step for step.

That's a fair way to study what a box costs. It's a strange way to leave it, because it means the machine
pays to settle something and then never uses it. So in this chapter the machine reads its box. Here's what
that buys, what it costs, and how chapter two walks back into the room the moment you try it.


The shortcut

Picture one piece of data, a number that can be changed, and a question to answer about it. There's a long
way to answer: a thousand steps, right every time. There's a shortcut: one step, but right only when the
number has some property, say that it's even. And there's a check for that property, and a box. The box goes
up only right after the check passes, which is chapter eight's established record. Now give the machine one
rule: the shortcut may run only when the box is up.

What happens when the number changes? The box was about the old number. So give the number an edition: every
write moves it to the next edition, and the box is about one edition, the one that was checked. The shortcut may
run only when the box for the current edition is up.

From a clean start, does the shortcut ever give a wrong answer? Walk it. The shortcut runs, so the box for the
current edition is up. That box went up only right after a check passed on that edition. Nothing has written to
the number since, because any write would have moved it to a new edition. So the number is the one that passed,
the property still holds, and the shortcut is right. That's chapter eight's four conditions, doing a job: same
property, same thing, same edition, honest check.

And look at what it does to covering the box. Cover it with your hand and you no longer get the same run step for
step, because the machine with the box takes the one-step road where the machine without it takes the thousand-step
one. You get the same answers, by a different number of steps. So this isn't chapter fifteen's machine. The box has
stopped being a passenger.

It computes nothing new. Every answer it gives, the long way gives too. What it saves is steps, the way a cache saves
them, and caches are old. What I want to show you is what keeping the shortcut honest costs, because it's chapter two's
bill again, in four different currencies.


Four doors

The weak spot is the edition. It's a counter, and on a finite machine a counter can't climb forever. So what do you do?
There are four doors, and I'll walk through each one with the machine that walks through it, the way chapter three did.

The first door: let the editions wrap around. Say there are two editions, 0 and 1, and after 1 comes 0 again. Four moves
are enough to break it. Check the number 0: it's even, so the box for edition 0 goes up. Write 1: edition 1. Write 3:
edition 0 again. Now ask. The box for edition 0 is still up, so the shortcut runs on 3, which is odd, and gives the wrong
answer. The box was about the first edition 0, and the shortcut is looking at the second. That's chapter twelve's coin
that moved, with a bad coin. And it's chapter eleven's lesson too: a counter that goes back down gets leaned on at exactly
the place where it goes down.

Programmers know this one. IBM's manual for its System/370 computers, in the edition of 1974 as revised in 1975, warns about it in a
note on an instruction called Compare Double and Swap. One program reads the head of a list; meanwhile another program "removes the
first two messages and then adds the first message back into the chain," and the first program, on continuing, "is not aware that the
list is changed." The fix in the note is a change number in the word next door, "incremented for each modification of the list," which
brings the risk down "to a negligible level": it can go wrong only if the first program is held up while a whole multiple of 2 to the 32nd
changes go by. That's the first door with a very big wheel. R. Kent Treiber, at IBM, drew the same accident in a 1986 report and fixed it
with what he called an allocation counter. The name came later. The earliest I can find is Maged Michael and Michael Scott's, in reports
dated December 1995 and their 1996 paper: "the ABA problem," a value that goes from A to B and back to A, so a check that only looks at the
value is fooled.

The second door: never reuse an edition. Each edition gets its own box, and a write moves to an edition that's never been
used. Every box stays up for good, so this is still a Thiele machine, and the shortcut is never wrong. But it pays in chapter
two's second column: fresh paper, a new edition on every write. On a finite machine that's a budget. Once the editions run
out, the honest move is a mark that goes up for good and says "spent," and from then on the machine takes the long way. That's
chapter eighteen's bank of fuses, one blown per update, with a design rule to make sure there are enough.

The third door: keep one box and knock it down on every write. That's a cache with an invalidate, and the shortcut is never
wrong. But the box comes down, so it isn't a Thiele record any more; it's chapter fourteen's toggle. And it doesn't get out of
chapter two either. Make the write as gentle as you like, even one that just flips the number between 0 and 1, which on the
number alone is one-to-one. Knocking the box down still sends the number with its box up and the same number with its box down
to the same place: two arrows meet. That's chapter six's WIPE. And the passing check that put the box up merged two states too:
the number with its box down and the same number with its box already up both land on box up. The toggle pays twice.

The fourth door: don't tie the box to the edition at all. Tie it to the value that was checked. "6 is even" never goes stale.
Write a different number, and the box for 6 is still true, because it's about 6, not about whatever's in the slot. Come back to
6 later and the box is waiting. No editions, nothing wraps, nothing gets knocked down, and every box stays up for good, so it's
a Thiele machine and the shortcut is never wrong. It pays in room: one box for every different value that ever passed. That's
chapter twenty-one's count. When the values are few, it's few boxes.

This door has an inventor. Donald Michie, at the University of Edinburgh, wrote in Nature in April 1968 about what he called memo
functions. Give a function two parts, he said, a "rule part," the procedure that works the answer out, and a "rote part," a look-up table,
and let the machine use whichever suits the moment, so that "each evaluation by rule adds a fresh entry to the rote." The word programmers
use now, memoization, grew out of his; it isn't in the paper. His rote is a box tied to the value: once an input has been worked out, it
never needs working out again.


Running all four

I ran all four on the same twenty thousand programs, forty moves each, on a number from 0 to 5, with the long way at a thousand
steps and the shortcut at one. The doors that never reuse an edition get four editions to spend, the same room the first door
wraps around in.

  [table: the four doors]

The first door is the fastest, and it's fast because it's wrong. The other three are never wrong. On these small numbers the
fourth door saves the most, and never needed more than three boxes, because only 0, 2 and 4 are even.


Why the other doors exist

If the fourth door is that good, why doesn't everyone always tie the box to the value? Ask chapter eight's warehouse question. In
the run above, the data is one small number, and finding its box takes one look. Make the data chapter eight's list of a thousand
numbers. A box tied to the value of the whole list can only be found by reading the whole list, to know which list you're holding.
Reading a thousand numbers takes about as long as checking whether they're sorted, which was the check you wanted to skip.

So on big data the fourth door has three ways forward, and each one is a bill you've already seen. Tie the box to a short fingerprint
of the list instead, and two different lists can share a fingerprint and a box; that's chapter eighteen's wall, scrambling functions
that make that hard but not impossible, and when it happens it's the first door's wrong answer again. Or never change a list at all:
keep exactly one copy of each different list and hand around a pointer to it, so the box can sit on the pointer and be found in one
glance; that's fresh memory for every new list. Or go back to the second or third door, put the box on the container instead of the
value, and let a write move the edition or knock the box down, so a later step can find it in one glance.

Keeping one copy of each value is old too. Andrei Ershov, in a paper printed in Russian in 1958 and translated into English the same
year in the first volume of the Communications of the ACM, gave a program that writes programs a way never to work out the same expression
twice. It scrambled each instruction into a number that said where to look, checked whether that place already held the same instruction,
and reused it if so, in time that grows with the number of instructions instead of its square. Donald Knuth credits him, along with Gene
Amdahl, as an independent discoverer of that kind of table. In 1974 Eiichi Goto, at the University of Tokyo, built the idea into a version
of Lisp, from a proposal he'd made with three colleagues the year before, and called it monocopy: no two copies of the same structure, so
that checking whether two are equal becomes checking whether they're the same one. (This is Andrei Ershov, the programmer. The Ershov whose
ladder came up in chapter fourteen is Yuri, a logician.)


What the doors say

Every time a box goes up, it pays the toll, because on a finite machine that's two arrows meeting, and that's chapter two and chapter three.
That part was already in the book. What this chapter adds is the second bill. Keeping a shortcut honest after the data changes costs one more
thing, and there are exactly four ways to pay it: fresh editions, which is fresh paper or a fuse budget; a box that comes down, which leaves the
definition and merges at the wipe; room for every value checked; or nothing, and wrong answers.

Programmers have used all four for decades. What this chapter adds is that they're four ways of paying chapter two's bill, and that under two
conditions there's no fifth. Here's the proof.

Say what the guard is allowed to see. The first condition: its glance can't tell a passing value from a failing one. If it can, then either it's
doing the check over again, which is no shortcut, or it's reading enough of the value to tie a box to it, which is the fourth door, with its bill of
room and, on big data, the time it takes to read the value. The second condition: the memory the guard reads is made only of boxes that go up and
never come down. If some of it can come back down, that's the third door.

Under those two conditions, run the same moves over and over: write a passing value, check it, ask; then write a failing value, and ask again. The
glance can't tell the two values apart, so whether the shortcut is unlocked depends only on the boxes. If it's unlocked after the failing write, it
answers wrong: the first door. Say it never answers wrong. Then every round that unlocks needs the boxes in an unlocked state after the check and in
a locked state after the failing write, so the boxes change between those two moments, and they have to change again before the next round can unlock.
A number of unlocked rounds needs at least twice that many changes, less one. But boxes only go up. With E boxes, they can change at most E times in
the whole run, because each change raises at least one box and none ever comes back. So twice the number of unlocked rounds is at most E plus one.
After that the shortcut never unlocks again, and the machine takes the long way for good: a budget, the second door. It's chapter two's chairs once
more, more changes needed than boxes to spend them on.

The fourth door's room is a count of its own. Say every value that's been checked has to stay unlocked, all at once, through any writes. Take two
different sets of checked values. Some value is in one set and not the other, and the guard has to unlock it for one and not for the other, so the
memory has to be in two different states. With k passing values there are 2 to the k sets, so the memory needs 2 to the k states: k boxes, one for
each value.

So under the two conditions, wrong answers or a budget are the only outcomes, and stepping outside the conditions is stepping through one of the other
two doors.

And it leaves one question hanging, the one every machine with a record runs into once its programs can be handed their own code. These shortcuts
were handed to the machine: I wrote the property, the check and the shortcut. Can a machine find its own shortcuts, and decide from the inside whether
one is sound? That question runs into a wall, the same wall Kurt Gödel and Alan Turing hit, and
I have to show you the wall is there before anything pretends to be on the other side of it. That's the next chapter.
