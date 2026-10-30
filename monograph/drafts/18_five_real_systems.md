Five real systems

So far there's been a toll, a counter, two kinds of wall and a cup, every one of them
shown on paper, with cups and cards and dice I made up. It's time to go look at what
people actually do. I picked five systems that keep records other people rely on, with
real money or real security behind them, and asked each one the question from the
paper: is there a price on the moment the record is written? Not on the work around it.
On the write itself, the moment the mark goes on and stays.

I'll give you the answer first, because it's one sentence and it surprised me. Of the
five, read through the pieces of them I copied out, one takes a fee at the moment of the
write, and that one leaks at exactly the place chapter eleven said a counter leaks: where
it goes back down.

"Price" needs one meaning for all five, or the answer is whatever I want it to be. So
here it is, fixed before looking. A system prices an event if it attaches one of three
costs to it. A fee: something taken at the event itself, whatever happens afterwards. A
bond: something put at risk by the event and lost only if some later event happens, like
a contradiction. A budget: a limited allowance the event draws down, so only so many such
events can ever happen. A wall isn't a price under this. Nobody pays a scrambling function;
undoing one is just too hard. Neither is work a system needs and never charges for. The
table at the end has a column for each of the three, and because the definition came
first, what the table shows is a finding about the five, not something I arranged.

Three things are easy to blur here, so I'll keep them apart all the way through. There's
the real system: the document that real money and real security run on. There's my copy:
one piece of that document, copied out small enough to check by hand. And for some of the
five there's a wrapper: a tiny model that takes one condition as given and says what
follows. A claim checked at one level isn't a claim about the level above it. Near the end
of the gas section I'll walk gas through all three, so you can see where each claim stops.


Proof-of-stake finality: the price is on going back

Ethereum, and chains like it, decide which blocks are final by having validators, people
who've locked up money, their stake, vote on checkpoints: blocks picked out at regular
numbered rounds, which they call epochs. A vote isn't for one checkpoint. It's a link from
a checkpoint the validator already trusts to a later one, and every chain starts from one
first block, the genesis block, which counts as trusted from the start. In the design
Vitalik Buterin and Virgil Griffith published in 2017, called Casper, a checkpoint is
justified when validators holding two thirds of the stake vote a link to it from a
justified one, and final when it's justified and a two-thirds link runs from it to its
direct child. The record is "this checkpoint is final."

Two rules carry the price. Don't vote for two different targets in the same round. And
don't cast a vote whose span, from where it starts to where it lands, surrounds the span of
another of your votes. Break either, and your deposit can be destroyed, which is called
slashing. The theorem they prove, which they call accountable safety, says: if two
checkpoints that contradict each other ever both become final, at least a third of the
stake broke a rule and can be slashed. So the price is on going back, on making the record
contradict itself. Writing the record, voting honestly to finalize, costs no stake at all.
That isn't a claim that running a validator is free; it's a claim about what the deposit
is taken for. In the terms above, Casper's price is a bond. The deposit stands behind every
vote, the honest ones included, and it's only taken from a validator whose own votes
contradict each other.

Do it with three validators of equal stake. Draw the genesis block at round 0, two competing
blocks at round 1, and one child of each at round 2. Let A and B vote both links on the left
branch, genesis to its first block and that block to the next. Let B and C vote both links on
the right.

  [figure: genesis, two branches, A B on the left links, B C on the right links]

Each link has two of the three votes, two thirds of the stake. Both round-1 blocks are
justified and each has a justified link to its child, so both are final, and they're
siblings, so neither is an ancestor of the other. B voted for two different targets in round
1, so B's third of the stake can be slashed. A and C each voted one link landing in round 1
and one landing in round 2, which neither doubles nor surrounds, so they broke no rule. The
picture records votes; nothing in it takes anybody's money. What it shows is that the
theorem's condition can actually happen: forks like that can be built, and the theorem fires
on them.

Why does the theorem hold? Walk it. Say two contradicting checkpoints are both final, one in
round v and the other in round w.

If v and w are the same round, then two groups, each with two thirds of the stake, voted links
landing in that round on two different blocks. Two thirds plus two thirds is four thirds, more
than everything, so the two groups share at least a third. Every validator in that shared part
voted two different targets in one round.

If they're different rounds, say v is earlier, look at how the later one got justified: a chain
of two-thirds links climbing from genesis, every block on it an ancestor of the later checkpoint.
None of those blocks is the earlier final checkpoint or comes after it, because then the later
checkpoint would too, and they contradict. So that chain has to get past round v without touching
the earlier checkpoint, and some link in it starts at or before v and lands after v. Three ways
that can go. It lands at exactly v plus one: then it and the earlier checkpoint's finalizing link
land in the same round on different blocks, and the shared third voted both, a double vote. It
starts at exactly v: then its starting block is a justified block at round v that isn't the
earlier checkpoint, and the two links that justified those two blocks land in round v on different
blocks, a double vote again. Otherwise it starts before v and lands after v plus one, so it
surrounds the earlier checkpoint's finalizing link, which runs from v to v plus one, and the shared
third made a surround vote. In every case a third of the stake broke a rule.

Everything there stands on the overlap. Take away "two groups of two thirds share a third," and the
argument promises nothing.

The piece I copied out comes from a published proof by Runtime Verification and the University of
Texas at Austin, based on Yoichi Hirai's, with that overlap taken as a condition: the copy takes it as
given and doesn't do the arithmetic. It has no deposits, no rewards, and no rule for picking which
branch to build on. On a chain with one validator, one vote finalizes the genesis block and nobody is
slashed: that's "writing costs no stake," shown in the simplest case there is.

One thing that means for the record itself: finality can be undone at a price, the price is named, and
a final block can still hold a false statement.

Is the 2017 design what Ethereum actually runs? Partly, and the paper's title is the clue: Casper the
Friendly Finality Gadget. Its first sentence says it's a finality system laid over a chain still choosing
its blocks by proof of work, so it's a gadget, bolted on top. In 2020 a larger group, Buterin among them,
wrote up Gasper, joining Casper's finality to a rule for picking branches called LMD GHOST, and on 15
September 2022, in the switch people called the Merge, Ethereum stopped choosing blocks by proof of work at
all and went over to proof of stake. So the checkpoints and the two slashing rules are one part of a system
that holds real money today, and my copy is of that part's safety argument, the way the 2017 design states
it. Everything between the two, the branch rule and the rest of the running protocol, is the gap between my
copy and the running system. None of it moves the price: finalizing still costs an honest validator no
stake, and what costs is contradicting yourself.


Gas: the one that charges a fee at the write

Every operation on Ethereum costs gas, paid in ether by whoever sent the transaction. The yellow paper,
Ethereum's formal specification, gives the reason in one line: every computation costs a fee, so the
network can't be abused and questions about whether a program stops are sidestepped. The record I care
about is a storage slot holding something other than zero, which every full copy of the chain in the
world has to keep until it's cleared. Clearing a slot is allowed, and the refunds below exist to reward
it.

Writing a fresh slot from zero to something costs twenty thousand gas, by the table in the yellow paper's
appendix, plus twenty-one hundred for touching a cold slot, one the transaction hasn't touched yet. After
the first touch it's warm. The point, as I read it, is to discourage storage growth, since storage grows
every copy's database. That charge is a fee on the write, at the moment of the write, and it's the only fee
in the five. Gas has a budget too: every block has a gas limit, and the gas its transactions use can't go
over it, so only so many writes fit in a block.

Where does a number like twenty-one hundred come from? Somebody picked it, so the next question is who, and
why, and the answer has a date on it. In September 2016, just as Ethereum's developers were gathering in
Shanghai for Devcon 2, their developer conference (the third one, since they started counting at zero),
attackers started filling blocks with an operation that was cheap in gas and expensive in fact: it sent every
copy of the chain off to read data from its disk, and copies fell behind. The first repair, a change that
October called Tangerine Whistle, raised the prices of the operations the attack leaned on. The cold-slot
charge came later, in a proposal by Vitalik Buterin and Martin Swende called EIP-2929, switched on in the
Berlin upgrade of April 2021, and the reason it gives is still those 2016 attacks. So twenty-one hundred
isn't a law of nature or a measurement of anything deep. It's a scar: a price set after somebody found where
the old price was wrong. That doesn't change the argument; the write is still priced at the moment of the
write. It does change how I read the rest of that table. Some of its numbers, at least, are somebody's answer
to "what did this cost us last time," which is a record of a different kind.

Now the leak, which is chapter eleven's leak. Set a slot and clear it again in the same transaction, and you
get a refund. Count it through. The first write costs twenty-two thousand one hundred. Clearing it costs a
hundred and credits a refund of nineteen thousand nine hundred. Net: twenty-three hundred. Leave it set, and
you pay at least twenty thousand. So the write is priced, and the write you take back nearly isn't.

Twenty-three hundred on its own misleads, though, because of the 2021 change from chapter eleven, the one that
ended the refund-hoarding token's advantage: the refund a transaction actually gets is capped at a fifth of all
the gas it used, and that includes the twenty-one thousand every transaction pays just for existing. Take a
transaction that does nothing but set and clear the slot. Count only that base and the two stores (the steps
that load their arguments add about a dozen more): it uses 43,200 gas, so the cap is 8,640, so it pays 34,560.
That's 13,560 on top of the base. Look at the slot alone and forget the base, which the rule doesn't do, and
you'd get 17,760. Either way it's far above twenty-three hundred.

You can check the twenty-thousand floor with a pencil. My copy follows the specification's rule for one slot in
one transaction, starting from zero: a store of something that isn't zero into a slot that's still zero costs
twenty thousand; any other store costs a hundred; and putting the slot back to zero gives back nineteen thousand
nine hundred. Keep two lines on a sheet. "Slot at zero: net so far at least zero." "Slot not at zero: net so far
at least twenty thousand." The fresh slot meets the first line. Now check that every store keeps whichever line
fits where it lands. Zero to zero adds a hundred: still at least zero. Zero to something adds twenty thousand: from
at least zero to at least twenty thousand. Something to something else adds a hundred: still at least twenty
thousand. Something back to zero adds a hundred and takes off nineteen thousand nine hundred, nineteen thousand
eight hundred off in all: from at least twenty thousand down to at least two hundred, still at least zero. So
whatever the list of stores, if the slot ends up holding something, the net is at least twenty thousand. The cold
charge comes once, on the first store, and nothing after it depends on it, so from a cold slot it's at least
twenty-two thousand one hundred.

That copy covers one slot in one transaction, with the gas and refund arithmetic copied out of Ethereum's execution
specification. It has no other slots, no calls between programs, and no refund cap.

The wrapper is a different kind of thing. It's a gas schedule in the abstract: any states, any steps, a cost on each
step, a box that's up or down, and a rule saying which steps get charged. There's no Ethereum in it at all. It's
chapter seven's clerk under a new name. Ask a schedule for two things: every run pays at least as much as the number
of times it turned the box up, and no run pays more than that. Both together hold exactly when the schedule charges one
on each step that turns the box up and nothing on any other. Both halves are easy to see on a one-step run. Leave one
step that turns the box up uncharged, and that one-step run turns it up for free: the first fails. Charge one step that
doesn't turn it up, and that one-step run pays more than the nothing it turned up: the second fails.

So walk gas through all three. Think of Ethereum as it runs as a kitchen, and my copy as a photocopy of one recipe from
it. The photocopy says a set-then-clear nets twenty-three hundred, and inside the photocopy that's right. In the kitchen,
the bill for that transaction is 34,560, because the kitchen has a base charge and a cap the photocopy doesn't. The wrapper
isn't from that kitchen at all: it says what an exact price would have to look like, one per raise, and Ethereum's twenty
thousand isn't that and isn't trying to be. A claim made with the photocopy in hand is a claim about the photocopy.

Gas prices storage and computation. It says nothing about whether what's stored is true.


Attestation: a quote about the past

A lot of computers carry a small security chip, a trusted platform module. It keeps registers that can only be extended:
each new measurement gets scrambled together with the old value. A quote is the chip signing some of those registers along
with a challenge from whoever's asking, so they can tell it's fresh, and the asker still has to check the signature, the
challenge and the values they expected. That can give you a fresh report of what was measured. It doesn't tell you every
important fact about the machine got measured.

Some of those registers can be reset, depending on the register and the rules of the platform. Some reset at startup; some
allow resets partway through. So "you can only extend" describes a stretch of time with those resets left out, and a claim
about an unbroken history has to say which resets it allows. Intel's SGX enclaves use their own measurements and reports for
a similar purpose, but not these registers.

What does the specification price on the registers? Nothing: no fee, no bond, no budget. Forging a different measurement
history that passes depends on breaking the scrambling or the trusted parts, which is a wall, not a price. An allowed reset is
a separate thing, not an attack. That's the difference between expensive and impossible in practice, and it's easy to blur,
which is why the definition at the start of this chapter leaves walls out.

So what stands behind a cost can come in three currencies. It can be money, a fee or a deposit the system takes: Casper and gas
are there. It can be a wall, going back made too hard by something nobody knows how to undo, with no exact price on it:
attestation and transparency are there. Or it can be physical, energy spent or hardware worn, which none of these five charges as
a fee or a bond; the nearest is the chip's write budget, below.

Why the registers, then, when something that lasts would make a better record? Because the quote is what a faraway asker reads,
and the registers are what it signs. The same chip has longer-lasting records, closer to the cup than anything else in this
chapter. Version 2.0 of its specification has slots of a kind it calls a bit field, changed only by a command that ORs new bits
into the old value: while that slot exists, it can set a bit and can't clear one. Deleting a slot and making it again is governed
by separate permissions, and any claim about how long the record lasts has to include them. The chip also has counters that only go
up, and a new counter starts above every count the chip has held before, so deleting one and making a new one doesn't start over at
zero. That's a promise about this chip, not about somebody swapping in another chip.

Those slots are rationed. Bryan Parno and his coauthors, building a system called Memoir in 2011, noted that the specification of
the day only required a counter to be able to tick once every five seconds, and that the chip's storage was expected to survive about
a hundred thousand writes in its whole life, so writing once a second would wear it out in under twenty-eight hours. Memoir writes to
it twice per startup. That's an expected lifetime, not a budget the protocol enforces, and the quoted registers have no number like it
at all. But on the bit field it's chapter five's row of cups, which can only turn up as many times as there are cups. Phones and small
controllers go one floor further down, to fuses like Chow's in chapter fourteen: a version number kept as a row of fuses, one more blown
at each security update, and startup code that refuses anything older. A 2021 guide by Rob Smart for PSA Certified, a security
certification scheme for chips and devices, tells designers to make sure there are enough fuses to last the number of updates expected
over the supported life of the chip's root of trust, the part every later check starts from. That's chapter five's count of cups, written as a design rule.

What it's all for is rollback. Memoir's example is a password checker put back to an old saved state to undo a user's password change.
In 2017 a system called ROTE did the same job for Intel's enclaves by having several machines vouch for each other's counters, and its
authors say the only way left to break it is to reset every one of them to its start. In 2016 Raoul Strackx and Frank Piessens's Ariadne
got the job down to flipping one bit of lasting memory per update, which they call the lowest possible. Notice who the attacker is in
every one of these: whoever gets to put an old state back. Not a bad program. A record kept by the step can't see that attacker. Everything
an established record guarantees about its history is stated from a clean start. Put back a state the machine really reached, and every
guarantee still holds of it, through the run that reached it first. None of them can say nothing came after it. The toll on each step still
holds after a restore; it just can't tell you what happened before.

Systems run as several copies put the same kind of record somewhere else: inside each copy, where a copy that's been taken over still can't
make it say two different things. Byung-Gon Chun and his coauthors built a log a copy can only add to, called A2M, in 2007. Dave Levin and
his coauthors shrank that to a trusted counter, TrInc, in 2009. MinBFT, from Giuliana Veronese and her coauthors in 2013, uses a trusted
counter to agree with 2f + 1 copies when f of them can lie, where the usual count is 3f + 1. Damysus, from Jérémie Decouchant, David
Kozhaya, Vincent Rahli and Jiangshan Yu in 2022, has a small trusted service it calls the Checker, which keeps a count of where the
protocol is that only goes up. And Allen Clement, Flavio Junqueira, Aniket Kate and Rodrigo Rodrigues worked out in 2012, with proofs,
what such a record buys, and as I read their result it's a good warning for this book. On its own, stopping a copy from saying two
different things doesn't lower the 3f + 1 at all when messages can be slow. Add signatures a third party can check, and it turns a system
that survives crashes into one that survives liars, with no extra copies. The way I read it, a record helps the others only as far as they
can check what it says. That's chapter seven from the other side.

Under those three currencies there's a fourth, and every permanent record on a finite chip pays in it: the chairs from chapter two. Here's
how. Forgetting by itself doesn't pick out a record write; any step that overwrites a field that could hold two things forgets something.
What picks it out is where the forgetting lands. Count the states where the record already reads yes, and call that number K. Take a step
that never turns the record off anywhere, and turns it on at one state that read no. That step sends each of the K yes-states to a yes-state,
and it sends the one no-state to a yes-state too. That's K plus one starting places and only K yes-states to land on, so two of them land
together. Both came from the yes side or from the one it just raised. So what a permanent write destroys is a distinction on the record's own
yes side: two states it already vouched for, or the one it just raised and one that was up already. Any overwrite merges something somewhere.
A permanent write has to merge it there. That needs no assumption about money, keys or heat. The other three each need an assumption of their
own: a fee rule, a wall nobody can climb, a law of physics.

What the quote can do is say what was measured. It can't say the measured code is correct, and it can't say anything about what was never
folded in. A correctly measured buggy program gets a beautiful quote. Try it with the smallest pair there is: two machines with nothing
measured at all, one with some running flag up and one with it down. Their registers are the same, so their quotes are the same, and
anything that reads only the quote has to give them the same answer. No reader of the quote can recover the flag. That's chapter seven's
window again. Anything that depends only on what was measured, the quote can answer; that's what it's for. And a "sign and check" interface
by itself promises nothing: a check that always says yes fits the interface perfectly and accepts a signature no key ever made. The protection
has to come from the scrambling and the keys, which is a further assumption.

That limit, turned outward, is the honest edge of chapter eight's four conditions. Every one of them is about a thing the machine holds: same
property, same thing, same edition, honest check. For a claim about the world, the oven is hot, the parcel arrived, there's no edition the
machine controls. Whatever reads the world is a window onto it, and "nothing changed between the check and the commit" stops being something a
step can enforce and becomes an assumption about the sensor. So a record can establish claims about the machine's own state, and claims about the
world only through stated assumptions about whatever measured them. A correctly recorded sensor reading establishes what the sensor reported.
Whether the oven was hot still depends on the sensor and on how its report connects to the world.


Certificate transparency: visible, unpriced

The certificates that put the padlock in your browser are issued by hundreds of authorities, and a bad or broken one can issue a certificate for
a site it shouldn't. Certificate Transparency puts certificates in public logs you can only add to, built as trees of scrambled values. It was
written up as RFC 6962 in 2013 and revised as RFC 9162 in 2021. I went looking for which one the running logs follow, and it's still 6962:
Mozilla's reference for web developers says browsers are built to it, and as late as November 2025 Chrome's team was only proposing to drop its
rule that every certificate carry a timestamp from at least one 6962 log. My copy is of 9162.

The tree is chapter four's chained running total, folded into a tree: Ralph Merkle's tree from the same chapter. Scramble each certificate; those
are the leaves. Scramble the leaves together in pairs, then those in pairs, and so on, up to one value at the top, the root. To prove one leaf is
in, the log hands you only the few values sitting beside the climb from that leaf to the root, and you redo the climb yourself. A second check
shows that a bigger tree is a smaller one with leaves added on the end and nothing rewritten. The record is a leaf in the tree.

That kind of tree has a history of its own. The computer scientists Scott Crosby and Dan Wallach, at Rice University, built logs you can't quietly
change on the same kind of tree in 2009, with a proof that an entry is in the log and a proof that a later version extends an earlier one, each only
a handful of values long even for a huge log. A rewrite that doesn't extend a root somebody already saw gets caught by the second check.

Do the climb by hand. Lay out seven cards, d0 through d6. Join neighbours with paper brackets: a joins d0 and d1, b joins d2 and d3, c joins d4 and
d5. d6 stands alone. Then L joins a and b, and R joins c and d6. The root joins L and R.

  [table: the inclusion climb for d3]

To check d3, you only need three cards: d2, a and R. Join d2 on the left of d3 and you've rebuilt b. Join a on the left of that and you've rebuilt
L. Join R on the right and you've rebuilt the root. You never opened a or R. Swap left and right anywhere, though, and the bracket changes: the proof
has to carry the order as well as the cards. The same seven cards check every other leaf too. d0 needs d1, b and R, all on the right. d4 needs d5 and
d6 on the right and then L on the left. d6, standing alone, needs only c and then L, both on the left.

Now the second check. Say you saw the tree when it had four cards, and its root was L. Now it has seven. The log hands you one card, R. Put L on the
left of R and you get the new root. So the old tree is the left half of the new one, untouched, and only cards were added on the end.

My brackets are brackets, not numbers, so what you just checked is how the tree is put together. A real log uses short scrambled values, and "two
different trees can't give the same root" is then a separate promise, from the wall.

What does the RFC price? Nothing. It says in its first section that logs let people detect a bad certificate afterwards. They don't prevent one. And
a log that shows different trees to different people can beat the checking, so logs are still trusted parties. What it buys is visibility.

So why does any authority bother logging? Nothing in the RFC makes it. A browser does. Chrome's team set the rule, enforced from Chrome 68 in July
2018, that every certificate issued after 30 April 2018 had to meet its transparency policy, and a publicly trusted certificate that doesn't simply
isn't trusted by Chrome: the visitor gets a full-page warning in front of the site. So there is a price after all, though it isn't in the
specification. It lives in one company's browser, and it's the price of being shown to that browser's users at all. Which means the strongest lever on
this record is a policy one company can change, and that's a fact about who holds the stamp, not about the tree. It changes nothing in the table, which
asks what each specification prices. But keep two sentences apart: "the specification prices nothing" and "nothing is priced."


Proof-carrying code: no toll required

George Necula's idea, from chapter twelve, is to send untrusted code with a proof that it follows the receiving computer's rules; the receiving computer
works out what would have to be true and checks the proof with a small checker before running anything. The record is the checked proof, or the result
of checking it, and a computer may keep either. Nothing in the idea requires a permanent box, or charges anything for accepting. Producing and checking
the proof both take work, and nothing here makes that work the toll.


The same question, five ways

Lay them out by the one definition of price from the start. Casper puts a bond behind the write and takes it on going back. Gas takes a fee at the write,
mostly refunds it if you take the write back, up to a cap, and rations writes with a gas limit per block. The chip's quoted registers have no fee and no
budget; its separate bit fields have only so many bits to set, which isn't a quota on everything the chip does. Transparency charges nothing at the write;
what it gives is that a bad certificate can be seen afterwards. Proof-carrying code requires neither a toll nor keeping anything.

  [table: the five systems by fee, bond and budget]

The first four rows come with a piece copied out and checked; the fifth is a comparison of ideas. Each copy shows only what it shows. To read a row as a
claim about the running system you'd need evidence from that system.

So the thing the toll charges for, the moment the record is written, gets a fee in one of the five, and in that one the designers had to patch the place
where the charge could be clawed back. I don't find that a win or a loss. It's a fact about what people built, and what they built was mostly walls and
penalties for contradicting yourself. A toll on the write was rare. Whether a toll is a better design than a wall is something I can't prove, and I won't
pretend the five say so. Because the definition came first, that last part is a count: of the fifteen fee, bond and budget squares in the table, three are
filled, one of each kind, and only gas takes a payment at the moment of the write.

What I read in them, and it's a reading of five cases I chose, is that each one has something it treats as the record, they last for different lengths
of time, and they all picked something different: final, committed, measured, logged, checked. Is there anything that picks out one event as the one worth
recording, or is it a free choice every time? That's the next chapter.
