Heat

Every price in this book so far is one I wrote down. Chapter one said it had nothing to say
about heat, and chapter three promised heat its own chapter, with the people who doubt it
named, and promised that Landauer's heat would turn out to be owed only for what you didn't
know. This is that chapter. Everything in it is either counting, which I'll do with you, or
physics, which I'll name and source and leave as physics. I'll keep saying which is which.


The stamp at zero

Start where chapter three left one door open. Take a sheet of paper whose reading is just BLANK
or STAMPED, and one move: stamp it if it's blank, leave it alone if it's already stamped. It's
finite, two readings. It's permanent: STAMPED stays STAMPED. And it settles something, because
BLANK goes to STAMPED. Both readings land on STAMPED, so two arrows meet. The paper's fibres, the
ink and your memory aren't in this two-state picture; the merge is a loss from the reading, not
the disappearance of every trace.

Now set the price of that move to zero. The toll fails, and you can watch it fail: the box went up
for nothing. Nothing in counting stops you from doing that. A price of one satisfies everything
chapter three asked for, so the asks can hold together; whether they must is a different question,
and only a claim about the world can answer it. The nearest such claim is Rolf Landauer's.

I have to be exact about the gap between his claim and mine. Bennett's rule, as I wrote it, charges
every move where two arrows meet, whether or not you already knew which state you were in. Landauer's
heat, as this chapter will show, is owed only for what you didn't know. My rule is the worst case on
purpose: a move that has to work whatever it's handed pays for the worst it could do. And it keeps only
a yes-or-no question, whether any pair can meet. The one-bit reset is where it comes from, and it doesn't
measure the heat of any particular preparation.


What Landauer said

Here's what Landauer said, in 1961, as exactly as I can put it. I went past the summaries and read the
paper itself. A logical operation with no single-valued inverse, a step that forgets, in this book's
words, must give off heat, "typically of the order of kT" per operation, where k is Boltzmann's constant
from chapter three and T is the temperature. For the specific case of resetting one bit whose value you
don't know, the minimum is kT times the natural log of 2, about 0.69 kT.

I want you to hear two things in that. First, "of the order of": he wasn't handing out a number to three
decimals. Second, and this surprised me, he didn't measure anything. The paper is argument, with models.
He writes that he can "show, or at least very strongly suggest" the conclusion, and that his reasoning
gives "no guarantee that this minimum is in fact achievable." That's the founding paper of the whole
subject, and it's a careful man saying "I think this is right and here's why." I like him more for it.

Was it measured, eventually? Yes, and only recently. In 2012 a group at the École Normale Supérieure in
Lyon, Antoine Bérut and Sergio Ciliberto's lab working with Eric Lutz, trapped a single glass bead, two
millionths of a metre across, in a double well made of laser light, and used the two wells as the two
values of a bit. Then they erased the bit, by lowering the barrier, tilting the trap and raising it again,
many times over, slower and slower, and measured the heat each time. The average heat came down toward
Landauer's kT ln 2 as the erasure got slower, closer the slower it went, and never under it, on average.
Single runs went under it; the bound is about the average, and any one erasure can beat it. And if you
only succeed in erasing half the time, the floor drops to zero, which the paper's formula shows and which
I think is the most honest line in it.

Others have done it since with different devices. Yonggun Jun, Momčilo Gavrilov and John Bechhoefer did it
in 2014 with a bead in a feedback trap, and ran the same moves with no tilt as a control. Jeongmin Hong,
Brian Lambson, Scott Dhuey and Jeffrey Bokor did it in 2016 with tiny magnetic memory bits. Rocco Gaudenzi
and his coauthors did it in 2018 with the spins of molecules at one kelvin. The table near the end of this
chapter has their numbers. So it was predicted in 1961 by argument, and seen in a laboratory fifty-one years
later.


Who doubts it

Is it settled? No, and I'd be lying by leaving that out, because the people who doubt it aren't cranks. John
Norton, a philosopher of physics at Pittsburgh, has argued since 2005 that the usual proofs of the principle
quietly assume what they're trying to prove, and that the kinds of process they assume, put together, could be
made to break the very law the principle is supposed to guard. An earlier objection, made in 1998 and 1999 by
Norton and his Pittsburgh colleague John Earman, also a philosopher of physics, was that the principle can't be
independent of the second law. Charles Bennett, who did more than anyone to build the subject, rated that one
"in my opinion the one of greatest merit," and then disagreed with it. Others replied to Norton; Norton replied
back. Owen Maroney, a philosopher of physics who works on exactly this, wrote the Stanford Encyclopedia of
Philosophy's entry on it in 2009, and it ends without a verdict. I've read what I could of both sides, I'm not
qualified to referee them, and I'm not going to pretend the laboratory settles a question about what the
principle means in general, because measuring one bead doesn't do that.

So here's what I did with it, and I think it's the only honest thing to do. The charge on forgetting is written
into this book as an assumption with a name. Nowhere is it proved as a general fact, because it can't be proved
from counting. For a particular machine with a particular price list you can see it hold, the stamp at cost one,
and that's a different thing. If Norton turns out to be right, every argument in this book still holds; they just
have one assumption fewer that the world agrees to. If Landauer's side turns out to be right, it backs a heat
price under its conditions, and the whole-number charge on every merging move is still my bookkeeping rule. Either
way nothing here says a device does anything until somebody measures the device.

Naming an assumption isn't the same as leaving it unplaced, though, and a hedge isn't a position, so I'll give mine.
Earman and Norton's objection is a fork, set out in the first part of their paper, in 1998. Either an information-based answer to Maxwell's demon assumes the second law,
which they call the sound horn, and then it adds nothing the second law didn't already give; or it rests on a new
principle tying information to entropy, the profound horn, and nobody has given that principle grounds of its own. My
named assumption is the sound horn, on purpose. That's where Bennett ended up in 2003, and Norton's "Too Good to Be
True," written in 2025 and published in 2026, says the careful literature almost always takes that horn, and argues that
whatever works there is ordinary thermodynamics relabelled. I'll take that. Ordinary thermodynamics, relabelled onto a
ledger, is all this book asks of the physics.

And on the counting, I'm on Norton's side outright. His 2018 paper "Maxwell's Demon Does Not Compute" disposes of the demon
with Liouville's theorem and nothing else, no information and no computation: motion that keeps every patch of states the
same size can't crowd a big set of states into a small one. The counting at the bottom of this book, that a step losing
nothing can't carry a no-state into a set that stays up, is that point in finite, countable form: chapter two's chairs.

If you want the best case for the assumption itself, the one I found is James Ladyman, Stuart Presnell, Anthony Short and
Berry Groisman in 2007. From one of the standard statements of the second law, the one named for Kelvin, they derive that a
logically irreversible operation can't be carried out in a thermodynamically reversible way by any of their model machines,
which they call L-machines. That's a physical argument under their stated model of a machine. It deserves to be argued with on
those terms. It doesn't by itself give my whole-number charge.


Where the difference goes

A physicist asks one question before any of that, and it's a good one. The laws underneath never merge anything. Classical
mechanics carries each exact state forward to exactly one next state and could carry it back, and Liouville's theorem adds that
a patch of states keeps its size as it moves. Quantum mechanics is one-to-one too. So when this book says a step merged two states,
where did the difference go?

It went out of the machine. The merge is in the machine's own description, the states its reading is about. The machine together
with everything around it still runs one-to-one, and the distinction the machine forgot gets pushed out into the surroundings. The
surroundings are chapter two's endless strip: fresh paper, which the universe as a whole may have to spend and the machine doesn't,
because the machine isn't the universe and its memory fills.

Does that make the whole argument depend on where you draw the machine? Draw it coarser or finer and you get different states: the dial
on a bench is a state, and so is each atom in it, and so is each atom together with the light it gave off. It doesn't, and the reason
fits in one picture.

Draw the fine states, and draw a fence around each group of them that counts as one coarse state. Say the coarse description follows the
fine one exactly: wherever a fine state steps, its fence steps to the fence of where it landed, and every fence has at least one fine
state in it. Now say the coarse picture merges: two fences step to one fence. Then something has to give down below. Suppose it doesn't:
the fine step never merges, never steps outside the fenced states, and no run goes on landing on fine states it hasn't been to before,
forever. Follow any fine run. It must come back to some fine state it's been in, and since nothing merges, walk the two visits back together one step at a time, the way
chapter two did, until the earlier one reaches the start. So every fine run is a loop through its own start. Look at that loop through the
fences: every fence is on a loop too. Now take the two fences that stepped to one. Wait as many steps as the product of their two loop
lengths: each is back where it began. But they were together after one step, and the same rule can't pull them apart again, so they must
have begun in the same place. They didn't. So down below, one of three things happens: the fine step merges, or it steps out of the states
the coarse picture describes, or it runs off taking a new one every tick. The three ways out from chapter two come back one level down.

Chapter nineteen's dial and light are the example. In the dial's own picture, phases wash out and two starts end up the same: a merge. In the
picture of dial and light together, the step is one-to-one, and it's the second way: the light starts blank and leaves carrying the copy, so
the fine step leaves the states where the light is still blank. Nothing merges at the fine scale.

And that's where the heat floor sits: where the merge really is. Landauer's assumption charges the scale whose step merges states that were
really possible. A description that merges only because it stopped looking at the light owes that floor nowhere just because of that. Pushing a
distinction out isn't heat yet, either: another memory could keep it as a readable record. It becomes heat when a reset removes real uncertainty
into something warm, a reservoir, and then Landauer's assumption bounds the average heat handed over.

None of that heat has to be wasted. Takahiro Sagawa's 2014 analysis says erasure can in principle approach a process that produces no entropy
overall: the reservoir's entropy goes up by what the memory's goes down. A positive heat can be unavoidable without being wasteful.


Two meanings of reversible

Ladyman and his coauthors and Sagawa look like they disagree, and they don't. They use "reversible" for two different things.

Ladyman's L-machines are devices, and a device counts as reversible only if it produces no entropy on every input it's fed, each one known. Their
section 4 says it: the L-machine is thermodynamically reversible if and only if every one of its processes, one per input, produces no entropy.
Sagawa's reversible erasure is a process on one given spread of inputs, with the device tuned to that spread. The standard eraser is reversible in
Sagawa's sense and not in Ladyman's: on an even mix of 0 and 1 it produces no entropy, and on each known input it produces k ln 2.

One identity holds the two together. Take a fixed device that sends every input to one output, and any spread of its inputs. The average, over the
inputs, of the entropy produced on each input known, equals the entropy produced on the spread, plus k times the Shannon entropy of the spread. It
holds because the heat is the same average either way, the device being fixed, and the output is the same either way. The only difference is at the
start: the spread's own entropy includes a term for not knowing which input it is, and each known input's doesn't. Sagawa makes the first term on the
right zero. Ladyman reads the left side, which is then k times the spread's entropy, more than zero. For the even mix of 0 and 1 that's k ln 2 on the
left, nothing plus k ln 2 on the right.

That identity hands you a floor that doesn't need anybody's knowledge. Take K inputs a fixed device sends to the same output, and spread your chances
evenly over them. The average over the K of the entropy produced on each one known equals what's produced on the even spread, plus k ln K. The second law
makes what's produced on the spread zero or more. So the average is at least k ln K, and the worst of the K is at least the average. On some one of them,
the device produces at least k ln K of entropy, and, when dissipated work is temperature times entropy produced, at least kT ln K of dissipated work.
Going slowly doesn't remove that. Using different controls for different known inputs changes the device being compared; the bound is about one fixed
device across them. So the floor sits on the merging move, on its worst input, whatever anyone knows. That's the shape of the toll.


Counting in bits

There's one more way to say all this, and I include it because it's how physicists say it, and because it says exactly when the heat floor is zero:
when no two states you might be in land on one.

Claude Shannon, in 1948, gave a number to how much you don't know. If something could be in any of n states and you've no idea which, your uncertainty
is log base two of n bits, the number of halvings from chapter three, and that's the most it can be for n states. Push your uncertainty through a step
that forgets nothing and it stays the same; through a step that merges two states you might have been in, it drops.

Why does Shannon's number share a name with the physicists' entropy at all? There's a story. Shannon wanted to call it uncertainty, and the mathematician
John von Neumann told him to call it entropy instead, for two reasons: the same formula already lived in physics under that name, and nobody really knows
what entropy is, so in an argument he'd always have the upper hand. It's a great story. It comes from Myron Tribus, who spent years tying information theory
to thermodynamics, who said Shannon told it to him in 1961, and who printed it with Edward McIrvine in Scientific American in 1971. Then in 1982 an
interviewer, Robert Price, asked Shannon about it, and Shannon said he didn't think von Neumann had told him any such thing. So it's a legend with one
witness, and the person the witness quoted doesn't remember saying it. What doesn't hang on the story: the two formulas really do have the same shape, and
it still takes Landauer's assumption to turn a count of bits into heat.

Here's how the count works when the chances aren't even. Give each state a chance, all adding to one. Each state contributes its chance times the number of
halvings it would take to single it out, and you add those up. Try four equally likely cards, A, B, C and D. Each has chance a quarter, and singling one out
takes two halvings, so each contributes a half: two bits in all. Now send A and B to a box marked X, C to a box marked Y and D to a box marked Z. The boxes'
chances are a half, a quarter, a quarter. X takes one halving to single out, Y and Z two each, so the three contribute a half each: one and a half bits. Half
a bit was lost on average. You can see where: half the time the box is X and leaves one question unanswered, A or B? The other half of the time, Y or Z tells
you the card exactly. An actual draw never loses half a card; the half belongs to the average over many draws.

  [figure: four cards into three boxes]

A move that forgets nothing sends each state somewhere different, so the chances get carried along one for one: nothing piles up, and the uncertainty is the
same number after as before. That's why a price on bits lost can leave every reversible move costing nothing, which is the shape the toll needs.

Now push uncertainty through a permanent raise. Say m states already read yes, and the move turns k states that read no into yes. Before the move you might be
in any of the m + k states in play. After it, you're in one of m. How much uncertainty can m places hold? At most log base two of m, and only when the chance
is spread evenly. Here's why that's the most, in one line. The curve of the natural log never rises above the straight line y minus one; they touch only at
one. For each place with chance q, put y equal to the even share, 1 over m, divided by q. The line says q times the log of that y is at most the even share minus q.
Add over the places: the right side totals at most one minus one, which is zero. The left side totals the spread's uncertainty minus log m. So the uncertainty is at most
log m, whatever the spread.

So if you started with every one of the m + k states equally likely, you had log2 of (m + k) bits, you end with at most log2 of m, and the move removed at least
log2 of (m + k)/m. That's chapter three's halving count again, in Shannon's units. There's a second floor too, and sometimes it's bigger. Count one landing pile
at a time. Say a pile holds s of the starts. You land in it with chance s over (m + k), and when you do, log2 of s bits are gone: the s starts in it
can't be told apart any more. So that pile's share of the total loss is s log2 s over (m + k). A pile of one adds nothing. A pile of two adds 2 over (m + k).
And s log2 s is never less than 2(s minus 1): the two are equal at s of two, and from there s log2 s climbs faster. So every pile adds at least 2 over (m + k)
for each start after its first. There are m + k starts and at most m piles, so at least k starts come after the first in their pile. That gives at least 2k
over (m + k) bits. The
first floor is reached when k is a multiple of m: keep each old yes-state where it is and send the same number of newcomers to each. The second is reached when
k is at most m: send each newcomer to its own old yes-state.

And in the worst case it's a full bit every time. A permanent raise makes two arrows meet, by chapter two. Put half the chance on each of those two states, and
the move removes exactly one bit, however many states already read yes.

The assumption, stated as I use it: for a chosen physical memory and its spread of inputs, a step that lowers the memory's logical uncertainty by some number of
bits hands at least kT ln 2 of heat per bit to its surroundings at temperature T, on average over that preparation, not on every single run. It needs a physical
model in which the logical uncertainty has that meaning; a table of arrows doesn't supply one. And it's for a symmetric memory, whose two states are alike apart
from their labels, as Landauer assumed. For a memory whose states differ, the floor changes, which Owen Maroney worked out in 2009, and Gavrilov and Bechhoefer in
2016 measured erasure work in a lopsided double well that came out below kT ln 2.


How big is that

Take the case where one state flips in beside one that was already yes. The floor is kT ln 2. At room temperature, about 300 kelvin, that's roughly three
zeptojoules: three thousandths of a billionth of a billionth of a joule. That's the biggest floor a one-state raise gets from the even spread. With one newcomer
the floor shrinks as more states already read yes, because the squeeze gets thinner: with a thousand of them it's 2 ln 2 over 1001 of kT, about a
seven-hundred-and-twentieth, some five hundred times less than the case of two.

So for the even spread, one unit of cost is not one halving. It's one halving exactly when the squeeze is two, and for any thinner squeeze the physics asks for
less, and the toll still charges a whole unit, because the cost comes in whole numbers. In the worst case over what the machine might be holding, the way chapter
three's halving rule reads a move, it's a full bit every time, so the gap between the unit and the bits is a fact about the even spread. Whatever the size, it's heat
only if you grant the assumption; nothing on this page measured anything.

For comparison, Anson Ho, Ege Erdil and Tamay Besiroglu's 2023 tally of the limits of ordinary chips puts switching a single gate at a hundred attojoules at the low
end, over thirty thousand times this floor. The point of the number isn't that a permanent raise is expensive. It's that, on the assumption, it isn't zero.

The same logarithm turns up in a different physical question, and I want to keep the two apart. Yûto Murashita, Ken Funo and Masahito Ueda in 2014 studied processes
whose reverse histories include some with no forward partner, which they call absolute irreversibility. Their bound on average entropy produced picks up the logarithm
of one over the share that's left. Their example is gas that starts in one part of a box split into two, the parts in the ratio l to 1 minus l, and spreads out
through the whole box; the logarithm is of one over l. (Take l to be a tenth and you get the logarithm of ten; that number is my illustration, not theirs.) Make l the
old yes-states' share of the pile, and out comes the same logarithm as the squeeze. That's a match of numbers, not of processes. My arrows don't say what the reverse experiment is or
how likely its histories are, so they don't determine that share. Gonzalo Manzano, Gülce Kardeş, Édgar Roldán and David Wolpert in 2024 studied questions like that for
computations with one-way steps and random stopping times. Their physical assumptions are on top of my counting.

The even spread is the easy case, and it's fair to worry that the heat depends on picking it. It doesn't. Take any spread that gives a real chance to the state that
flips and to every yes-state. After the move, they all land among the yes-states, and there's one more of them than there are yes-states, so two of them with real
chances land together. Count bits state by state: each state carries its chance to where it lands and finds whatever else landed there, and its share of the loss is
how much more crowded its landing spot is than what it brought. Nobody's spot holds less than they brought, so every share is zero or more, and the two that landed
together each find a spot holding more than they brought, so their shares are more than zero. A positive number of bits, at a positive temperature, is positive heat.


Three roads, two strengths

There are three ways to charge for forgetting, and they come in two strengths. Charge the bits a move removes, on every spread: that's entropy pricing. Charge, as
chapter three did, at least as many units as the halvings in a move's biggest landing pile: that's the halving rule. These two are the same rule. The most bits a move
can remove, on any spread, is log2 of its biggest pile, because once you know which pile you landed in, the starts left to tell apart are at most that many; and the
even spread on that biggest pile removes exactly that much. So a price that covers every spread covers the biggest pile, and a price that covers the biggest pile
covers every spread.

The third road is Bennett's rule from chapter three: at least one whenever any two arrows meet. That's the halving rule looked at through two starts only: if two starts
land apart nothing's lost, and if they land together, a pile of two asks for one halving. So it's weaker. Try eight equally likely cards all sent to one box: three bits
lost. A charge of one passes Bennett's rule and fails the other two, which ask for three. All three give the toll on a permanent raise; only the stronger two give the size
of the squeeze.


The coin under the cup

Now the case where the floor is zero. Toss a fair coin under a cup without looking at how it landed, and let the rule be: set it heads up. You might have had tails; now you
have heads; one bit of what you didn't know is gone, and that's the bit Landauer charges for. Now lift the cup, see heads, put the cup back, and apply the rule again. Nothing
you didn't know changed, and no bit was lost. And the assumption, applied to a state you already knew, asks for nothing: a known state is a spread with all its chance on one
state, which holds no bits before or after, so the assumption reads "heat at least zero." It sets no floor.

That's easy to overread, so be careful with it. It doesn't mean a stamping machine run on a known-blank sheet gives off nothing. A real stamping device may cost something
because it runs in finite time; how much depends on how it's built, how it's driven and how fast it goes. All it means is that the assumption sets no floor there. The floor
comes from what you didn't know. And it doesn't mean telling somebody which way the coin landed changes an unchanged device's heat. If you lifted the cup after an uncertain
toss, you made a record that's tied up with the coin, and resetting that record has to be counted with that tie. If the coin was handed to you heads up for certain, there
was no uncertain toss to record. Those are different preparations.

This is the general form of Landauer's principle, worked out by Owen Maroney in 2009, in a paper he wrote at the Perimeter Institute in Canada, and by Sagawa in 2014. And Landauer himself had the seed of it in 1961: for a row of bits all already ONE, he wrote, there's no need to carry out any operation, so no
entropy changes and no heat is given off; and resetting a row all ZERO to ONE involves no entropy change either, because neither row carries any information.

Notice that the toll still charges the known-state stamp one unit, because the toll is a rule about the move, and the move doesn't know what the watcher knows. That's the
worst-case gap from the start of the chapter, and it's the price of having a rule a machine can follow without asking who's watching.

The physics of all this has a standard review, Juan Parrondo, Jordan Horowitz and Takahiro Sagawa's "Thermodynamics of information" from 2015, which puts Landauer's bound,
its general form and the costs of measuring and acting on what you measured side by side. And the gap between a device and the spread it runs on has a physicist's number on
it. Artemy Kolchinsky and David Wolpert showed in 2017 that a fixed process built to waste as little as possible on one spread over its states pays extra when it runs on
another, and the extra is how much closer the process brings the two spreads together, measured in relative entropy. They called it the dissipation due to an incorrect prior, and in 2018 Wolpert and
Kolchinsky gave it the name it goes by now, mismatch cost. Under their
conditions, their formula says which input pays: the one the device's own best spread gave the least chance. A device can make one input cheap only by making another dear.
That's the worst-case gap again, priced for an actual spread, where the toll prices the move.

There's a second piece of fine print, about who works the controls. Lower this barrier, tilt that well, raise the barrier again: those operations have a timing and a
physical build, and counting bits prices neither. Paul Riechers, Alexander Boyd, Gregory Wimsatt and James Crutchfield in 2020 analysed memories held behind barriers under
controls that are the same played forwards or backwards. A symmetric clock pulse can be like that; an arbitrary one needn't be. For that setting, as the allowed error shrinks,
the least work picks up a term that grows like kT times the log of one over the error, times the chance that the memory sits in a state the operation, done twice, doesn't
bring back to where it started. They call those transitions nonreciprocal. A permanent raise is nonreciprocal at the no-state: doing it twice can't bring it back to no. So a
known input there can face extra work in their setting, even though it holds no bits. Their class also includes a three-state cycle, which merges nothing. It's about the
allowed controls as well as the arrows, and it doesn't change the coin under the cup.

One more limit, about which states collide. Chapter two guarantees two arrows meet among the yes-states together with the one coming in. It doesn't guarantee that the one coming
in is one of the two. Take four states with only the first reading no, and a move that sends the first to the second, the second to the third, and leaves the third and fourth
where they are. The second and third land together on the third, and the first shares with nobody. So for a spread with all its chance on no-states, this counting alone forces
no loss. The toll on the move still follows from Bennett's rule.

So here's what the counting and the assumption give together. A permanent raise has two starting states that land on one. Prepare those two with equal chances, and the raise
removes one bit, and on the assumption its average heat is at least kT ln 2. That's a worst-case preparation, not a charge on every run. A known start gets no floor from the
assumption. A fixed device that merges K inputs produces at least k ln K of entropy on one of them. And the ledger charges the merging move whatever the preparation, because my
rule says so. The counting proves a collision; the preparation decides how much uncertainty is removed; and the physics connects that to heat.


Going faster gives off more heat

Everything so far is about the floor, the least heat as you go slower and slower. Going at a speed costs on top of that, and here there's a small model I can work all the way
through.

Charles Bennett's Brownian computer, from his 1982 review, is a walker on a line that's pushed forward a little. At each tick it steps forward with some chance p and back with
the rest. Its speed, on average, is the difference between the two, 2p minus 1. Grant the standard assumption of this corner of physics, called local detailed balance, which
Udo Seifert's 2012 review sets out: a forward step hands the surroundings kT times the log of p over 1 minus p in heat, and a backward step takes the same amount back. Then the
average heat per tick, in units of kT, is the speed times that log, which follows from Jürgen Schnakenberg's 1976 formula for the entropy
produced by a system that jumps between states. When p is more than a half, both are positive; when it's less, both are negative; either way the product is
positive. Only at exactly a half, no drift at all, is it zero. And no drift doesn't mean a walker standing still: it still jumps about, and it can reach a nearby spot on the
first tick. It just doesn't get anywhere on average.

How much heat to get somewhere? Per step forward on average, the heat is the log of 1 plus v over 1 minus v, where v is the speed, and that log is never less than 2v: the difference
is zero at no speed and only grows from there, because its slope, 2 over (1 minus v squared), minus 2, is never negative. So walking a distance N costs at least 2N times v in heat and
takes N over v in time, and heat times time is at least twice N squared. Halve the speed and the heat about halves while the time doubles; the product never drops below twice the
distance squared. Going slowly makes the heat for a given distance smaller and the time longer. These are averages.

The walker is the case I can work by hand. Others have worked other models. Tim Schmiedl and Udo Seifert in 2007 found the best way to drag a bead in a spring-like trap through water
from one place to another in a set time, and the least work you can get away with is the drag times the distance squared, divided by the time plus twice the drag over the stiffness:
at long times, drag times distance squared over time. Erik Aurell, Carlos Mejía-Monasterio and Paolo Muratore-Ginanneschi in 2011, for a bead that drifts, and Naoto Shiraishi, Ken Funo
and Keiji Saito in 2018, for states that jump, showed that changing one spread of chances into another in a set time produces at least a fixed fraction of the square of how far apart
the two spreads are, divided by the time and by how lively the motion is. Those are their results under their stated motion, and I cite them as physics. They're about entropy produced,
not positive heat on every step: a step that leaves the spread exactly as it was owes nothing on them, and a single step's heat can be negative when the device's own entropy goes up.

And there's a machine that, in principle, owes nothing at all. Edward Fredkin and Tommaso Toffoli, whose gates that lose nothing were in chapter two, also described in 1982 a computer
made of perfect billiard balls bouncing their way through a computation, and in principle it could run without wasting anything. Bennett wrote in 2003 that such ballistic machines compute at constant velocity without dissipating any energy, and that they must be kept
isolated from heat baths and noise. Keeping one on course against noise means correcting its errors, and whether that brings the waste back I don't settle here; in 2003 Bennett called the
thermodynamics of error correction a subject that appears to be in its infancy.

The bead of Jun, Gavrilov and Bechhoefer shows the other half. Put through the same moves as an erasure but with no tilt, so nothing is squashed, its work, carried out to the slow limit,
came out at 0.05 kT, give or take 0.03: within two error bars of zero. No floor under it, which is what the assumption says. With the tilt, so two wells really do become one, it came out at
0.71 kT, give or take 0.03, against ln 2, which is 0.693.

So keeping something costs, on top of going at a speed, either a merge, which on Landauer's assumption owes kT ln 2 per bit that no slowness removes, or a state the device has never used
before. Taking a fresh state escapes the floor, and doesn't settle how much a real device wastes in finite time. And a finite set of states, where every state has a next one, forces the merge.


A simulation in code

I wanted to see those steps, so I ran a simulation in code. It models a bead in a double well shaped like a quartic curve, and follows the experiment's sequence: lower the barrier for one
second, ramp a tilt, take the tilt away, raise the barrier for one second. The well is a shape I chose and the motion is a numerical approximation; it isn't the measured trap, and nothing in it
was measured. The modelled bead starts from the thermal spread in that well, equally likely on either side.

Keep three accounts as it moves. Changing the trap while the bead holds still does work on it. The bead moving in a fixed trap hands heat to the water around it. Whatever's left changes the
bead's stored energy.

  [figure: work in, heat out]

Work in minus heat out is the change in stored energy, on every simulated path, to rounding. That checks the bookkeeping. It doesn't show the time steps are small enough to copy continuous motion
exactly.

Here's what came out, with 3,000 paths at each setting and a time step of half a millisecond. Each setting uses a tilt picked to make roughly nine erasures in ten work, and success means ending in
the right well. The last two columns average only the successes, in units of kT. The time column is the tilt ramp; the two one-second barrier ramps come on top.

  [table: bead simulation]

Heat and work are close in some rows and less close in others; the difference is measured by the simulation, not put in by hand. Now try to make a floor out of those six points. Fit the successful
heat to a constant plus a number divided by the tilt time, and the constant comes out at 0.674 kT, give or take 0.015, near ln 2. Halve the time step and run the six
settings again, and it comes out at 0.732 kT, give or take 0.016: it moved by nearly four of its own error bars. The second run also samples different paths, so that
comparison mixes sampling error with numerical error. Still, it's enough to
stop me treating a fitted constant near ln 2 as a confirmation. The barrier ramps are still one second long, the tilt changes between settings, and the fit doesn't take the whole procedure to a slow
limit.

There's a theoretical comparison, and it's a comparison with work. For the continuous thermal model, starting in equilibrium and ending in the same symmetric trap, there are two bounds, both
written in terms of the success rate p. Averaging over successes and failures, the work is at least kT times ln 2, plus p ln p, plus (1 minus p) times ln (1 minus p); that's
the formula from Bérut and his coauthors' 2012 paper that drops to zero at half. Looking only at the successful paths, the work is at least kT times the log of 2p. Bérut,
Artyom Petrosyan and Ciliberto worked that one out in 2013, from a version of Christopher Jarzynski's 1997 equality that sorts paths by how they end, due to Suriyanarayanan
Vaikuntanathan and Jarzynski in 2009 and to Ryoichi Kawai, Juan Parrondo and Christian Van den Broeck in 2007. At nine successes in ten the two come to about 0.368 kT and
0.588 kT. Neither is a heat bound for the simulation without also counting its change in stored energy.

The script is in the repository as scripts/bead_erasure_sim.py. It reports heat, work, stored-energy change, sampling errors and the fits, and takes a smaller time step for checking them. What it shows
is that the slower settings use less work and give off less heat on average. It doesn't find a universal floor, and it doesn't reproduce the laboratory's fitted constant.


What's been measured

Here's the laboratory side in one place, so you can see how near it has come to each piece.

  [table: what has been measured]

These experiments test particular memories and procedures, including the symmetric-memory floor and heat against time. They aren't a survey of all physical computation, and they aren't an experimental
proof of the counting.


Why the rule sits on the raise

So here's how the heat and the toll fit. The toll charges for what's kept, whichever way it's paid, merge or fresh paper. A price on merges alone charges only the merge, so it misses something kept
by taking fresh paper: the machine that keeps every history, chapter two's endless strip, raises its box at zero cost under it. And it charges merges that keep nothing, like a reset that takes a box
down. The toll doesn't ask that reset for a unit, and it still merges two states, so in a real device it owes Landauer's floor whenever the bit it lowered was really unknown. The ledger leaves that to
physics, along with the waste of going at a speed.

That's the heat. What none of this touched is what keeping takes when the steps themselves are noisy, or quantum, and how much room a memory needs to keep its history without any merge at all. That's
the next chapter.
