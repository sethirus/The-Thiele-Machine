from audit import edit,span,note
span('entitlement_check_payment', 'Without the third part, the object may be sitting right there', "And here's the part to hold on to.", r'''Keep the second and third parts separate. A note saying ``coin under cup one, checked''
can be written without anyone lifting a cup. That gives an object, but no checked relation.
Now actually lift the cup, find the coin and write the result. Suppose this is a free move:
the note is on the sheet, the check really happened, but the NO box stays NO and the tally
line stays blank. This time the object and the checked relation are both there. What is
missing is the paid event. The run isn't entitled in this definition's sense; that doesn't
make the result of the check false.

The reverse distinction matters too. A move from NO to YES earns a mark on the tally line,
but the bare toll says nothing about what that move looked at. Payment alone supplies
neither a check nor its correctness. The later machine will bind those acts together in its
step rule. The five parts of a certification system do not do that by themselves.''','Separate missing verification from missing payment; neither alone establishes the other.')
edit('lvars_read_discipline',r'''That's a cup. What the cup buys them took me a couple of reads. As I understand it,
writers running side by side can push the value up in a different order on every run, and a cup
that's up stays up whatever the order was, so a program that only ever looks at cups can't see
the others' timing.''',r'''That's a cup. Writers running side by side can push the value up in different orders,
and a threshold once passed stays passed. Their deterministic behaviour also depends on
which reads and updates the language permits. Permanence alone would not do it: a program
allowed to ask whether the cup is up \emph{yet} could still see another writer's timing.''','Monotonicity alone does not imply schedule independence.')
edit('direction_base_noninterference', 'Here the record is never allowed to steer anything, so I sit with the ghost state.', 'Here the record is never allowed to steer the base computation, so that particular restriction sits closer to the ghost state.', 'Restrict noninterference to the base projection.')
edit('window_parity_information',r'''A window that knows nothing about where you are, and knows
exactly when you've gone somewhere, can send the right bill every time.''',r'''A window that cannot tell you your exact place, but detects every rise and every pause,
can send the right bill every time.''','Parity carries partial information about position.')
edit('weighted_entropy_scope',r'''Take any spread of non-negative weights over the states, uniform or not. (1) If every landing pile
has at most $N$ states, the conditional entropy of the state given its landing spot is at most the
total weight times $\log_2 N$ bits. (2) So on a machine with finitely many states and the halving price, the average
information a move destroys is at most its cost in bits, times the weight. (3) The bound is reached:
the even spread on a pile of $2^c$ states loses exactly $c$ bits.''',r'''Take any spread of non-negative weights over the states, uniform or not. (1) If every landing pile
has at most $N$ states, with $N\ge1$, the weighted conditional entropy of the state given its landing spot is at most the
total weight times $\log_2 N$ bits. (2) So on a machine with finitely many states and the halving price, that weighted
information loss is at most its cost in bits times the total weight. For a probability distribution,
the total weight is one and the average loss is at most the cost. (3) If a landing pile has $2^c$ states,
the uniform probability distribution on it loses exactly $c$ bits and attains that bound.''','State positive logarithm argument, normalization and attainability condition.')
edit('infinite_halving_price',r'''No finite toll can price a move that sends infinitely many states
to one spot, and that's a theorem.''',r'''No finite charge satisfying the halving price can price a move that sends infinitely many states
to one spot. The weaker merge price could still charge one; it does not measure the pile's size.''','Infinite-fibre impossibility concerns halving pricing, not every toll.')
edit('infinite_average_budget',r'''two bits of toll would cover the average, though nothing covers the worst case.''',r'''a two-bit information budget covers the average, though no finite budget covers the worst case.''','Distinguish information budget from arbitrary instruction toll.')
edit('infinite_divergence_budget','No toll covers it, on average or otherwise.','No finite information budget covers that average loss.','Scope divergence to entropy.')
edit('infinite_theorem_budget','grows past every bound, so no cost covers it.','grows past every bound, so no finite bit budget covers it.','Scope formal conclusion to quantity calculated.')
note(11,'Checked entitlement, paid trees, covers, posterior counts and refinement. Separate absent check from absent paid event; qualify refinement characterization as uniform over keys.')
note(14,'Checked threshold representation, strict-chain cup count, counterexamples and generalized merge/revoke claims. Correct LVars timing inference and restrict noninterference to base.')
note(15,'Checked window exactness, fibre location, halving/entropy bounds and infinite-pile distributions. Correct weighted versus normalized average, attainable bound, and infinite-fibre pricing scope.')
note(16,'Checked substrate diagonal, nat-family quantifier order, L recursion construction and Rice argument. Internal representation restriction and distinction from generic application are explicit. Quoting construction cross-checked in appendix review.')
note(17,'Checked Casper proof cases, gas arithmetic and uncapped scope, quote indistinguishability, symbolic Merkle examples and bounds checker. These remain scoped fragments, not verification of deployed protocols.')
note(18,'Checked independence mixing argument, reachable-state restriction, pointer definitions, observer-map counterexamples and durability proof. Empirical pointer claim is explicitly a thesis, maps are explicitly stipulated.')
