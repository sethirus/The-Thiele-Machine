from audit import edit,span,note
edit('landauer_average',r'''A step that lowers the entropy of the machine's state by $\Delta H$ bits, at temperature
$T$, gives off heat $Q \ge k_B T \ln 2 \cdot \Delta H$, where $k_B$ is Boltzmann's constant.''',r'''For the chosen physical memory and its input distribution, assume that a step lowering
its logical-state entropy by $\Delta H$ bits transfers mean heat
$Q \ge k_B T \ln 2 \cdot \Delta H$ to a bath at temperature $T$, where $k_B$ is Boltzmann's constant.
Here $Q$ is an average over that preparation, not a bound on each individual trial.
Applying this premise requires a physical model in which the logical entropy loss has
this thermodynamic meaning; a bare state-transition table does not supply one.''','Clarify ensemble-average heat and physical interpretation prerequisite.')
span('absolute_irreversibility_scope', 'Physicists have a name for a step with no way back', 'The even spread is the easy case',r'''A related logarithm appears in a different physical question. Y\^uto Murashita,
Ken Funo and Masahito Ueda (2014) study processes whose reverse histories can include
ones with no forward counterpart. They call this \emph{absolute irreversibility}.
If those reverse histories have total probability $\lambda$, their bound on mean
entropy production contains $-\ln(1-\lambda)$. In their free-expansion example, gas
initially confined to a fraction $l$ of a box gives $\ln(1/l)$.

Setting $l=m/(m+k)$ gives the same logarithm as the squeeze bound. That numerical
match does not identify two physical processes. Our arrows specify neither a
thermodynamic reverse experiment nor its path probabilities, so they do not determine
$\lambda$. We cannot infer absolute irreversibility, its absence, or a heat equality
from the state count alone. Gonzalo Manzano, G\"ulce Karde\c{s}, \'Edgar Rold\'an and
David Wolpert (2024) study such trajectory-level questions for computations with
one-way transitions and random stopping times. Their physical premises are additional
to the counting done here.''','A deterministic logical map and matching logarithm do not specify thermodynamic reverse histories or absolute-irreversibility parameter.')
edit('door_three_price_scope',r'''So the premise is Landauer's
claim taken in its worst case over what the machine might be holding, and that's the
version the counting needs.''',r'''Merge pricing keeps only a yes-or-no distinction: whether any pair can merge. It is
motivated by the one-bit reset, but does not itself measure the full worst-case entropy
loss or the heat of a particular preparation. The counting needs that abstract price rule.''','Remove remaining identification of pairwise merge price with full worst-case Landauer charge.')
edit('known_state_preparation',r'''The principle
charges for \emph{uncertainty removed}. The shape of the move doesn't enter.''',r'''The entropy-loss bound depends on the preparation and on what the move does to it.
Here ``known'' means a preparation concentrated on one logical state, or a conditional
ensemble whose side information is explicitly included in the account. Merely telling a
spectator which way the coin landed does not change an unchanged device's heat.''','Observer knowledge alone does not change thermodynamics; distinguish physical ensemble and conditional information.')
edit('summary_k_merges',r'''forgets something, and a move that raises k states collapses at least k of them.''',r'''has a collision somewhere. If it raises $k$ distinct no-states, the yes-states together
with those newcomers have at least $k$ fewer distinct outputs than inputs. This does
not say that each newcomer shares its destination.''','Count lost distinguishable alternatives, not which individual states collide.')
edit('quantum_recurrence_scope',r'''The quantum version came in 1957, when P. Bocchieri and A. Loinger proved the same return
for a closed quantum system whose energies come in separate levels, so going quantum isn't a way
out of the room either, not for a closed system that never sheds anything.''',r'''A quantum recurrence result came in 1957, when P. Bocchieri and A. Loinger proved
returns arbitrarily close to the initial state under their conditions on a closed
quantum system. That is a neighbouring recurrence argument, not this finite-state proof:
even a finite-dimensional quantum system has continuously many states. Applying it to a
physical record requires saying how that record is read and how robustly it distinguishes
nearby states.''','Do not identify approximate quantum recurrence with finite-state exact pigeonhole argument.')
edit('intro_permanent_price',r'''A finite machine pays to
keep anything for good, and that's the chairs, still to come.''',r'''On a finite machine, writing a record that stays up forces the instruction to merge
some states. Charging for that merge is a further premise. Those are the chairs and the
price rule, still to come.''','Front matter must not infer price from finiteness alone.')
edit('intro_bennett_steps','It costs about twice the steps and a lot of scratch paper, and that\'s all it costs.', 'It takes a forward run, a copy of the answer and a backward run, with scratch space for the history.', 'Avoid universal overhead constant and total-physical-cost inference.')
edit('intro_bennett_bill','the steps and the scratch paper are the whole bill.', 'the construction accounts for steps and scratch space, without establishing zero heat for a physical implementation.', 'Absence of entropy-loss lower bound does not exhaust physical costs.')
edit('intro_heat_scope',r'''and if Landauer's right, a merge costs heat whenever the machine doesn't already know which of the
merged states it was in. So on that assumption, a device that has to settle things correctly
without knowing its own state ahead of time can't do it for free.''',r'''and under the adopted Landauer premise a preparation giving positive probability to
both members of a colliding pair has a positive mean heat bound. The instruction's collision
is one fact; which starts actually occur, and the physical device's heat, are further facts.''','Early explanation must distinguish existence of collision from positive average loss for chosen preparation.')
edit('intro_information_scope',r'''The difference isn't information; information theory says the sort added nothing new.''',r'''It isn't a difference in the algorithmic information of the final list: the list is the
same. A retained record of the runs would be additional information, and these two machines
kept none.''','Algorithmic information of equal outputs does not make history noninformational.')
edit('intro_final_heat_scope',r'''If Landauer's
right, that costs, for any device that has to settle things without already knowing which state
it's in.''',r'''A preparation that actually loses uncertainty through that merge has a mean heat bound
under the physical premise. The merge by itself does not give every run that bill.''','Propagate ensemble dependence to opening conclusion.')
edit('intro_log_scope', 'A log kept by one program\ncovers only that one.', 'A log a program can freely write does not by itself supply that guarantee.', 'Conventional software monitors can enforce guarantees across many programs.')
edit('short_price_scope',r'''If merging is charged for, the way Landauer's
principle charges for it in its worst case, the rule follows.''',r'''If every merging instruction is charged at least one mark, the rule follows.
That is an abstract price on the instruction; a physical heat bound also needs the
input distribution and the device premises.''','Correct short-version conflation of abstract and physical price.')
edit('short_machine_usage',r'''Parts I to III never use my
machine; every claim in them is about any system with the pieces it names, and the pictures
are toys.''',r'''Parts I to III develop the abstract arguments and their examples. They also point ahead
to instances and limits on the machine built in Part IV.''','Parts II–III explicitly apply record-layer merge and other results to concrete machine.')
edit('ledger_partition_uniformity', 'entitles exactly the groupings that refine it & proved', 'entitles, uniformly over keys, exactly the groupings that refine it & proved', 'Propagate uniform-over-keys quantifier to ledger.')
edit('ledger_time_tax_view', 'no free program of fewer than $m$ moves decides $A \\ge m$,', 'no free program of fewer than $m$ moves decides $A \\ge m$ from its final line and $B$,', 'Lower bound concerns specified output observation, not direct inspection of A.')
edit('ledger_reversible_scope', "A finite reversible base can't write a record & proved; an endless history can", "A finite reversible machine cannot raise a permanent reading & proved; an unbounded-history extension can", 'Finiteness must cover the extended state space, not only the projected base.')
edit('ledger_nat_quantifiers', 'The nat family: every decider misses program two', 'The nat family: each candidate decider misses program two in the instance built from it', 'Quantifier order: one substrate per candidate, not one substrate defeating all functions.')
note(1,'Reviewed risky introductory claims and all summaries against body. Correct unconditional price and heat language, implementation costs of reversible simulation, output-information distinction and unguarded-log generalization. Retain physical/structural and universal-program restrictions.')
note(2,'Reviewed short version and reading map. Correct abstract-price/heat conflation and false claim that earlier parts never instantiate the later machine.')
note(7,'Compared all formal statements and proofs with explanation, finite/all-state conditions, distributions and physical interpretations. Correct collision location, pricing-strength equivalence, known-state preparation, mean heat, absolute-irreversibility analogy, quantum recurrence analogy and primary-source time-symmetry bound. Physical premises remain premises.')
