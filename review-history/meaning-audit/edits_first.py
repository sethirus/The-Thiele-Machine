from audit import edit,span,note
span('reset_full_state','Making a record on a blank place is one operation.',"I'll put the rest of the lineage quickly,",r'''
Making a record on a blank place is one operation. Landauer's 1961 paper names
another: set a bit to one whatever it held. If that bit is the whole state, down
goes to up, up stays up, and two possible states become one. Landauer called this
``restore to one.'' On an uncertain input it removes information; a heat bound
then needs the thermodynamic premises.

A larger machine has more state than its flag. Two starts can both finish with the
flag up while remaining different elsewhere. The next section proves that, on a
finite machine whose reading is permanent, any instruction that raises it must
merge some full states. It does not say the newly certified state is one of that
pair. Put one chair outside the certified room and two inside. Send the outsider
to the first inside chair, and both insiders to the second. The flag rises for the
outsider, but the two insiders are the states that merge. These arrows describe
alternative starts, not three things happening in one run.

That is the distinction the one-bit picture hides. The instruction has a collision
somewhere; the actual distribution of starting states determines whether that
collision removes uncertainty. A known starting state loses none under the entropy
premise, even when its flag rises (Theorem~\ref{thm:known-state}). The ledger can
still charge the instruction under merge pricing. A ledger charge, information
loss and a device's heat are three quantities to keep apart.
''','Separate the two-state reset, whole-state collision, actual input distribution and physical heat at the first explanation.')
edit('reset_lineage',r'''The step itself has a price on
it already: raising a flag that stays up, from a state that might already have it up, is
Landauer's restore to one, and he priced that as a reset in 1961. What nobody I found wrote down
is when a certifying step has to be that reset.''',r'''The literal one-bit reset already has a thermodynamic analysis: Landauer's restore
to one. The question here is which premises force an instruction that raises a
record to merge full states, and which further premises let us price that loss.''','Remove the repeated identification of every permanent flag raise with the literal two-state reset.')
edit('reset_smallest_scope',r'''Landauer's restore to one, which is the one-bit
toll step, priced as a reset whatever the bit is standing for.''',r'''Landauer's restore to one, the literal two-state version of the crossing, whose
heat bound depends on the input uncertainty and the thermal premises.''','Keep the lineage comparison from implying an unconditional physical price.')
edit('chairs_local_collision',r'''Finite. Permanent. Flip. Those three and nothing else, and the conclusion is ``two states
became one.''''',r'''Finite. Permanent. Flip. Those three force a collision in the instruction's map.
The two starts that collide need not include the outsider: send the outsider to
one inside chair and send two insiders to another. A run from a known outside
chair can still have a uniquely identifiable start. The collision is a fact about
the instruction over possible states.''','Put the quantifier distinction directly beside the chairs argument, not only in the later known-state discussion.')
span('pricing_strength_before','So there are three roads to the toll: merge pricing,',r'\begin{theorem}[One premise, three forms]',r'''
There are three roads to the toll, with two different strengths. Entropy pricing
and the halving price are equivalent: the most bits a deterministic move can remove
is the base-two logarithm of its largest pile of starts sharing a destination.
Merge pricing asks only for at least one mark whenever any pair collides. It is
the two-state restriction of the stronger conditions.

Try eight equally likely cards all sent to one box. The loss is three bits. A
charge of one meets merge pricing but fails entropy pricing and the halving price,
which require at least three. All three conditions give the permanent-record toll;
only the stronger two give the full squeeze bound.
''','Correct prose implying equivalence between pairwise merge pricing and full entropy/halving pricing.')
edit('pricing_theorem_title',r'\begin{theorem}[One premise, three forms]',r'\begin{theorem}[Entropy pricing, halving, and pairwise merge pricing]','Make the theorem title reflect its unchanged, qualified statement.')
span('pricing_strength_after',' So the premise under all three roads is','Now the zero.',r'''
Thus merge pricing is weaker than full entropy pricing, though both force the
one-mark toll under the permanence and finiteness premises. The mathematical
prices are rules on instructions. A physical interpretation additionally needs
Landauer's premise for the actual distribution and an explicit conversion from
bits or marks to thermal quantities.
''','Preserve the difference between abstract operation pricing and a distribution-dependent heat bound.')
edit('known_device_heat',r'''A fixed device that merges states dissipates on known input too; Bennett calls that
wasteful, because entropy goes out into the room with nothing taken from the data.''',r'''A device can dissipate on a known input too: heat can go into the room even when
no uncertainty is removed from the data. Its dissipation depends on its physical
implementation and control protocol.''','Do not assert that every fixed merging device has positive dissipation for every known input.')
edit('record_price_not_physics',r'''on the part of the state that's new it's still Landauer's premise.''',r'''on the record distinctions it is still an assumed operation-level price; identifying
it with heat needs a physical model.''','Record-layer merge pricing is not itself the thermodynamic premise.')
edit('record_toll_premise',r'''On that machine the toll is forced by Landauer's
premise asked of the record layer, and the machine's own price list, clause (c) included, is one
the premise allows.''',r'''On that machine the toll follows from record-layer merge pricing, and the machine's
own price list, clause (c) included, satisfies that premise. This is a result about
its ledger, not a heat bound.''','Stop silently converting an abstract pricing assumption into Landauer physics.')
edit('reversible_floor_not_zero',r'''full merge pricing charges the base nothing, and clause (c) holds with merge pricing as it stands.''',r'''full merge pricing permits those base moves to cost zero. Choosing that schedule
would meet clause (c); the lower-bound premise alone does not require zero charges.''','A floor permits free injective moves; it does not force them to be free.')
edit('physics_reset_summary',r'''What the permanence
theorems add is the \emph{derivation}: which premises about a machine (finite, permanent) make
the certifying step a reset, so that Landauer applies to it. That's a result about the
machine. Physics gets nothing new from it, and that's the right size for it.''',r'''What the permanence theorems add is a structural derivation: finiteness and a
permanent reading force any flag-raising instruction to merge some full states.
They do not identify the newly certified state as part of that collision, or
supply the input distribution and physical conditions for a heat bound. With
those supplied, Landauer's premise applies to the uncertainty actually removed.
The machine result and the physical premise do different jobs.''','Repeat the corrected scope in the physics summary.')
edit('ledger_pricing_strength',r'''Merge pricing, the halving price and entropy pricing are one premise: the most bits a move removes from any spread is $\log_2$ of its worst pile-up, entropy pricing is the halving price, and merge pricing is both asked of two states''',r'''Entropy pricing is equivalent to the halving price; merge pricing is their weaker restriction to pairs. The largest entropy loss is $\log_2$ of the largest pile-up''','Make the claims ledger agree with the actual pricing-equivalence theorem.')
edit('assumption_pricing_strength',r'''Third, merge pricing is Landauer's principle taken in its worst case over
what the machine might be holding: it charges every merging move, while the principle in its
general form charges only for uncertainty actually removed, when the step can be driven by a
protocol timed from outside it (Theorem~\ref{thm:known-state}).''',r'''Third, merge pricing is an abstract lower bound on every merging instruction.
It is the pairwise restriction of worst-case entropy pricing, which is equivalent
to the halving price. Landauer's premise instead bounds heat from the uncertainty
actually removed under its thermal conditions. A known starting state supplies no
positive floor from that premise (Theorem~\ref{thm:known-state}).''','Keep the assumption appendix from identifying a qualitative charge with a physical entropy bound.')
edit('index_questions_scope',r'''the number of yes-or-no questions it takes to pick one of $n$ things.''',r'''the fewest yes-or-no questions that can guarantee identification among $n$ things
when arbitrary binary splits are allowed.''','State the worst-case and available-question conditions behind the index-bit interpretation.')
edit('potential_floor_not_exact',r'''Only
in the trivial way: the conversion costs exactly one mark and that's the whole theory.''',r'''Only as this simple resource-accounting example: the floor is one mark for a
no-to-yes run. An exact one-mark conversion additionally needs a run attaining it.''','The generic toll proves a lower bound, not attainability or an exact conversion price.')
edit('partition_uniformity',r'''which is item (2), and what a raised reading entitles is read off the partition too: every finer
grouping, and nothing else. Refinement, the order on partitions, is the entitlement order.''',r'''which is item (2). Soundness of the recorded grouping guarantees soundness of every
refinement, uniformly over all keys. A grouping that is not a refinement may still
be sound for a particular key; the guarantee does not extend to every key. If all
four buttons have the same colour, every grouping is sound. The theorem identifies
what follows from the first grouping's soundness alone.''','Distinguish a guarantee uniform over keys from truth for one particular key.')
edit('insight_extra_hypotheses',r'''so adding any hypothesis
about what else the end state shows leaves the bound at $1$ and cannot raise it.''',r'''so that proof establishes the same lower bound $1$ whatever else the end state
shows. A stronger lower bound can follow from additional hypotheses, but those
hypotheses must do additional work; it does not follow from the toll alone.''','Additional hypotheses can strengthen a bound; a proof not using them cannot rule that out.')
edit('insight_price_depth',r'''And putting something remarkable behind the reading doesn't make it cost any more.''',r'''The toll alone does not charge more for a remarkable claim; another pricing rule
or an additional requirement could.''','Scope the flat floor to the stated toll rather than all possible cost laws.')
edit('latch_noninterference',r'''The pieces
above the line, the record and the ledger, are the ones that never steer anything; the pieces that
make a flag mean something sit below it, where this theorem doesn't look.''',r'''The cover makes the projected base step independent of which extension state lies
above it. The record, ledger and hidden fields may still affect other extension
fields; the theorem does not make the entire extension inert. On the small machine,
the checks that give the flag its meaning sit in the base chosen for this cover.''','A commuting cover guarantees noninterference with the projected base, not all fields of the extension.')
edit('latch_ledger_event',r'''``The ledger passed one'' is an event too, and so is anything else the base can reach.''',r'''``The ledger passed one'' is an event only if the chosen base includes enough
information to decide it. An extension-only ledger is hidden from a base event,
just as the hidden clock was. The free choice is among functions of the chosen base.''','Do not allow the free-event choice to violate the base-driven condition.')
edit('finite_record_instruction',r'''on a finite machine the record's first write is a merge, and
Section~\ref{sec:a2-not-arbitrary} already put the price on that.''',r'''on a finite machine an instruction that first raises a permanent reading must
merge some possible states. The entering state need not belong to the colliding
pair; Section~\ref{sec:a2-not-arbitrary} prices the instruction under merge pricing.''','Carry the instruction-versus-actual-state distinction into the reversible-record discussion.')
note(5,'Compared equivalence/partition theorem and proof with surrounding scope and prior structural examples. Retain the stated ruler for smallest and the extra yes-label distinction; no stronger mathematical equivalence introduced.')
note(6,'Checked certification definition, first-crossing proof, fixed-start caveat, composition examples and reset comparisons. Correct first reset explanation and repeated lineage claims; retain toll as definition rather than universal physical necessity.')
note(8,'Checked own-image narrowing, observer knowledge, four-state demon and minimal three-state teacher. The existence-versus-forced-free distinction is already explicit. Qualify index-bit interpretation by guaranteed identification and available questions.')
note(9,'Checked conservation, reachable-state uniqueness, potential equivalence and summaries. Correct exact-one conversion claim: the abstract result supplies a floor, not attainability.')
note(10,'Checked decoder direction and section assumption, step-pair collision versus state collision, conditional transcript verifiers, and universal bare-verifier claim. Contracts and abstract cost are explicitly stipulated; retain. Reference to record is a worked example, not a guarantee of public authenticity.')
note(11,'Checked paid-tree bounds, covering conditions, run-generated posteriors and partition/refinement theorem. Correct uniform-over-keys versus one-key prose; inspect entitlement example to separate missing check from missing payment.')
note(12,'Checked event definitions, flat-floor remark and unconstrained crossing. Correct claim that extra hypotheses cannot strengthen a bound and scope flat cost to the toll alone.')
note(13,'Checked latch factorization, converse, growing-history construction, hidden-clock cases, event selection, probabilistic records and weak equivalence. Correct noninterference overstatement and ledger-as-base-event ambiguity; keep all-state/reachable and threshold qualifications explicit.')
