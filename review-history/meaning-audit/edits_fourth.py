from audit import edit,span,note
edit('computable_translation','(3) So no translation\nfrom two-counter programs to one-counter programs keeps halting, unless', '(3) So no computable translation\nfrom two-counter programs to one-counter programs keeps halting, unless','Undecidability excludes effective reductions, not set-theoretic assignments.')
edit('compiler_certification_scope',r'''So compiling
a program computes its answer and certifies nothing: the compiler is a route to answers, and a
certification has to be written into the source as a CHECK, a COMMIT and a CERTIFY.''',r'''So a terminating compiled program delivers its answer and certifies nothing. To certify a
claim about that answer, a target program must add a CHECK, a COMMIT and a CERTIFY;
this compiler does not insert that chain.''','Do not claim unsupported source-language record instructions or termination of every source program.')
edit('pair_six_attainment','six, and six is reached. (6)', 'six. Suitable loaded starts and a three-act certificate on each side attain six; this does not promise to reach every chosen pair of thresholds in six moves. (6)', 'Distinguish joint nonvacuity witnesses from arbitrary target reachability.')
edit('injective_heat_floor',r'''Such a step can be run backward, and Landauer's principle charges it nothing; a floor
read without the last clause would charge it a whole unit.''',r'''Its input can be recovered from its output, and its entropy loss is zero. The adopted
Landauer premise therefore supplies no positive heat floor; this does not promise that an
implementation gives off no heat. A floor read without the last clause would charge a whole unit.''','Logical reversibility removes this lower bound, not all implementation dissipation.')
span('time_symmetric_physics','The generalized principle can charge a known state nothing', 'A deterministic run from a known start',r'''The entropy-loss bound supplies no positive floor for a known input. Whether a device
can approach that floor also depends on its controls: lower this barrier, tilt that well,
raise the barrier again. Those operations have a timing and a physical implementation.
The entropy calculation alone does not price either.

Paul Riechers, Alexander Boyd, Gregory Wimsatt and James Crutchfield (2020) analyse
metastable memories under \emph{time-symmetric} control: the prescribed control is the
same played forwards or backwards, with the relevant time-reversal conventions. A
symmetric clock pulse can meet that restriction; an arbitrary clocked pulse need not.
For memory states unchanged by time reversal, their low-error result distinguishes
inputs $m$ for which applying the desired logical map $C$ twice fails to return to $m$.
They call those transitions \emph{nonreciprocal}. With equal local-equilibrium free
energies, the leading minimum-work term as the error allowance $\varepsilon$ tends to
zero is proportional to
\[
k_B T\ln(1/\varepsilon)\,
\Pr\bigl(C(C(m))\ne m\bigr).
\]
The probability is over the initial memory states. This is a low-error scaling with
physical premises, not an exact finite-error heat charge on every execution.

A permanent flip from no to yes is nonreciprocal at that no-state: a second application
cannot return it to no. A known input at that state can therefore face the extra work
cost in their restricted control setting, even though its initial logical entropy is zero.
Their class also includes a three-state cycle, which merges nothing. The distinction is
about the permitted controls as well as the logical map. It neither changes
Theorem~\ref{thm:known-state}'s entropy calculation nor identifies the book's abstract
merge price with a universal physical bill.''','Primary paper equations 28–30 give input-weighted low-error work scaling, with time-reversal assumptions; avoid exact universal heat claim.')
edit('assumption_control_scope',r'''Under time-symmetric control,
Riechers, Boyd, Wimsatt and Crutchfield (2020) argue, even a known state pays for a move that
doesn't undo itself.''',r'''Riechers, Boyd, Wimsatt and Crutchfield (2020) derive additional work bounds under
time-symmetric control of metastable memories. Their low-error bound depends on the
initial distribution and the memory's time-reversal behaviour; it is not a universal
heat charge on each logical move.''','Propagate primary-paper scope to assumption summary.')
edit('pointer_falsifier', 'a rival event copied and relied on as well\nas certification in a real ecosystem;', 'a rival event copied and relied on that fails at a reachable state where\ncertification holds in a real ecosystem;', 'A weaker copied event is compatible with certification as strongest pointer.')
edit('independence_falsifier',r'''A clause none of the
excluded machines needs: drop it and show the paid latch or the silent machine still fails, and
the exclusion of the paid latch or the exclusion of the silent machine has been proved
by the wrong clause, which is worth a letter.''',r'''For clause independence, take one of the four witnesses in Theorem~\ref{thm:tc-independent}
and show that it also fails one of the three clauses it is said to meet, or that it meets
the clause it is said to fail. That would break the claimed independence witness.''','Earlier paid latch fails two clauses; dropping one does not refute exclusion proof.')
edit('conclusion_price_premise',r'''and if forgetting is charged for, the way Landauer's
principle charges for it in its worst case, the toll follows.''',r'''and under the merge-pricing rule the toll follows. The collision is a property of the
instruction on its allowed states; it need not involve the state that just entered.
A heat bound additionally needs the input distribution and a physical model.''','Preserve central instruction/run/physics distinctions in conclusion.')
edit('conclusion_merge_credit',r'''and the price on a merge is Landauer's, as a
premise.''',r'''and the abstract merge price is motivated by Landauer's reset example. Identifying that
price with heat needs the further premises stated in Part II.''','Avoid equating abstract merge pricing with distribution-dependent Landauer bound.')
note(20,'Checked lift hypotheses, finite-lever obstruction versus grouping, seven-model translations and one-counter stopping proof. Correct effective-translation qualifier.')
note(21,'Checked composition claims against their projection, threshold, interface and simulation conditions. Clarify six-mark attainability is for suitable certificates, not arbitrary thresholds; nesting bounds are explicitly at matched certified points.')
note(22,'Checked compiler scope, runtime interpretation and certification claim. Correct source-versus-target record instruction statement; runtime figures remain reports about the particular implementation, not general model bounds.')
note(23,'Checked exact pinned-matrix test, rational strictness, quantum-versus-classical scope and earned PCHSH chain. The elliptope and larger matrix remain explicitly separate from the installed property; finite tallies are not hypothesis tests of quantum origin.')
note(24,'Checked unit conversion, structural dissipation premise, history lift and driven-reset arithmetic. Remove zero-heat inference from injectivity; preserve known-state and distribution qualifications.')
note(25,'Compared falsifiers to the claims they target. Correct pointer-thesis counterexample and clause-independence challenge; preserve premises for physics and machine refutations.')
note(27,'Reviewed scope chapter against theorem restrictions. No new edits required here; clean-start, window, encoding, physical and deployment limitations are already explicit.')
note(28,'Reviewed conclusion and propagated instruction/run distinction and abstract/physical pricing separation. Preserve central structural proposal and conditional mathematical results.')
note(30,'Reviewed assumptions, quantitative floor and telescoping proof. Correct merge-price/Landauer equivalence and control-dependent physical summary.')
note(32,'Checked classical, pinned matrix, integer clearing, Schur/Sylvester, 1+AB slice and elliptope arguments; compare quantum construction with previous standalone audit. Preserve explicit correlation-only and supplied-completion scope. No new numerical formula changes required.')
