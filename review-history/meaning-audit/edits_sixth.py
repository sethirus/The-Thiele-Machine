from audit import edit,span,note
edit('front_interface_scope','that no reading makes Thiele-complete', 'that no interface makes Thiele-complete', 'The machine reading is fixed; exclusion quantifies over interfaces.')
edit('front_physics_table', 'a known state\'s reset has no Landauer floor under control timed from outside; time-symmetric control charges every nonreciprocal move', 'the entropy-loss bound is zero for a point-mass input; further work bounds depend on control, reliability and input distribution', 'Propagate correct time-symmetry and entropy scope to comparison table.')
edit('front_irreversibility_table','a step with no way back has a logarithmic entropy floor', 'absolute-irreversibility bounds require forward and reverse path probabilities', 'Logical noninvertibility alone does not specify absolute irreversibility.')
edit('front_kolmogorov', 'the structure in an object is the length of the\nshortest program that prints it.', 'the description complexity of a string is the length of the\nshortest program that prints it, relative to a fixed description language.', 'Do not identify arbitrary structural organization with algorithmic complexity.')
edit('front_toll_merge',r'''where
the toll's commit is a deterministic merge that stays.''',r'''where
the toll prices a deterministic no-to-yes transition. Finiteness and permanence are the
additional conditions that force its instruction to merge states.''','Bare toll does not itself require permanence or noninjectivity.')
edit('glossary_shifts','A shift moves\nevery bit left or right, which multiplies or divides by a power of two.', 'A logical shift moves\nbits left or right: for unsigned values it multiplies or divides by a power of two,\ndiscarding overflow on a fixed-width left shift and rounding down on a right shift.', 'Qualify finite-width and unsigned arithmetic.')
edit('glossary_simulation_encoding', 'a Turing machine simulates any system of the model\nwhose step a program can compute, my machine included, by writing the whole state out on its tape,', 'a Turing machine can simulate a system with effective finite encodings of its states and moves\nand a computable step on those encodings, my small machine included, by representing its state on tape,', 'Computable presentation needs encodable states, not merely an abstract step.')
edit('glossary_instance_simulation', 'it\'s an instance of the\nmodel, and it simulates nothing.', 'it directly satisfies the\nmodel\'s rule. Whether it also simulates another machine is a separate question.', 'Being an instance does not preclude simulation.')
edit('glossary_landauer_average', 'gives off\nat least Boltzmann\'s constant times the temperature times the natural log of two in heat per\nbit.', 'gives off mean heat\nat least Boltzmann\'s constant times the temperature times the natural log of two per bit,\nunder a physical model relating that logical entropy to the memory\'s thermodynamic entropy.', 'Propagate ensemble heat and physical model condition.')
edit('glossary_recursion_equivalence', 'some program behaves exactly like its own\ntransform.', 'some program computes the same partial function as its own\ntransform. Its timing, storage and records need not agree.', 'Functional fixed point is not full operational equivalence.')
edit('glossary_crypto_hash', 'A hash is a short fingerprint of a longer piece of data, made so', 'A cryptographic hash is a short fingerprint of a longer piece of data, made so', 'Collision resistance belongs to cryptographic hashes, not every hash function.')
edit('glossary_early_parts', 'Parts I to III live there, and every claim in them\nis about any system with the pieces it names.', 'Parts I to III develop those general arguments, alongside particular examples\nand applications to the later machine.', 'Avoid false blanket claim that earlier parts contain only general results.')
edit('glossary_property_forms','the properties come from a fixed language of three,', 'the properties come from a fixed language with three forms,', 'Ge(n) denotes infinitely many properties, not one of three total properties.')
edit('contributions_reverse_scope',r'''The match is a mirror image. It isn't a special case of their bound: the squeeze is ordinary Landauer heat, whose logarithm
equals their bound for the free expansion that undoes it, and absolute irreversibility reaches
the commit itself only on a fixed-rate device starting from a known state.''',r'''The logarithms coincide for the stated counts. This does not supply a physical reverse
process: absolute irreversibility needs forward and reverse path probabilities that the
logical map alone does not specify.''','Propagate corrected thermodynamic-reversal comparison.')
edit('contributions_price_scope','and the price is\nLandauer\'s, as a premise).', 'and the price is\nan abstract premise motivated by Landauer\'s reset).', 'Separate adopted abstract price from physical law.')
edit('contributions_memory_scope',r'''An ordinary programmable computer, as built, doesn't do this for the programs it runs, because
the code beside a program shares its memory and can flip anything; $U$ is a fixed interpreter
that does.''',r'''Code that shares unprotected memory with a record can overwrite it. Ordinary computers
can also isolate memory and enforce rules through monitors. The claim here is the specific
simulation and record guarantee proved for the fixed interpreter $U$.''','Avoid false universal assertion that conventional programs can access all memory.')
edit('contributions_structural_question',r'''What's mine is the question (should an
account of computation carry what was certified and what certifying cost, as part of how it
steps),''',r'''The question organizing this book is what structural relations an account of computation
should carry in its state and step, with certification and its price as the worked case,''','Keep broad proposal distinct from selected certification example; avoid claiming priority on general question.')
# Add the two middle chapters' principal results to the ledger, using existing labels.
old=r'''A growing record is a family of latches & definition; proved, and one latch isn't enough & Section~\ref{sec:latch}, Definition~\ref{def:u11-growing}, Theorem~\ref{thm:u11-growing} \\'''
new=old+r'''
A chain of $n+1$ stages needs $n$ write-once Boolean cups & proved; ordinary rewritable binary storage is a different question & Section~\ref{sec:direction}, Theorem~\ref{thm:dir-bits} \\
A window can price rises exactly without determining the record value & proved, under the collision and decidability conditions stated there & Section~\ref{sec:shadow-exact}, Theorem~\ref{thm:dir-window} \\
With an injective shadow step, merged states lie in one shadow fibre & proved; the shadow-injectivity premise is needed & Section~\ref{sec:shadow-exact}, Theorem~\ref{thm:dir-fibre} \\
Halving pricing bounds weighted conditional entropy; an infinite landing pile admits no finite halving price & proved; average loss still depends on the distribution & Section~\ref{sec:shadow-exact}, Theorems~\ref{thm:dir-bits-loss} and~\ref{thm:dir-infinite} \\'''
edit('ledger_direction_shadow',old,new,'Add missing principal results of direction and exact-shadow chapters to claim ledger.')
note(3,'Reviewed definitions of layers, computing power, universality and comparison tables. Correct interface quantifier, physical summary, Kolmogorov wording and deterministic-merge scope.')
note(4,'Rechecked origin chapter in light of preceding full prose audit. Historical development is presented as author experience, with early engine explicitly a simulation, not a derivation of physics. No change needed.')
note(26,'Compared claim-ledger summaries against theorem premises across the book. Propagate pricing strength, refinement quantifier, observed-output restriction and nat-family quantifier order; add omitted direction and exact-shadow principal results.')
note(29,'Reviewed glossary against body definitions. Correct ensemble heat, encoding requirements, simulation versus instance, functional recursion, shifts, property forms and cryptographic hash scope.')
note(31,'Reviewed contribution statements for stronger restatements and priority claims. Correct reverse-process analogy, abstract price identification and conventional memory-isolation overclaim; keep structural proposal broader than certification.')
note(33,'Read Scott numerals, builders, guarded call-by-value recursion and quotation induction. They supply the pieces used by the diagonal construction; no new edit required.')
note(34,'Read tangible and symbolic tape, counter, prime-packing, FRACTRAN, partial-recursive and L constructions. Encodings, halting correspondence and variable cost remain explicit. No new edit required.')
note(35,'Read block definitions, register layout, instruction numbering, paid sites and simulation invariants; compare with preceding standalone block-expansion verification. No block or arithmetic edit required.')
note(36,'Read brief methodology note. It correctly limits proof-assistant role; no authority claim inserted into the argument.')
note(37,'Reviewed source-list role, internal references and entries implicated by the semantic corrections; retrieved Riechers et al. primary paper for its disputed bound. This pass does not independently reauthenticate every historical quotation, biography, bibliographic entry or URL; earlier source caveats remain.')
