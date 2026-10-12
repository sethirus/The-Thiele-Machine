for n in [65,69,77,83,90,91,92,93,94,102,103,104,107,123,128,130,134,143,144,152,153,172,174,202]:edit(n,'')
sub(60,'show in Coq, as I read their paper,','show, as I read their paper,')
edit(61,"It's the room again, once for every cup.")
regex(62,r",\nwhich is a sentence I'll come back.*?book is\.",'.')
regex(63,r"That's \\code\{[^}]+\}, which rules out a decider that says yes if and\nonly if a program admits a shortcut, stated for \\emph\{any\}\nsubstrate with those fields\.","This rules out a decider that says yes if and only if a program admits a shortcut,\nfor any substrate with those parts.")
sub(63,'the bare shape the class asks for','the mathematical structure just described')
sub(63,'The smallest checked\ninstance','The smallest\ninstance')
regex(63,r" \(The file's header.*?clean\.\)",'')
edit(64,r'The correctness ruled out is $d(p)$ true exactly when $A(p)$. Every part named above is a premise; the theorem is about every substrate that supplies them.')
regex(66,r'\(That one isn.t a separate theorem.*?did it\.\)',"(It's three lines and a pencil, and you just did it.)")
sub(67,'2017 as a model of computation in Coq','2017 as a model of computation')
regex(67,r'The development here builds.*?There,\n\\code\{L.*?\} is a theorem with a proof,',"Here L is built from its reduction rules. The recursion theorem is proved,")
sub(67,'the generic class\n(the class wants','the generic framework\n(that framework asks for')
regex(68,r'de Bruijn, who ran.*?sec:coq\};', 'de Bruijn;')
regex(70,r'That breaks.*?nothing else\.',"That breaks Rice's theorem for L, whose proof rests on the reduction rules.")
sub(71,'into Coq, small enough to check','into a mathematical model, small enough to examine')
sub(72,'a small Coq model','a small mathematical model')
regex(73,r'a transcription of a published Coq proof.*?with validator sets as predicates and', 'a reconstruction of the published casper-proofs argument from Runtime Verification\nand the University of Texas at Austin, based on Yoichi Hirai\'s proof, with validator sets and')
regex(73,r'\\code\{[^}]+\}: a finalization','A finalization')
regex(73,r'And\n\\code\{[^}]+\}: a one-validator','And\na one-validator')
edit(74,'The model takes quorum intersection and the accountable-safety setting as premises. Its guarantees are conditional on those premises.')
regex(75,r"That's \\code\{[^}]+\}, and \\code\{[^}]+\} is the other half:","The other half is this:")
edit(76,'The arithmetic follows the execution specification\'s storage instruction and gas table.\nThe end-of-transaction refund cap of one fifth is not in the fragment.')
edit(78,r'''The proof is Theorem~\ref{thm:perm-flip-merges} with permanence required only of the one instruction $i$.
For the second half: if the step were one-to-one on the states that read on together with $s$,
it would map the states that read on onto themselves, and then $s$ would land where some state
that reads on already lands.''')
edit(79,'Any Boolean claim about the retained digest can be read off the quote. But a scheme whose\nverification always says yes satisfies the sign-and-verify interface while accepting a\nsignature no key produced.')
regex(80,r'The checked work runs the\nRFC.s own examples.*?through a transcription',"The RFC's own examples, including the awkward lone-leaf case, can be run\nthrough a transcription")
edit(81,'The append-only history is list append: appending keeps every old entry.')
regex(82,r'Its formal shape is checked.*?nothing about them is proved\.', 'The schema takes the class, the reachable states, the certification event and the priced\nrecords as inputs; it proves nothing about which real systems satisfy them.')
sub(84,'a Coq observer\nmap','a mathematical observer\nmap')
regex(85,r' All of that is checked.*?The only renaming',' The only renaming')
sub(86,'I made fancy. For this construction I can reuse the two-counter result in the Coq Library of\nUndecidability Proofs. The halting reduction is their work; the step-for-step connection',"I made fancy. For this construction I use the two-counter result of Forster, Larchey-Wendling\nand coauthors. The halting reduction is their work; the step-for-step connection")
sub(87,'proved, with the\nproof checked in the Isabelle proof assistant, that','proved that')
regex(88,r'is real work,.*?The two-counter result in it is Larchey-Wendling.s, reached',"is real work. The construction used here is Larchey-Wendling's, reached")
edit(89,r'''Be precise about the reduction used below. A procedure deciding this halting question
would give a program listing the single-tape Turing machines that do not halt. Such a
listing cannot exist: halting runs can already be listed, and running the two listings
in parallel would decide halting. The undecidability statement below records that
reduction, so its meaning is in the connection between the two problems.''')
regex(95,r"The only answer I know\nthat works is de Bruijn.s .*?:",'The answer used here is simple:')
sub(96,'proved in the\nproof checker Isabelle/HOL, for','proved, for')
regex(97,r'The\nexact condition is \\code\{[^}]+\}:','The\nexact condition is this:')
regex(97,r' All of these\nare in.*?EarnedCore.v\.','')
edit(98,ps[98][ps[98].index("The version whose check can't"):])
regex(98,r' \(\\code\{min.*?\)', '')
sub(99,' The formal counterparts are in EarnedCore.v and EarnedCoreLinks.v.','')
edit(100,ps[100][ps[100].index('An interface over a language'):])
sub(101,'is a field of the interface','is a condition on the interface')
regex(101,r'Inside Coq with no extra\nassumptions.*?Hand the definition a checker like\nthat', 'For example, take a function that answers whether an arbitrary program runs forever.\nIt need not be computable. Hand the definition a checker like that')
regex(105,r'and its theorems are checked by Coq.*?for you\.',"and each case of its simulation argument has to hold. The definitions are on the page\nso you can examine what those cases establish.")
regex(106,r' \(\\code\{cg.*?UniversalPCodes.v\)', '')
edit(108,ps[108][ps[108].index('Part (3)'):])
regex(109,r' \(The Coq file.*?\$U\$\.\)', '')
edit(110,ps[110][ps[110].index('Three reservations'):])
edit(111,ps[111][ps[111].index("It's a checklist"):ps[111].index('The packaged form')].rstrip())
edit(112,ps[112][ps[112].index('Part (3)'):])
edit(113,ps[113][ps[113].index("It's a real narrowing"):])
edit(114,r'''The certifying comparison is $3 + 3\lambda < m$; the deciding comparison $1 + \lambda < m$
is arithmetic on the free lower bound and the one-move decider. '''+ps[114][ps[114].index('The exchange is sharper'):])
edit(115,'A property that depends only on the partial function a program computes, whether it stops\nand what it leaves in register 0, is extensional, so it is covered. That case also follows\nfrom the recursion theorem below.')
regex(116,r'I wrote that algorithm out in Coq, turned it into a term of the lambda calculus L, and\nran the library.s compiler from L to Minsky programs, which gives a program of two-counter\ninstructions that a host program can be read off from, instruction for instruction\. The tools\nsupply the program that computes the evaluator\.',"Express that algorithm in the lambda calculus L and apply the translation from L to\nMinsky programs established by Forster, Larchey-Wendling and coauthors. This gives a\nprogram of two-counter instructions that a host program can be read off from, instruction\nfor instruction. This construction supplies the program that computes the evaluator.")
edit(117,ps[117][ps[117].index('Be exact about one'):])
sub(118,'evaluator written out in Coq, turned into a term of L and compiled to Minsky programs','evaluator expressed as a term of L and translated to Minsky programs')
edit(119,'In the replay, the trap latch is up exactly when the fifth number is 1, and the flag\nexactly when the fourth is positive. Restricting the comparison to the computed function\ngives the usual fixed-point statement. '+ps[119][ps[119].index('Two limits'):])
edit(120,'The same obstruction holds for any machine with finitely many control states whose counters\nare read only through zero and parity above a threshold. It gives a computable transformation\n$F$ with no program $e$ equivalent to $F(e)$ on plain inputs.')
regex(121,r'with the toll proved: \\code\{[^}]+\}\n', 'with the toll proved\n')
regex(122,r'The Coq Library of Undecidability Proofs, built over\nseveral years by (.*?)proves in\nCoq that',r'The constructions developed over several years by \1show that')
sub(124,'The Coq definitions are drawings','The mathematical definitions are drawings')
sub(125,"once by Coq's own machinery and once by hand",'once generated from the formal definitions and once implemented separately')
sub(126,'Coq, extracted OCaml and Python agree on every tested step','the executable versions agree on every tested step')
sub(126,'run, extracted, against the Python guest','run, against a separate guest implementation')
edit(127,'The first executable is generated from the formal definitions. The second is written\nseparately from the same specification. Both implement the small machine, the host with a\nregister for every whole number, the host with PAY, the universal programs and the loaders.\nThe compiler below has an executable runner too.')
edit(129,r'''Whole numbers matter here. Machine words in one build are 63 bits wide, while the guest\ncodes $U$ reads go up near $2^{100}$, so ordinary fixed-width arithmetic would wrap around.\nThe mathematical machine has no such overflow. Its executable therefore uses unbounded\nintegers, with arithmetic chosen to match the definitions: subtraction stops at zero and\ndivision by zero returns zero. The mappings, compilers and input/output routines remain\nimplementation dependencies; testing them does not change the mathematical definitions.''')
edit(131,'A run shows what a build did on those inputs. Comparing two implementations step by step\ncan expose a disagreement with the specification; agreement on tested runs leaves other\nruns open.')
regex(132,r'Against Coq itself,.*?The same|Against Coq itself,.*?They agree on every step of every\none\.', 'The comparison covers exhaustive sets of short programs, random programs, both hosts and\nthe small guests listed below. They agree on every tested step.')
edit(133,"A shared mistake can survive both implementations. The comparison doesn't test whether\nthe definitions say the right thing, since both implementations follow them. That's what\nhaving the definitions and arguments on the page is for.")
sub(135,'(the Coq function that gets extracted)','(the bounded evaluator of the compiled host program)')
edit(136,"The statement says nothing about how many steps the compiled program takes. It's about answers.")
regex(137,r'Each answer is compared.*?Ackermann.s function',"Answers are compared with direct arithmetic and separate interpreters of the source and\ncompiled programs. Ackermann's function")
sub(137,'The runner and the compiler are extracted','The runner and the compiler are implemented')
sub(137,'The extracted runner','The executable runner')
sub(138,'as Coq definitions, as extracted OCaml, and as a Python program written by hand, and those three\nagree on every step anybody has checked','as mathematical definitions and executable implementations that\nagree on every tested step')
regex(139,r'full equivalence,.*?the last part of this section states it\.', 'full equivalence, in the form that speaks of the four averages, appears in the last part of this section.')
regex(140,r'\(\\code\{[^}]+\}, TsirelsonAlgebraic.v; the next part says how\)', '(the next part says how)')
edit(141,r'Theorem~\ref{thm:chsh-check-sound} and Corollary~\ref{cor:chsh-iff} in the appendix give the two directions.')
edit(142,r'This is Theorem~\ref{thm:chsh-psd-tsirelson} in the appendix.')
edit(145,"That's the one thing the\nmachine does with the check, as the section's opening said: a raised flag can stand on it. Five\ntallies, each a theorem with its counts written out, show the check isn't vacuous and where its\nedges are.")
regex(146,r'\(\\code\{[^}]+\},\nQuantumPartitionPSD.*?1AB.v\)', '')
regex(146,r'\(\\code\{[^}]+\}, S equals', '(S equals')
regex(147,r'\n\(\\code\{[^}]+\}, checked by computation\)', '')
regex(147,r'\n\(\\code\{[^}]+\} for real amplitudes and \\code\{[^}]+\} for complex,\nTsirelsonRepresentation.v\)', ', for both real and complex amplitudes')
regex(148,r' \(\\code\{[^}]+\} in the source\)', '')
sub(149,"There's a function in the source that multiplies the counter by a chosen energy per mark,",'Multiply the counter by a chosen energy per mark,')
regex(149,r'\(@.*?\)', '') if False else None
regex(149,r'\(\\code\{[^}]+\}, proving the predicate \\code\{[^}]+\} for\nevery k and T\)', 'for every k and T')
sub(149,'true with the scale set to a dollar a mark. I\'d say that out loud, so the name\n``Landauer\'\' in it does no work.','true with the scale set to a dollar a mark.')
regex(149,r'\\code\{landauer[^}]+\}, and that one is an assumption with a name that nothing proves\.',"Landauer's principle, which is a physical premise.")
edit(150,ps[150][ps[150].index('The physics is the premise'):])
regex(151,r"That's checked as.*?\. The machine",'The machine')
regex(154,r'the formal statement it cites \(Appendix.*?easy\)\.', 'the mathematical statement and argument it refers to.')
challenge_names={
'universal_nfi_any_substrate':'the universal floor',
'permanent_flip_is_not_injective':'the permanent-flip theorem','permanent_flips_compression_bound':'the squeeze bound','flip_merges_or_revokes':'the merge-or-revoke claim','fin_merging_priced':'merge pricing on that machine',
'permanent_step_entropy_ceiling':'the entropy ceiling','entropy_drop_pos_of_support_merge':'the strict entropy-drop claim','landauer_heat':"of Landauer's principle",'known_state_flip_forces_no_heat':'the known-state argument',
'observer_narrowing_can_be_free':'the free-learning example','mu_conservation':'conservation','nec_f_initiality':'the uniqueness argument','shadow_cannot_price_exactly':'the window-pricing obstruction',
'ent_representation':'the entitlement bound','ent2_uncovered_claim_false':'the uncovered-narrowing counterexample','ent2_questions_cap':'the sixteen-check ceiling','ent2_free_cannot_decide_fast':'the free-step lower bound',
'record_axis_is_latch_holds':'the latch theorem','L_recursion_theorem':"L's recursion theorem",'sm_host_rice':"Rice's theorem for the host",'sm_kleene':"its recursion theorem",'sm_guest_rice':"the fixed-input Rice theorem",'tc_rice':"the all-input Rice theorem",'tc2_no_mult':'the multiplication obstruction','sm2_kleene_obs':'the fixed-point theorem for the record',
'earned_certification_provenance':'certification provenance','earned_commitment_provenance':'commitment provenance','no_forging':'the no-forging claim','certified_run_min_cost':'the minimum-price theorem','simulation_step':'the step correspondence','halting_correspondence':'the halting correspondence',
'complete_has_free_move':'the free-move requirement','clock_not_thiele_complete':'the exclusion of clocks','complete_no_record_oracle':'the window obstruction','paid_latch_not_thiele_complete':'the exclusion of the paid latch','silent_not_thiele_complete':'the exclusion of the silent machine',
'universal_halting':'the halting equivalence','universal_flag_iff':'the flag equivalence','universal_ledger_exact':'the ledger equality','universal_earned':'the earned-chain guarantee',
'presented_universal_flag_iff':'the reading equivalence','presented_universal_surcharge_le_two':'the surcharge bound','presented_universal_no_exact_below_three':'the lower bound of three',
'chsh_violation_rules_out_locally_factorizable_coupling':'the classical bound',
'npa_psd_iff_column_contractive':'the matrix equivalence','npa_psd_implies_tsirelson_bound':'the bound on the score','small_chsh_flag_implies_tsirelson':'the earned game-check guarantee','small_chsh_check_iff':'the exact integer-check equivalence',
'q1ab_psd_iff_column_contractive':'the nine-by-nine equivalence','q1ab_check_at_gzero_implies_classical_bound':'the zero-extras bound',
'deterministic_strategy_elliptope':'the inclusion of deterministic plans','elliptope_tsirelson':'the completion bound','pr_box_not_elliptope':'the exclusion of the PR box','elliptope_check_full_sound':"the decider's soundness",'turing_point_elliptope':'the displayed completion'
}
for n in range(155,172):
 t=ps[n]
 def word(m):
  name=m[1].replace(r'\_','_');assert name in challenge_names,name
  return challenge_names[name]
 t=re.sub(r'\\code\{([^}]+)\}',word,t)
 t=t.replace("the file's own pair of\ncounterexamples. The file built those already.","the two counterexamples already given.")
 t=t.replace('the file\nalready builds one of each','the chapter\nalready builds one of each')
 t=t.replace('is checked over any counter machine as\nthe uniqueness argument', 'holds over any counter machine')
 t=t.replace("the premise\nof Landauer's principle for that device, which is Landauer's principle", "Landauer's premise for that device")
 t=t.replace('(the displayed completion for the second)','')
 t=re.sub(r'(?<=[.!?]) (the |conservation|certification provenance|commitment provenance|merge pricing)',lambda m:m[0][0]+m[0][1:].capitalize(),t)
 edit(n,t)
sub(173,'two-counter machines and the Coq library that proves their halting undecidable and compiles','two-counter machines and the constructions that prove their halting undecidable and compile')
sub(173,"Michael Norrish's in HOL4, Mario Carneiro's in\nLean, and Yannick Forster, Fabian Kunze and Gert Smolka's in Coq.","Michael Norrish's, Mario Carneiro's, and Yannick Forster, Fabian Kunze and Gert Smolka's.")
sub(173,'verified in Coq\n','proved correct\n')
regex(175,r'\(textbook, Halmos;.*?NecTPartition.v\)', '(textbook, Halmos)')
regex(176,r'; \\code\{nec.*?NecWArgued.v\)', ')')
sub(177,"(the book's word; Coq has no such term)","(the book's word)")
regex(178,r'\(\\code\{generic.*?EarnedGeneric.v\)', '')
regex(179,r'proved: \$S\^2 \\le 8\$.*? & Section~', r'proved: $S^2 < 8$, with passing tallies as close to 8 as desired & Section~')
regex(179,r'\(\\code\{q1ab.*?1AB.v\)', '')
sub(179,r'\code{fine\_theorem} as stated','the single-bound statement')
regex(179,r'proved; earned CHECK integration: \\code\{[^}]+\}', 'proved, including the earned CHECK')
sub(179,"The theorems prove physical reality, or Coq's consistency & not claimed & Section~\\ref{sec:coq}",r'The theorems prove physical reality & not claimed & Section~\ref{sec:landauer}')
regex(180,r', checked as\n\\code\{[^}]+\}', '')
sub(181,"The proofs also use Coq's whole numbers",'The mathematical machine uses whole numbers')
sub(182,'borrowing their undecidable halting from the Coq library','using the halting reduction of Forster, Larchey-Wendling and coauthors')
regex(183,r' \(\\code\{[^}]+\} and its neighbours\)', '')
sub(184,'verified in Coq for monitors','proved for monitors')
edit(185,r'''``Kernel'' has two uses here. In mathematics, the kernel of a map is what it sends to the
identity; for a projection the useful version is the relation ``these two states project
to the same thing.'' An operating-system kernel is the core of an operating system, as in
the packet-filter example in Section~\ref{sec:models}.''')
sub(186,'built in Coq','presented')
regex(187,r'and a price list, \\code.*?; on my machine the sum is a checked theorem too,', 'and a price list; on my machine the sum is a theorem too,')
edit(188,r'''\begin{definition}[Certification system]\label{def:app-certsys}
A certification system consists of a set of states $S$, a set of moves $I$, a step function
$\mathrm{step}: S\times I\to S$, a cost $\mathrm{cost}:I\to\mathbb{N}$, and a reading
$\mathrm{cert}:S\to\{\mathrm{no},\mathrm{yes}\}$, satisfying the toll: every move that
turns the reading from no to yes costs at least one. This is the condition of
Section~\ref{sec:toll}, called A2 in the table below. Every result stated ``for any
certification system'' assumes it.
\end{definition}''')
edit(189,r'''\begin{definition}[Quantitative certification system]\label{def:app-qcs}
A quantitative certification system is a certification system with a \emph{witness},
a function $W$ from states to $\mathbb{N}$, and a threshold $N \in \mathbb{N}$, satisfying:
(A3) $W(s) + \mathrm{cost}(i) \ge W(\mathrm{step}(s, i))$, the witness grows by at most
what the move cost; and (A5) a state that reads yes has $W(s) \ge N$.
An optional additional condition is (A4) $W(s) \le W(\mathrm{step}(s, i))$.
\end{definition}''')
for name in re.findall(r'\\code\{([^}]+)\}',ps[190]):
 regex(190,r': (?:field|a hypothesis of) \\code\{'+re.escape(name)+r'\}(?: of (?:\\code\{[^}]+\}|the full record))?', '') if (': field \\code{'+name+'}') in changes.get(190,ps[190]) or (': a hypothesis of \\code{'+name+'}') in changes.get(190,ps[190]) else None
sub(190,'In the certification records','Condition')
t=ps[191];lines=[]
for line in t.splitlines():
 if ' & ' in line:line=line.rsplit(' & ',1)[0]+r' \\'
 lines.append(line)
t='\n'.join(lines).replace(r'p{0.233\linewidth}>{\raggedright\arraybackslash}p{0.221\linewidth}>{\raggedright\arraybackslash}p{0.221\linewidth}>{\raggedright\arraybackslash}p{0.221\linewidth}',r'p{0.22\linewidth}>{\raggedright\arraybackslash}p{0.35\linewidth}>{\raggedright\arraybackslash}p{0.35\linewidth}')
edit(191,t)
sub(192,'Second, the class\n\\code{Substrate}  carries a different rule from the toll, \\code{mu\\_monotone}: the counter','Second, the substrate used for the diagonal also carries a different rule from the toll: the counter')
sub(193,'machine, here Coq','machine')
# Keep attribution of known results and the classification of contributions accurate.
for n in [194,195,196,197,198,199,200]:
 t=ps[n]
 t=t.replace('Coq-checked extension','extension')
 t=t.replace('proved in Coq','proved').replace('verified, in Coq,','verified')
 t=t.replace('checked in the Coq\nLibrary of Undecidability','established by Forster, Larchey-Wendling and coauthors')
 t=t.replace('checked in the Coq Library of Undecidability','established by Forster, Larchey-Wendling and coauthors')
 t=t.replace('coauthors in Coq, including L itself, 2017, and\nthe Coq Library of Undecidability','coauthors, including L itself, 2017, and\ntheir library of undecidability results')
 t=t.replace('; I found no mechanization of Landauer\'s principle in Coq,\nIsabelle, or Lean','')
 t=re.sub(r'\\code\{complete\\_hides\\_record\}; ', '',t)
 edit(n,t)
edit(201,r'''This appendix supports Section~\ref{sec:chsh}. That section tells the story; this one does
the algebra. Each item gives the statement with its hypotheses and the steps needed to
check it. Nothing here identifies an arbitrary matrix with a physical state. Where quantum
strategies enter, their relationship to the matrices is stated explicitly.''')
regex(203,r'Eight counts sit in the record \\code\{[^}]+\}\n: for each', 'There are eight counts: for each')
edit(204,r'''A matched round contributes $ab = +1$ and a differing round $ab = -1$, so $D_{xy}$ is the sum
of the products and $D_{xy}/N_{xy}$ is their average. Since $|D_{xy}| \le N_{xy}$, every
correlator from counters lies in $[-1,1]$. When a bucket is empty, its correlator is defined
as 0. The score is $E_{00}+E_{01}+E_{10}-E_{11}$.''')
edit(205,r'''The same bound follows by checking the sixteen sign cases. For rational-valued functions
$f_A,f_B:\mathbb{N}\to\mathbb{Q}$ whose values are $\pm1$, the absolute value of
$f_A(0)f_B(0)+f_A(0)f_B(1)+f_A(1)f_B(0)-f_A(1)f_B(1)$ is at most 2.
The real-valued version has the same bound.''')
regex(206,r', \\code\{[^}]+\}', '')
regex(207,r'\[\\code\{[^}]+\}, one direction only\]', '[The classical bound for a finite local model]')
regex(207,r'\n\(kernel/quantum/MinorConstraints.v; restated as \\code\{[^}]+\}\)\.', '.')
edit(208,r'''\begin{remark}[Scope of the classical bound]\label{rem:chsh-fine-scope}
Fine's 1982 theorem is an equivalence between several descriptions of local models and the
Bell inequalities. The preceding theorem proves one direction: a finite factorizable model
obeys the bound. The converse of this single inequality is false. The correlation-form
equivalence requires each correlator to lie between $-1$ and $1$ and all eight inequalities.
The preceding theorem covers finitely many hidden states ($\lambda\le\lambda_{\max}$),
not an arbitrary probability space. It applies to rational boxes as well: if their
correlations form a factorizable model, their rational score has absolute value at most 2.
\end{remark}''')
regex(209,r'\[\\code\{[^}]+\}\]', '[A tally consistent with one local plan]')
sub(210,r'\code{chsh\_stat\_from\_wc} $w$', '$S(w)$')
regex(210,r'This is \\code\{[^}]+\}\n\. A stronger companion,\n\\code\{[^}]+\}, states that','A stronger statement is that')
for n in [211,216,220,221,223,238,239,240,243,257,259,260,261,263]:
 regex(n,r', \\code\{[^}]+\}(?=\])','') if re.search(r', \\code\{[^}]+\}(?=\])',changes.get(n,ps[n])) else None
for n in [211,239]:regex(n,r'\([^\n]*?\.v, closed by \\code\{ring\}\.\) ?', '')
regex(212,r';\nthis is \\code\{[^}]+\}\.', '.')
regex(213,r'This is.*?The absolute form', 'The absolute form')
regex(213,r' is\n\\code\{[^}]+\}\.', ' follows.')
regex(214,r' This is.*?\.\n', '\n')
regex(215,r'The step about where equality.*?Equality \$S', 'Equality $S')
edit(217,r'''\begin{definition}[The pinned level-1 matrix]\label{def:chsh-five}
Set all four one-party entries and both within-party entries to zero. On rows and columns
$I,A_0,A_1,B_0,B_1$, the resulting matrix is:
\end{definition}''')
edit(218,r'''Positive semidefiniteness is defined by quadratic forms: $v^{\mathsf T}Mv\ge0$ for every
$v\in\mathbb{R}^5$. The matrix here is also symmetric. In block form,''')
regex(219,r'The lemma is checked in general form,.*?the\nforward direction', 'The identity and implication hold for finite index sets and any symmetric $P$ with a\nsymmetric inverse; the forward direction')
sub(222,r'\code{PSD5} holds of $M(E)$','$M(E)$ is positive semidefinite')
regex(222,r'\nThis is.*?\.\n','\n')
regex(224,r' \(The Coq proof.*?\)', '')
sub(225,r'\code{PSD5} holds of $M(E)$','$M(E)$ is positive semidefinite')
regex(225,r' This is\n\\code\{[^}]+\}\.', '')
regex(226,r'; their values are the lemmas.*?\.', '.')
edit(227,r'''\begin{corollary}[The equivalence]\label{cor:chsh-iff}
For all real $E_{00},E_{01},E_{10},E_{11}$, the symmetric matrix $M(E)$ is positive
semidefinite if and only if the correlators are column contractive.
\end{corollary}''')
edit(228,r'''\begin{theorem}[PSD implies Tsirelson]\label{thm:chsh-psd-tsirelson}
If the pinned matrix $M(E)$ is symmetric and positive semidefinite at
$E_{00},E_{01},E_{10},E_{11}$, then $S^2\le8$ and $|S|\le\sqrt8$.
\end{theorem}''')
regex(229,r'\\code\{[^}]+\}  says a symmetric PSD','A symmetric PSD')
regex(229,r'This is\n\\code\{[^}]+\}\. Then','Then')
regex(229,r'applies, through \\code\{[^}]+\}\n\.', 'applies.')
regex(230,r'\(item G, \\code\{[^}]+\}\)', '(item G)')
regex(230,r'\(\\code\{qs.*?twice the length\)', '(with complex amplitudes, use real vectors of twice the length)')
sub(230,r'is \code{tr\_representation}: the strategy','comes from this construction: the strategy')
regex(231,r'\[\\code\{[^}]+\}\]', '[The seven-integer check]')
edit(232,'The check has the following guarantee:')
edit(233,r'''\begin{theorem}[Soundness of the integer check]\label{thm:chsh-check-sound}
If a tally $w$ passes the seven-integer check, then its four correlators
$E_{xy}=D_{xy}/N_{xy}$ are column contractive. Consequently its pinned matrix is positive
semidefinite.
\end{theorem}''')
regex(234,r'If \\code\{[^}]+\} \$w\$ = \\code\{true\}', 'If a tally $w$ passes the seven-integer check')
regex(234,r'On the small machine.*?Section~', 'For the earned form on the small machine, see Section~')
edit(235,r'''The five additional parameters name the moments
$\gamma_1=\langle A_0 A_1 B_0\rangle$,
$\gamma_2=\langle A_0 A_1 B_1\rangle$,
$\gamma_3=\langle A_0 B_0 B_1\rangle$,
$\gamma_4=\langle A_1 B_0 B_1\rangle$ and
$\gamma_5=\langle A_0 A_1 B_0 B_1\rangle$.
These are labels for the entries; the definition below does not construct operators.''')
regex(236,r'\[\\code\{[^}]+\}\]', '[The level-1+AB matrix]')
regex(236,r'\(kernel/quantum/QuantumPartitionPSD.*?1AB.v\) ', '')
sub(236,'with the entries exactly as\nthe Coq definition places them:', 'with the following entries:')
regex(237,r', guarded by\n\\code\{[^}]+\} \(QuantumPartitionPSD.*?1AB.v\)', '')
regex(237,r'\n\(\\code\{[^}]+\}, QuantumPartitionPSD.*?1AB.v\)', '')
regex(237,r'Symmetry is\n\\code\{[^}]+\}\.', 'The displayed matrix is symmetric.')
regex(238,r'\(QuantumPartitionPSD.*?1AB.v\)\n', '')
sub(238,r'The predicate \code{column\_contractive\_q1ab} says', 'The condition called column contractivity at level 1+AB is')
regex(240,r'\(QuantumPartitionPSD.*?1AB.v\) ', '')
regex(240,r'\\code\{PSD9\} of the matrix of Definition.*?holds\. The directions are.*?\.',r'the matrix of Definition~\\ref{def:chsh-nine} is positive semidefinite if and only if\nthe residual $R$ is nonnegative for every choice of its six real inputs.')
edit(241,r'''As a quadratic form in $(v_{B_0},v_{B_1},v_{00},v_{01},v_{10},v_{11})$, numbered 1 to 6,
the residual has the symmetric coefficient matrix $H$ with these upper entries. Each entry
can be read back off $R$ by collecting the coefficient of $v_i v_j$.''')
regex(242,r'The instances used are.*?\.\n', 'The cascade uses this identity at sizes six and five.\n')
regex(243,r'\(QuantumPartitionPSD.*?1AB.v\) ', '')
regex(243,r' \(\\code\{[^}]+\} to \\code\{[^}]+\}\)', '')
regex(244,r'\\code\{[^}]+\} \(closed by \\code\{ring\}\) is the fraction-free factorization','Use the fraction-free factorization')
regex(245,r'The\nreal predicates are.*?\.', 'Together these conditions make the residual nonnegative and hence the nine-by-nine matrix positive semidefinite.')
sub(246,'buckets the source swaps them','buckets the letters name numerator and denominator')
sub(246,"I keep the source's letters so the names below match the files. ", '')
regex(246,r' \(\\code\{[^}]+\} to \\code\{[^}]+\}\)', '')
sub(246,r'\code{schur\_step\_Z}, ', '')
sub(246,r'decider \code{q1ab\_g12345\_check\_z\_kernel} is','decider is')
sub(246,r'\code{q1ab\_g12345\_full\_integer\_check\_kernel} is \code{column\_contractive\_check\_witness} of item', 'combines the seven-integer check of item')
sub(246,'E and this decider.','E with this decider.')
regex(247,r'The bridge lemmas,.*?prove that each cleared integer', 'Each cleared integer')
sub(248,r'\code{q1ab\_g12345\_check\_z\_kernel}', 'the decider just defined')
regex(248,r'and \\code\{PSD9\}\. This is.*?1AB.v\)\.', 'and positive semidefinite.')
sub(249,r'\code{PSD9}', 'positive semidefiniteness')
regex(250,r'A worked example.*?\. Take the correlators', 'A worked example of the cascade in exact rational arithmetic. Take the correlators')
regex(251,r'That last fact is general.*?\$E_\{00\}', 'That last fact is general. The zero-moment check takes no $\\\\gamma$ buckets; it combines\nthe level-1 check with the integer form of\n$E_{00}')
regex(252,r'If \\code\{[^}]+\} \$w\$ = \\code\{true\} \(QuantumPartitionPSD.*?function\),', 'If the zero-moment check accepts a tally $w$,')
regex(253,r'\\code\{q1ab[^}]+\} \(QuantumPartitionPSD.*?1AB.v\) proves \\code\{PSD9\}\nat', 'The matrix is positive semidefinite at')
sub(253,r'condition \code{q1ab\_g5\_caller\_witness} asks','condition asks')
regex(253,r'The\ninteger version, \\code\{[^}]+\}, runs', 'The\ninteger version runs')
sub(253,r'\code{true}', 'yes')
sub(254,r'\code{column\_contractive\_check\_witness}', 'the seven-integer check')
sub(254,"That is a composition I did by reading\nthe definitions; the source has no single theorem stating it.",'This follows directly by composing the definitions and the bound.')
sub(255,r'\code{completed\_npa}  is the record of item D','Complete the matrix of item D')
sub(255,'with the\nwithin-party entries set to free reals:', 'by setting the\nwithin-party entries to free reals:')
regex(256,r': \\code\{[^}]+\}\.', '.')
edit(258,r'''The all-ones plan is one instance. The classical mixture $(1,0,1,0)$ has a completion at
$x=1$, $y=0$, with form $v_0^2+(v_1+v_2+v_3)^2+v_4^2$.''')
sub(262,r'\code{elliptope\_pd\_check}:','The positive-minor branch:')
sub(262,r'\code{elliptope\_ldl\_check}:','The factorization branch:')
sub(262,r'\code{elliptope\_check\_full} is','The full gate is')
sub(263,r'\code{elliptope\_check\_full} returns \code{true}', 'the full gate returns yes')
sub(263,r'And \code{elliptope\_full\_gate\_never\_accepts\_pr\_box}: on','On')
sub(263,r'\code{false}', 'no')
edit(264,r'''Examples by direct computation: the all-ones plan passes through the factorization branch
at $x=y=1$; the classical mixture $(1,0,1,0)$ passes; the $12/5$ point passes through the
positive-minor branch at $x=y=0$; and $(3/5,4/5,4/5,-3/5)$ passes through the factorization
branch with pivots $(1,1,0,0)$.''')
sub(265,'is checked in ArcsineBoundary.v as','holds as')
regex(266,r'\\code\{[^}]+\} for real amplitudes and \\code\{[^}]+\} for complex\nones', 'for both real and complex amplitudes')
sub(267,'measurements that reach it are built in QuantumStrategies.v:', 'measurements that reach it are explicit:')
regex(268,r'\(\\code\{[^}]+\}, Theorem~','(Theorem~')
regex(268,r'The comment in ElliptopeGate.v.*?the\nfour 1\+AB checks accept nested sets\.',r'The assertion that the factorization branch accepts every rational PSD completion needs\na completeness argument for its rational certificates; no such argument is supplied here.\nNor is it shown that the four 1+AB checks accept nested sets.')
sub(269,'proved again here in Coq','proved again here')
sub(269," (tsirelson\\_\\allowbreak{}inequality in Mathlib.Algebra.Star.CHSH)",'')
sub(270,'whose Coq development of L','whose construction for L')
sub(270,'with\nevery step checked on the standard library','with\nthe reductions written out')
regex(272,r' The companion names are.*?identify\.', '')
