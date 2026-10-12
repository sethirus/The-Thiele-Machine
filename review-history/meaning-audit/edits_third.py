from audit import edit,note
edit('test_lower_bound_reference','I argue that; nothing checks it.','Theorem~\\ref{thm:time-tax} gives the precise lower bound and the matching ladder.', 'Replace unsupported-proof disclaimer with actual book proof.')
edit('mirror_program_own_flag',r'''So this
host runs any guest by construction and keeps the guest's record by theorem, as a copy of the
guest's flag. It never earns a flag of its own.''',r'''So this
host runs any guest by construction and keeps the guest's record by theorem, as a copy of the
guest's flag. The mirroring program $U_0$ does not earn the host's own flag; a different program
could do so with the host's OWN CHECK, COMMIT and CERTIFY.''', 'Scope non-earning to program U0, not host instruction set.')
edit('time_tax_trace_bill',r'''(3) The paid chain of three instructions raises the flag exactly when $A \ge m$ and has a ledger of
exactly 3, whatever $m$ is.''',r'''(3) Executed as a three-move trace from $\mathrm{start}(a,b)$, the paid chain raises the flag exactly when $a \ge m$ and has a ledger of
exactly 3, whatever $m$ is. As a stored program it pays 3 on success and stops after its first failed CHECK with a ledger of 1.''','Distinguish fixed trace costs from early-stopping program costs.')
edit('time_tax_program_length', '(2) A program of $m$ DECs and INCs (a ladder:', '(2) A program of $m$ DEC/INC pairs (a ladder:', 'Ladder contains 2m instructions, observed after m moves; do not conflate code length and runtime.')
edit('floor3_ends_up', 'every run from a state that raises the flag costs at\nleast three exactly when', 'every run from a state that ends with the flag up costs at\nleast three exactly when', 'Floor includes zero-length run of already-certified state, rather than requiring a crossing.')
note(19,'Compared all extracted definitions, theorem statements and proofs with adjacent claims, including clean starts, exact prices, simulation points, language-first interfaces, interpreter surcharge, host mirrors, diagonals and counter obstruction. Correct host-versus-program statement, trace-versus-program charge, ladder code length and floor wording; preserve explicit limits on runtime, bare inputs and claim semantics. This is a mathematical/editorial review, not independent execution of every universal interpreter or certification of every proof script.')
