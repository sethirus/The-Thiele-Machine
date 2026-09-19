# Rotated selector candidate and precise missing executable protocol

This is external candidate algebra, not B2c closure or a proved VM macro.

Let A=u-v, B=a-b, T=u+v+a+b+1. Set witness buckets:

- 00 same=8u+2v+9a+b+5, diff=2u+8v+a+9b+5;
- 01 same=9u+v+2a+8b+5, diff=u+9v+8a+2b+5.

Their denominators are both 10T and numerators are 6A+8B and 8A-6B. Logical increments/decrements can preserve this shared-denominator representation using fixed trial sequences: +A adds (8,2) to bucket00 and (9,1) to bucket01; -A adds (2,8),(1,9); +B adds (9,1),(2,8); -B adds (1,9),(8,2). Each increment vector can be realized arithmetically by exactly 20 existing trials; these four instruction-list macros have not been formally assembled and verified here. No data-dependent arithmetic is needed for these update sequences.

Mode A helper buckets 10=(4t,t), 11=(9t,t) give second row (3/5,4/5). Mode B helper buckets 10=(9t,t),11=(t,4t) give (4/5,-3/5). Column contractivity forces the first-row dot product with the unit second row to vanish. Therefore these geometries select A=0 and B=0, respectively. The standalone integer determinant identity and implication are compiled in RotatedSelector.v: under n>0 and x²+y²<=n², the three cleared constraints for helper (3/5,4/5) are equivalent to 3x+4y=0. The full actual-checker candidate is not a completed proof and is saved separately.

Every individual helper switch is reachable by only increments:

- A at scale t to B at scale 9t: add (77t,8t) to bucket10 and (0,35t) to bucket11.
- B at scale s to A at scale 4s: add (7s,3s) to bucket10 and (35s,0) to bucket11.

An A→B→A cycle multiplies hidden scale by 36. Each transition could be implemented by a fixed block repeated t or s times, **if** the unchanged VM could count those repetitions and detect completion while preserving A and B. No such instruction sequence has been established. The current guard selects a logical counter zero, not the hidden helper scale; bounded ordinary registers cannot hold arbitrary t. Supplying t or the repetition count through a Gallina runner would move the missing computation outside the VM and is not an answer.

Likewise, applying the guard to intermediate helper states does not furnish a known completion test: its answer also depends on the preserved first-row values A and B. The trivial first-row-zero case cannot establish a routine valid for arbitrary two-counter contents. This missing scale-control/storage protocol is the obstacle in this candidate, rather than an algebraic failure of the selector idea.

## Evidence and limits

The retained diagonal comparison is formally proved in `coq/kernel/foundation/VMAlternativeCounterAccess.v`. The rotated representation above remains an external candidate and does not supply a VM mode-switch loop, an independent-counter execution theorem, or universality.

The evidence distinguishes reproducible arithmetic checks from incomplete scratch proofs:

- `/tmp/thiele-resume/alternative_counter/RotatedSelector.v`: standalone integer determinant selector lemma. `coqc /tmp/thiele-resume/alternative_counter/RotatedSelector.v` exited 0. Its conclusion concerns the displayed integer inequalities; it does not mention `run_vm`.
- `artifacts/review_revision/check_rotated_protocol.py`: Python standard-library exact-arithmetic checks. Running `python3 artifacts/review_revision/check_rotated_protocol.py` printed `100 scale transitions and 1250 rational selector checks passed (external arithmetic only).` These checks evaluate fractions and count additions, not the project's executable checker or VM runner.
- `/tmp/thiele-resume/alternative_counter/VMRotatedCounterAccess-candidate.v`: incomplete actual-checker proof candidate. Its direct arithmetic proof attempt timed out after 90 seconds. It was removed from the repository proof tree, together with its generated partial artifacts; no admission or axiom was introduced.

The finite checks are evidence for the candidate calculations, not a proof that every runtime mode switch terminates or preserves its intended representation. Arbitrary source-supplied repetition counts do not discharge that missing execution obligation. This report identifies one concrete representation protocol still to construct; it does not establish impossibility for the unchanged ISA or for other protocols.
