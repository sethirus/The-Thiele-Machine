# VM contracts

The unbounded VM results are stated for three related but distinct objects:
the fixed self-interpreter construction, the extensional limitative reduction,
and the guest's recursion theorem. All three are formal results about the
unbounded sibling semantics.

## Self-interpreter

`VMSelfProgram.U` is a fixed 122-instruction host. It interprets the declared
guest fragment consisting of HALT, LOAD_IMM, XFER, ADD, SUB, MUL, AND, OR,
SHL, SHR, JUMP, and JNEZ over four guest registers. Guest programs and inputs
are supplied as data in the host boundary state.

The checked contracts establish positive finite-step simulation, whole-run
correctness in both directions, malformed-word handling, live divergence, and
separation of the guest ledger from the host charge. The CM2 compiler maps its
programs into this fragment and preserves halting correspondence.

The construction does not interpret memory, graph, morphism, certification,
or port instructions. Guest structural fields are ambient and unchanged. No
claim is made about the word64 physical model or synthesized hardware.

## Rice reduction

The reduction is over well-formed programs in the same guest fragment. Its
observation compares returned registers and the guest ledger on every input.
The effective transformer preserves the supplied program when the compiled
MM2 instance halts and behaves as the divergent program otherwise. The
checked result establishes undecidability for extensional predicates that
separate those behaviors, including halting on zero and returning zero.

The reduction does not use the recursion theorem below.

## Recursion theorem

`vm_guest_recursion_theorem_closed` proves Kleene's recursion theorem inside
the guest: for every transformer that maps well-formed guest programs to
well-formed guest programs and is computed by a guest program on program
codes, some well-formed guest program has the same final registers and the
same guest ledger as its image on every input, and runs forever exactly when
its image does. The evaluator in the proof runs as guest code: the evaluator
relation is extracted to the lambda calculus L, compiled to a Minsky machine,
and executed by the guest.

## The full VM

None of the above is a recursion theorem for the full 51-opcode VM under its
bounded runs. Asked for every map on programs, with equality of the
thousand-step runs from every state, such a theorem is false
(`vm_full_recursion_premise_refuted`): that bounded shortcut property is
decidable, and the flip of any correct decider for it has no fixed point
(`vm_correct_flip_has_no_fixed_point`). So the conditional diagonal for the
full VM (`vm_structural_shortcut_undecidable_encoded`) applies only to
classes of maps that leave every such flip out. A total converged
`Substrate.run` is treated as a separate assumption whose consequences are
stated by its own theorem.

## Verification entry points

The exact statements and global assumptions are checked by the stable probes
under [`tests/coq_probes/self_interpreter/`](../tests/coq_probes/self_interpreter/)
and [`tests/coq_probes/rice/`](../tests/coq_probes/rice/). The native
reproduction and CI proof gates compile these probes against the active Coq
project and run dependency-enabled `coqchk` over the selected libraries.
