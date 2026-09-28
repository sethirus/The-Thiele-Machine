# VM contracts

The unbounded VM results are stated for two related but distinct objects: the
fixed self-interpreter construction and the extensional limitative reduction.
Both are formal results about the unbounded sibling semantics.

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

This is the selected proved construction for the stated limitative result. It
does not claim an internal recursion theorem, and it does not discharge a
conditional diagonal for a bounded or physical VM. A total converged
`Substrate.run` is treated as a separate assumption whose consequences are
stated by its own theorem.

## Verification entry points

The exact statements and global assumptions are checked by the stable probes
under [`tests/coq_probes/self_interpreter/`](../tests/coq_probes/self_interpreter/)
and [`tests/coq_probes/rice/`](../tests/coq_probes/rice/). The native
reproduction and CI proof gates compile these probes against the active Coq
project and run dependency-enabled `coqchk` over the selected libraries.
