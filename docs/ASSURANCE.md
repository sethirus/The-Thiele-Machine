# Assurance and scope

This repository separates checked mathematics, executable verification,
trusted translation, and finite implementation tests. A result is described
by the strongest category it actually satisfies; a generated file or a
passing test is not treated as a proof merely because it is committed.

## Checked Coq results

The active Coq project is the source of truth for the formal corpus. The
current checked surface includes:

- the kernel instruction semantics, state invariants, cost accounting, and
  the selected computability and limitative results;
- the Kami CPU rules, reset facts, register schema, selected execution
  traces, fetch/update observations, normalization schedules, and the
  explicitly stated hardware-boundary lemmas;
- the source-generation equality that identifies the canonical backend AST;
- the assumptions and dependency closure reported by the proof gates.

These theorems establish only the propositions stated by their types. In
particular, the checked CPU results do not by themselves establish a complete
reachable-state invariant, arbitrary scheduler correctness, abstract
retirement correspondence, compiler semantic preservation, or an unbounded
hardware refinement theorem.

The unbounded self-interpreter and Rice reduction are scoped to the stated
four-register guest fragment and the unbounded sibling semantics. They do not
claim interpretation of the full structural ISA, correctness of the word64
physical model, or correctness of the synthesized RTL.

## Executable verification

The repository runs source-level probes, dependency-enabled `coqchk`, native
extraction checks, OCaml runner checks, RTL simulation, receipt consistency
checks, and the Python test suite. These establish reproducibility and the
behavior of the tested finite cases. They do not extrapolate finite traces to
all states or all executions.

The probe sources used by the native proof reproduction live in
[`tests/coq_probes/`](../tests/coq_probes/). Generated logs and compiled
objects belong in the ignored reproduction directory or in a specifically
named published evidence record; they are not source inputs.

## Translation and hardware boundaries

The extraction, OCaml printer, Bluespec compiler, and project text
transformations are executed and replayed with recorded inputs and hashes.
Their semantic preservation remains a trusted boundary unless a separate Coq
theorem states otherwise. Byte identity proves provenance and repeatability,
not circuit-level semantic equivalence.

RTL simulation covers the checked finite programs and encodings. Synthesis,
place-and-route, timing, and bitstream results are claims only when the
corresponding full workflow has produced current evidence. Historical
measurements are not current measurements.

## Vocabulary used by current documents

- **Proved**: established by the checked Coq source and its required
  dependencies.
- **Tested**: exercised by an executable gate or finite regression suite.
- **Trusted**: relied upon at a translation or tool boundary without a
  corresponding semantic-preservation theorem in this repository.
- **Assumed**: supplied as a premise of a theorem or gate.
- **Outside scope**: deliberately not claimed by the current model or gate.
- **Historical**: retained for provenance and not a current result.

Real limitations remain visible in the relevant theorem and document. The
active documentation does not describe the order in which a result was
discovered, repaired, or deferred.
