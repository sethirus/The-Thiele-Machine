# Assurance and scope

A result is true when the argument for it is correct, and the arguments are written out in the monograph, on the page. The formal and executable checks described here are tools for catching mistakes in those arguments and in their formal versions; none of them is the reason to believe a result. This repository separates formal proofs from executable tests. A result is described by the strongest category it actually satisfies; a generated file or a passing test is not treated as a proof merely because it is committed.

## Checked Coq results

The active Coq project (`coq/_CoqProject`) is the source of truth for the formal corpus. The checked surface includes:

- the abstract model: priced record systems and the toll over any order (`coq/kernel/foundation/AxCore.v`), the certification system with the universal floor for any substrate (`coq/kernel/nfi/UniversalCertificationCost.v`), the member predicate, the flat reading as a non-member, the latch as the smallest member and the history lift (`coq/kernel/foundation/AxThiele.v`), the least price for the lift (`coq/audit/AxThieleLeast.v`), with the permanent-certificate, pricing, entropy and narrowing results beside the floor in `coq/kernel/nfi/`;
- the record axis and its extensions over any base (`coq/kernel/foundation/`), the record over any order (`coq/kernel/foundation/Ax*.v`), and the results showing that each premise is needed (`coq/kernel/foundation/Nec*.v`);
- the small models of `minimal/`: the smallest machine (`minimal/Napkin.v`), the step law, merges and fresh states, the sliced definition and its window, and the verifier corollary stated abstractly;
- the structural undecidability interface, its natural-number instance, and the recursion theorem and Rice's theorem (Henry Rice, 1953: no program decides a property of what programs do unless it holds of every program or of none) for the lambda calculus L (`coq/kernel/nfi/StructuralUndecidability.v`, `coq/kernel/foundation/LRecursion.v`);
- the stated finite models of external systems in `coq/kernel/reductions/`, the calorimeter protocol in `coq/kernel/thermodynamic/`, and the pointer-criterion models in `coq/kernel/frontier/`;
- the assumptions and dependency closure reported by the proof gates.

These theorems establish only the propositions stated by their types. A model of an external system covers the model only; the deployed system is outside it.

## Executable verification

The repository runs source-level probes, dependency-enabled `coqchk` over every module of the project, the assumption receipt, the Inquisitor proof audit, the kernel-conversion vacuity audit, and the Python test suite. These establish reproducibility and the behavior of the tested finite cases. They do not extrapolate finite traces to all states or all executions.

`minimal/nofi_demo.py` rebuilds the quantitative floor with Python's standard library alone; it is a finite sweep, and it proves nothing beyond the cases it runs. `scripts/break_it.py` searches every small machine for counterexamples to the results of the monograph's part on the bill and runs a control with each premise dropped; it is a search, not warrant. `scripts/bead_erasure_sim.py` (needs numpy) is a simulation of a model with the numbers of Bérut and colleagues (2012), not a measurement.

## Historical hardware disclosure

Earlier releases of this repository carried a 51-instruction virtual machine, a Kami CPU, generated RTL and an FPGA bitstream. That material is preserved at tag `v3.3.0` and in its Zenodo version, and its later development, through commit 7157ce1b, is preserved at the tag `archive/big-build-2026-10-05`; [`TECHNICAL_DISCLOSURE.md`](../TECHNICAL_DISCLOSURE.md) describes it as a historical disclosure. None of its assurance claims applies to the current tree, which contains no hardware and no virtual machine.

## Vocabulary used by the documents

- **Proved**: argued in full (in the monograph, for the results it states), with a formal counterpart in the Coq source and its required dependencies.
- **Tested**: exercised by an executable gate or finite regression suite.
- **Cited**: a result from the literature, named with its source and not re-proved here.
- **Assumed**: supplied as a premise of a theorem or gate.
- **Outside scope**: deliberately not claimed by the model or gate.

Real limitations stay visible in the relevant theorem and document. Apart from the dated timeline in TECHNICAL_DISCLOSURE.md and the monograph's own history, the documentation does not describe the order in which a result was discovered, repaired, or deferred.
