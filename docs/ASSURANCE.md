# Assurance and scope

This repository separates checked mathematics from executable tests. A result is described by the strongest category it actually satisfies; a generated file or a passing test is not treated as a proof merely because it is committed.

## Checked Coq results

The active Coq project (`coq/_CoqProject`) is the source of truth for the formal corpus. The checked surface includes:

- the abstract model: certification systems, the step rule, the ledger, A2, and No Free Insight for any substrate (`coq/kernel/nfi/UniversalCertificationCost.v`), with the permanent-certificate, pricing, entropy and narrowing results beside it in `coq/kernel/nfi/`;
- the record axis and its extensions over any base (`coq/kernel/foundation/`), and the record over any order (`coq/kernel/foundation/Ax*.v`);
- the small machine in `minimal/EarnedCore.v` (earned commitments, checker soundness, no forging, the cost of a certified run) and its links into the abstract records in `coq/kernel/foundation/EarnedCoreLinks.v`;
- the definition of Thiele-complete, the machines that meet it and the machines that fail it (`minimal/ThieleComplete.v`), and the window theorem for every Thiele-complete machine (`minimal/ThieleCompleteWindow.v`);
- the lifting of every universal base to a Thiele-complete machine (`minimal/Lift*.v`, `coq/kernel/foundation/Lift*.v`), the composition of Thiele-complete machines (`minimal/Cz*.v`, `coq/kernel/foundation/Cz*.v`), and the results showing that each premise and each clause is needed (`minimal/Nec*.v`, `coq/kernel/foundation/Nec*.v`);
- the host that runs small-machine programs as guests (`minimal/UniversalThiele.v`), the universal machine U and the priced host's program U_P (`coq/kernel/foundation/Universal*.v`), and the computably presented machines U_P runs (`coq/kernel/foundation/PresentedUniversal.v`);
- the verified compiler (`coq/kernel/foundation/Cmp*.v`) and the proofs that the definitions extracted to OCaml equal the originals (`coq/kernel/foundation/Realize*.v`);
- the structural undecidability interface, its natural-number instance, the recursion theorem and Rice's theorem for the lambda calculus L, and Rice's and Kleene's theorems for the two-counter machine and the multi-register host, and where recursion fails on two counters (`coq/kernel/foundation/Tc*.v`, `coq/kernel/foundation/Sm*.v`, `minimal/Tc2Mult.v`);
- the stated finite models of external systems in `coq/kernel/reductions/`, the CHSH/Tsirelson mathematics in `coq/kernel/quantum/` and `coq/kernel/category/`, the calorimeter protocol in `coq/kernel/thermodynamic/`, and the pointer-criterion models in `coq/kernel/frontier/`;
- the assumptions and dependency closure reported by the proof gates.

These theorems establish only the propositions stated by their types. A model of an external system covers the model only; the deployed system is outside it. The vendored undecidability library (`vendor/coq-undecidability/`), the Coq Library of Undecidability Proofs of Yannick Forster, Dominique Larchey-Wendling and coauthors, supplies the two-counter undecidability result, the L-to-Minsky reductions and the equivalence of its seven models of computation; its own proofs are checked with the rest of the build. The Turing-completeness of two-counter machines is a theorem of Marvin Minsky, who studied how bare a machine can be and still compute what a Turing machine computes (1961, 1967), and the calculus L is the one Yannick Forster and Gert Smolka presented as a model of computation in Coq (ITP 2017); Yannick Forster, Fabian Kunze, Gert Smolka and Maximilian Wuttke later checked in Coq that L and Turing machines simulate each other (ITP 2021). Neither result is re-proved in this repository's own files: the two-counter result is cited, and the Turing-completeness of L comes from the library's models-equivalence theorem.

## Executable verification

The repository runs source-level probes, dependency-enabled `coqchk` over every module of the project, the assumption receipt, the Inquisitor proof audit, the kernel-conversion vacuity audit, and the Python test suite. These establish reproducibility and the behavior of the tested finite cases. They do not extrapolate finite traces to all states or all executions.

`minimal/nofi_demo.py` rebuilds the quantitative floor with Python's standard library alone; it is a finite sweep, and it proves nothing beyond the cases it runs.

## Historical hardware disclosure

Earlier releases of this repository carried a 51-instruction virtual machine, a Kami CPU, generated RTL and an FPGA bitstream. That material is preserved at tag `v3.3.0` and in its Zenodo version, and its later development, through commit 7157ce1b, is preserved on the branch `archive/big-build`; [`TECHNICAL_DISCLOSURE.md`](../TECHNICAL_DISCLOSURE.md) describes it as a historical disclosure. None of its assurance claims applies to the current tree, which contains no hardware and no virtual machine.

## Vocabulary used by the documents

- **Proved**: established by the checked Coq source and its required dependencies.
- **Tested**: exercised by an executable gate or finite regression suite.
- **Cited**: a result from the literature or a vendored library, named with its source and not re-proved here.
- **Assumed**: supplied as a premise of a theorem or gate.
- **Outside scope**: deliberately not claimed by the model or gate.

Real limitations stay visible in the relevant theorem and document. The documentation does not describe the order in which a result was discovered, repaired, or deferred.
