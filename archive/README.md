# Archive

Work set to one side. None of it is part of the Thiele Machine as the README,
the monograph and its exact statements state it, and none of it is built,
tested or audited with the main tree. It is kept as source, the way it was
written.

What is here:

- The worked machine: the small two-counter machine whose record goes up only
  after a checked, committed and certified claim, Thiele completeness over a
  two-counter base, the universal programs U and U_P, the lift to other bases,
  composition, the verified compiler, Rice and Kleene for two counters, and
  the counterexamples for each of its clauses (`coq/kernel/foundation/`,
  `minimal/`).
- Its companion document, *The worked machine*
  (`monograph/worked_machine.tex`, with the PDF and plain text).
- The CHSH and Tsirelson mathematics and the check on the multi-register
  machine (`coq/kernel/quantum/`, `coq/kernel/category/`).
- The OCaml extraction (`ocaml/`), the hand-written Python machine
  (`thiele_small/`), and the tests and scripts that ran them (`tests/`,
  `scripts/`).
- The pinned Coq Library of Undecidability Proofs the two-counter results
  stood on (`vendor/coq-undecidability/`), and the MetaCoq setup its L
  modules needed (`.github/actions/setup-metacoq/`,
  `scripts/install_metacoq.sh`).
- The first edition of the monograph (`monograph/monograph.tex`, with its
  PDF), its set-aside passages (`monograph/set_aside.tex`) and its
  mathematical specification (`monograph/thiele_machine_math_spec.tex`), each
  with its PDF, as they stood when the second edition replaced them. The
  first edition's published form is the PDF in the v4.1.1 release.
- The theorem meanings and the results list as they stood at tag v4.1.1
  (`docs/`), which carry the entries about the material above.

Paths inside this folder mirror where each file lived in the main tree. Every
file is as it stood at tag v4.1.1, except the companion, the first edition and
its two companion documents, the file `coq/kernel/foundation/AxThieleComplete.v`,
and fifteen Coq files that were edited before they were set aside.
To build or run any of it, check out tag v4.1.1 and follow that revision's
instructions; the files here are not wired into a build of their own.
