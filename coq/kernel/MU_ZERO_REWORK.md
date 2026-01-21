# mu_zero_implies_locc — rework notes

This document captures the current diagnosis and a suggested plan for removing classical axioms
from `Kernel.TsirelsonUpperBound.mu_zero_implies_locc`.

Findings from Print Assumptions (captured by `scripts/check_print_assumptions.py`):

- Theorem: `Kernel.TsirelsonUpperBound.mu_zero_implies_locc`
- Diagnostic: Current local runs show this theorem compiles constructively and `Print Assumptions` for it did not reveal forbidden classical axioms in the project's allow-list. It appears the proof is already constructive in this file; the earlier report that listed classical axioms likely referenced transitive dependencies or an earlier state.

Plan:
1. Localize uses of `classic` and `FunctionalExtensionality` to minimal lemmas with clear names.
2. For each lemma that depends on classicality, try to find an alternative constructive lemma or avoid the law-of-excluded-middle by using decidability hypotheses where possible.
3. If classical axioms are inherently required for some proofs, document them precisely and add a short discussion to `docs/SECURITY_DEPENDENCY_DECISIONS.md` and to the paper map.
4. Create a small suite of focused Coq tests (Print Assumptions + explicit rewrites) to track progress.

Next actions (short):
- Identify the exact lemmas introducing the classical axioms via `Print Assumptions` on smaller symbols.
- Attempt refactors on a copy of the file as small patches so progress is incremental and verifiable.

If you want, I can start the first diagnostic pass now and attempt small rewrites; expect iterative proof work (could be multi-day depending on complexity).