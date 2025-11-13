# Axiom and admit inventory for the Thiele Machine development

_Updated after the halting-oracle refactor captured in `docs/COQ_PROOF_AUDIT.md`._

## Summary
- **Total Admitted**: 2 (Simulation backlog + roadmap stub)
- **Total Axioms**: 0 (all oracle hypotheses are now section parameters)
- **Kernel module admits/axioms**: 0

## Kernel module status

The kernel proof tree (`coq/kernel/`) continues to build without admits or axioms. It provides the audited VM↔kernel simulation and ledger invariants used by downstream tooling.【2fc38d†L1-L27】

## Outstanding items

### Admitted lemmas (2)
1. **`coq/thielemachine/coqproofs/Simulation.v:3797`** – `utm_interpreter_no_rule_found_halts`.
   - **Context:** Symbolic execution of the universal program when `find_rule` returns `None` remains to be mechanised.【495e62†L1-L20】
   - **Impact:** Blocks the fully mechanised proof of `thiele_simulates_tm` and therefore the containment half of the subsumption theorem.
2. **`coq/ThieleMap.v:52`** – `thiele_simulates_by_tm` stays admitted as a planning hook for the simulation wrapper; the file is excluded from the default build while the lemma is formalised.

### Planning stubs
- **`coq/ThieleMap.v:52`** – `thiele_simulates_by_tm` is recorded as an admitted goal to track the roadmap effort; the file is excluded from the core build.

## Next steps
- Maintain `coq/ADMIT_REPORT.txt` alongside this file whenever admits change until the reporting script is repaired.【27e479†L32-L34】
- Track progress in `docs/COQ_PROOF_AUDIT.md` and update these counts immediately after proofs land so the audit stays trustworthy.【6b8295†L1-L45】
