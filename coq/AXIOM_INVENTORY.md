# Axiom and admit inventory for the Thiele Machine development

_Updated in November 2025 following the audit recorded in `docs/COQ_PROOF_AUDIT.md`._

## Summary
- **Total Admitted**: 1 (Simulation proof backlog)
- **Total Axioms**: 1 (halting-oracle interface)
- **Kernel module admits/axioms**: 0

## Kernel module status

The kernel proof tree (`coq/kernel/`) continues to build without admits or axioms. It provides the audited VM↔kernel simulation and ledger invariants used by downstream tooling.【2fc38d†L1-L27】

## Outstanding items

### Admitted lemmas (1)
1. **`coq/thielemachine/coqproofs/Simulation.v:3797`** – `utm_interpreter_no_rule_found_halts`.
   - **Context:** Symbolic execution of the universal program when `find_rule` returns `None` remains to be mechanised.【495e62†L1-L20】
   - **Impact:** Blocks the fully mechanised proof of `thiele_simulates_tm` and therefore the containment half of the subsumption theorem.

### Axioms (1)
1. **`coq/thielemachine/coqproofs/HyperThiele_Halting.v:14`** – `H_correct : forall e, H e = true <-> Halts e`.
   - **Context:** Encapsulates the behaviour of the postulated halting oracle used in the HyperThiele experiment.【ac2173†L9-L30】
   - **Impact:** Remains acceptable only if the experiment is treated as exploratory; removing it would require a constructive halting witness or a different specification.

## Next steps
- Maintain `coq/ADMIT_REPORT.txt` alongside this file whenever admits or axioms change; the automation no longer reflects reality until the reporting script is repaired.【27e479†L32-L34】
- Track progress in `docs/COQ_PROOF_AUDIT.md` and update these counts immediately after proofs land so the audit stays trustworthy.【6b8295†L1-L45】
