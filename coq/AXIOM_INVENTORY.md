# Axiom and admit inventory for the Thiele Machine development

_Updated after the halting-oracle refactor captured in `docs/COQ_PROOF_AUDIT.md`._

## Summary
- **Total Admitted**: 0 (roadmap wrapper proved; debug isolates remain excluded from the core build)
- **Total Axioms**: 0 (all oracle hypotheses are now section parameters behind the optional `make oracle` target)
- **Kernel module admits/axioms**: 0

> **Debug artefact:** `coq/thielemachine/coqproofs/debug_no_rule.v` preserves the historical no-rule reproduction (with local
> admits) for experimentation.  It is not wired into `_CoqProject`, so the official admit count above is unchanged.

## Kernel module status

The kernel proof tree (`coq/kernel/`) continues to build without admits or axioms. It provides the audited VM↔kernel simulation and ledger invariants used by downstream tooling.【2fc38d†L1-L27】

## Outstanding items

### Admitted lemmas
- _None_.  All lemmas in the core tree now have completed proofs.

### Planning stubs
- _None_.  The roadmap wrapper `thiele_simulates_by_tm` has been proved and the file participates in the standard build.

### Conditional sections / oracles
- `coq/thielemachine/coqproofs/HyperThiele_Halting.v` declares the halting oracle
  as a section hypothesis inside `Section OracleHypothesis`.  The file is excluded
  from the `core` build and can be compiled explicitly with `make -C coq oracle`
  when experimenting with the toy hyper-halting wrapper.  The helper
  `hyper_thiele_decides_halting_trace` now exposes the compiled Thiele instruction
  stream corresponding to the oracle query, so the assumption manifests as a
  concrete program/trace pair rather than the abstract `run_program` list.

## Next steps
- Maintain `coq/ADMIT_REPORT.txt` alongside this file whenever admits change until the reporting script is repaired.【27e479†L32-L34】
- Track progress in `docs/COQ_PROOF_AUDIT.md` and update these counts immediately after proofs land so the audit stays trustworthy.【6b8295†L1-L45】
