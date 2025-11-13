# Axiom and admit inventory for the Thiele Machine development

_Updated after the halting-oracle refactor captured in `docs/COQ_PROOF_AUDIT.md`._

## Summary
- **Total Admitted**: 3 (two-step Simulation backlog + roadmap stub)
- **Total Axioms**: 0 (all oracle hypotheses are now section parameters behind the optional `make oracle` target)
- **Kernel module admits/axioms**: 0

## Kernel module status

The kernel proof tree (`coq/kernel/`) continues to build without admits or axioms. It provides the audited VM↔kernel simulation and ledger invariants used by downstream tooling.【2fc38d†L1-L27】

## Outstanding items

### Admitted lemmas (3)
1. **`coq/thielemachine/coqproofs/Simulation.v:4338`** – `utm_no_rule_preserves_tape_len` singles out the final tape-window equality in the universal interpreter proof.  Discharging it requires symbolically executing the ten-instruction no-match sweep and proving the tape window length is unchanged.【495e62†L1-L20】
2. **`coq/thielemachine/coqproofs/Simulation.v:4358`** – `utm_no_rule_preserves_cpu_config` now depends on the previous lemma together with the catalogue argument that the sweep re-establishes `find_rule_start_inv`.  Once both pieces are available, `find_rule_start_inv_cpu_state_to_tm_config_eq` yields the desired configuration equality.【495e62†L1-L20】
3. **`coq/ThieleMap.v:66`** – `thiele_simulates_by_tm` stays admitted as a planning hook for the simulation wrapper; the file is excluded from the default build while the lemma is formalised.  The new lemma `thiele_simulates_tm_prefix` records the proven finite-prefix behaviour that the final theorem will extend.

### Planning stubs
- **`coq/ThieleMap.v:66`** – `thiele_simulates_by_tm` is recorded as an admitted goal to track the roadmap effort; the file is excluded from the core build while the full containment bridge is formalised.

### Conditional sections / oracles
- `coq/thielemachine/coqproofs/HyperThiele_Halting.v` declares the halting oracle
  as a section hypothesis inside `Section OracleHypothesis`.  The file is excluded
  from the `core` build and can be compiled explicitly with `make -C coq oracle`
  when experimenting with the toy hyper-halting wrapper.

## Next steps
- Maintain `coq/ADMIT_REPORT.txt` alongside this file whenever admits change until the reporting script is repaired.【27e479†L32-L34】
- Track progress in `docs/COQ_PROOF_AUDIT.md` and update these counts immediately after proofs land so the audit stays trustworthy.【6b8295†L1-L45】
