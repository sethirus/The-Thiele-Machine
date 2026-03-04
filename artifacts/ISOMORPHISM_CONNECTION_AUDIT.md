# Isomorphism Connection Audit

Generated: 2026-03-04T00:09:07.838103+00:00

## Summary

- Connected elements: **0**
- Disconnected items: **11**
- Weak links: **2**
- Confidence: **guarded**

## Disconnected (Actionable)

- `state_shape` [reintegrate]: missing=['rtl'] → Add or tighten implementation/tests in missing layers and re-run isomorphism gates.
- `opcode_alignment` [reintegrate]: missing=['rtl'] → Add or tighten implementation/tests in missing layers and re-run isomorphism gates.
- `mu_accounting` [reintegrate]: missing=['rtl'] → Add or tighten implementation/tests in missing layers and re-run isomorphism gates.
- `mu_tensor_bianchi` [reintegrate]: missing=['rtl'] → Add or tighten implementation/tests in missing layers and re-run isomorphism gates.
- `partition_semantics` [reintegrate]: missing=['rtl'] → Add or tighten implementation/tests in missing layers and re-run isomorphism gates.
- `receipts_integrity` [reintegrate]: missing=['rtl'] → Add or tighten implementation/tests in missing layers and re-run isomorphism gates.
- `cross_layer_bisim` [reintegrate]: missing=['rtl'] → Add or tighten implementation/tests in missing layers and re-run isomorphism gates.
- `semantic_unmapped::coq` [reintegrate]: missing=['coq', 'matrix-coverage'] → Promote critical nearby files into declared layer set or explicitly archive them.
- `semantic_unmapped::python` [reintegrate]: missing=['python', 'matrix-coverage'] → Promote critical nearby files into declared layer set or explicitly archive them.
- `semantic_unmapped::rtl` [reintegrate]: missing=['rtl', 'matrix-coverage'] → Promote critical nearby files into declared layer set or explicitly archive them.
- `semantic_unmapped::tests` [reintegrate]: missing=['tests', 'matrix-coverage'] → Promote critical nearby files into declared layer set or explicitly archive them.

## Weak Links

- `proof-isolated-declarations` [reintegrate]: count=130 → Review declarations for dead-end proofs or unhooked lemmas; reintegrate or archive.
- `proof-tiny-components` [move_or_archive]: count=5 → Small disconnected clusters may indicate proof islands; connect to main theorem spine or move to archive.

## Coverage Scope

- `coq`: declared=6, discovered=323, coverage=0.0186, semantic_unmapped=302
- `python`: declared=4, discovered=132, coverage=0.0303, semantic_unmapped=115
- `rtl`: declared=2, discovered=6, coverage=0.3333, semantic_unmapped=4
- `tests`: declared=5, discovered=131, coverage=0.0382, semantic_unmapped=117

## Outside Main Body

- `archive/coq_with_axioms/TsirelsonBoundProof.v` markers=['archive']
- `archive/kernel_exploratory/MinorConstraints.v` markers=['archive']
- `archive/kernel_exploratory/MuInformationTheoreticBounds.v` markers=['archive']
- `archive/kernel_exploratory/QuantumBoundComplete.v` markers=['archive']
- `archive/kernel_exploratory/TsirelsonBoundComplete.v` markers=['archive']
- `archive/kernel_exploratory/TsirelsonBoundDirect.v` markers=['archive']
- `archive/kernel_exploratory/TsirelsonBoundProof2.v` markers=['archive']
- `archive/kernel_exploratory/TsirelsonBoundTDD.v` markers=['archive']
- `archive/kernel_exploratory/TsirelsonBoundVerification.v` markers=['archive']
- `archive/scripts_unused/challenge.py` markers=['archive']
- `archive/scripts_unused/convert_variable_to_axiom.py` markers=['archive']
- `archive/scripts_unused/di_randomness_conflict_chart.py` markers=['archive']
- `archive/scripts_unused/recover_neural_prng.py` markers=['archive']
- `archive/tests_disabled/disabled/test_cross_impl.py` markers=['archive', 'disabled']
- `archive/tests_disabled/disabled/test_demo_cli_end_to_end.py` markers=['archive', 'disabled']
- `archive/tests_disabled/disabled/test_di_randomness_conflict_artifact.py` markers=['archive', 'disabled']
- `archive/tests_disabled/disabled/test_drat_normalization.py` markers=['archive', 'disabled']
- `archive/tests_disabled/disabled/test_fuzz_receipts.py` markers=['archive', 'disabled']
- `archive/tests_disabled/disabled/test_isomorphism_complete.py` markers=['archive', 'disabled']
- `archive/tests_disabled/disabled/test_lrat_normalization_demo.py` markers=['archive', 'disabled']
- `archive/tests_disabled/disabled/test_maxwell_thiele_ratchet.py` markers=['archive', 'disabled']
- `archive/tests_disabled/disabled/test_medium_cnf_sanity.py` markers=['archive', 'disabled']
- `archive/tests_disabled/disabled/test_prereg_a_per_series_metrics.py` markers=['archive', 'disabled']
- `archive/tests_disabled/disabled/test_prereg_a_schema_and_filtering.py` markers=['archive', 'disabled']
- `archive/tests_disabled/disabled/test_prereg_a_smoke.py` markers=['archive', 'disabled']
- `archive/tests_disabled/disabled/test_prereg_c_catalog_smoke.py` markers=['archive', 'disabled']
- `archive/tests_disabled/disabled/test_schema.py` markers=['archive', 'disabled']
- `archive/tests_disabled/disabled/test_showcase_programs.py` markers=['archive', 'disabled']
- `archive/tests_disabled/disabled/test_structural_heat_experiment.py` markers=['archive', 'disabled']
- `archive/tests_disabled/disabled/test_thermo_experiment.py` markers=['archive', 'disabled']

## Iterated/Similar Groups

- `.md:readme` count=18 sample=['coq/README.md', 'coq/bridge/README.md', 'coq/isomorphism/coqproofs/README.md', 'coq/kernel/README.md', 'coq/kernel_toe/README.md']
- `.py:test_three_layer_isomorphism` count=2 sample=['scripts/test_three_layer_isomorphism.py', 'tests/test_three_layer_isomorphism.py']
- `.v:closure` count=2 sample=['coq/kernel/Closure.v', 'coq/kernel_toe/Closure.v']
- `.v:definitions` count=2 sample=['coq/kernel/Definitions.v', 'coq/kernel_toe/Definitions.v']
- `.v:minorconstraints` count=2 sample=['archive/kernel_exploratory/MinorConstraints.v', 'coq/kernel/MinorConstraints.v']
- `.v:nogo` count=2 sample=['coq/kernel/NoGo.v', 'coq/kernel_toe/NoGo.v']
- `.v:nogosensitivity` count=2 sample=['coq/kernel/NoGoSensitivity.v', 'coq/kernel_toe/NoGoSensitivity.v']
- `.v:oracleimpossibility` count=2 sample=['coq/kernel/OracleImpossibility.v', 'coq/thielemachine/coqproofs/OracleImpossibility.v']
- `.v:persistence` count=2 sample=['coq/kernel/Persistence.v', 'coq/kernel_toe/Persistence.v']
- `.v:separation` count=2 sample=['coq/theory/Separation.v', 'coq/thielemachine/coqproofs/Separation.v']
- `.v:simulation` count=2 sample=['coq/modular_proofs/Simulation.v', 'coq/thieleuniversal/coqproofs/Simulation.v']

## Stale/Superfluous Candidates

- `archive/coq_with_axioms/TsirelsonBoundProof.v` → Path marker indicates likely stale/externalized component.
- `archive/kernel_exploratory/MinorConstraints.v` → Path marker indicates likely stale/externalized component.
- `archive/kernel_exploratory/MuInformationTheoreticBounds.v` → Path marker indicates likely stale/externalized component.
- `archive/kernel_exploratory/QuantumBoundComplete.v` → Path marker indicates likely stale/externalized component.
- `archive/kernel_exploratory/TsirelsonBoundComplete.v` → Path marker indicates likely stale/externalized component.
- `archive/kernel_exploratory/TsirelsonBoundDirect.v` → Path marker indicates likely stale/externalized component.
- `archive/kernel_exploratory/TsirelsonBoundProof2.v` → Path marker indicates likely stale/externalized component.
- `archive/kernel_exploratory/TsirelsonBoundTDD.v` → Path marker indicates likely stale/externalized component.
- `archive/kernel_exploratory/TsirelsonBoundVerification.v` → Path marker indicates likely stale/externalized component.
- `archive/scripts_unused/challenge.py` → Path marker indicates likely stale/externalized component.
- `archive/scripts_unused/convert_variable_to_axiom.py` → Path marker indicates likely stale/externalized component.
- `archive/scripts_unused/di_randomness_conflict_chart.py` → Path marker indicates likely stale/externalized component.
- `archive/scripts_unused/recover_neural_prng.py` → Path marker indicates likely stale/externalized component.
- `archive/tests_disabled/disabled/test_cross_impl.py` → Path marker indicates likely stale/externalized component.
- `archive/tests_disabled/disabled/test_demo_cli_end_to_end.py` → Path marker indicates likely stale/externalized component.
- `archive/tests_disabled/disabled/test_di_randomness_conflict_artifact.py` → Path marker indicates likely stale/externalized component.
- `archive/tests_disabled/disabled/test_drat_normalization.py` → Path marker indicates likely stale/externalized component.
- `archive/tests_disabled/disabled/test_fuzz_receipts.py` → Path marker indicates likely stale/externalized component.
- `archive/tests_disabled/disabled/test_isomorphism_complete.py` → Path marker indicates likely stale/externalized component.
- `archive/tests_disabled/disabled/test_lrat_normalization_demo.py` → Path marker indicates likely stale/externalized component.
- `archive/tests_disabled/disabled/test_maxwell_thiele_ratchet.py` → Path marker indicates likely stale/externalized component.
- `archive/tests_disabled/disabled/test_medium_cnf_sanity.py` → Path marker indicates likely stale/externalized component.
- `archive/tests_disabled/disabled/test_prereg_a_per_series_metrics.py` → Path marker indicates likely stale/externalized component.
- `archive/tests_disabled/disabled/test_prereg_a_schema_and_filtering.py` → Path marker indicates likely stale/externalized component.
- `archive/tests_disabled/disabled/test_prereg_a_smoke.py` → Path marker indicates likely stale/externalized component.
- `archive/tests_disabled/disabled/test_prereg_c_catalog_smoke.py` → Path marker indicates likely stale/externalized component.
- `archive/tests_disabled/disabled/test_schema.py` → Path marker indicates likely stale/externalized component.
- `archive/tests_disabled/disabled/test_showcase_programs.py` → Path marker indicates likely stale/externalized component.
- `archive/tests_disabled/disabled/test_structural_heat_experiment.py` → Path marker indicates likely stale/externalized component.
- `archive/tests_disabled/disabled/test_thermo_experiment.py` → Path marker indicates likely stale/externalized component.

## Visualization

```mermaid
flowchart LR
    C0[Connected Elements] --> C1[Cross-layer alignment]
    D0[Disconnected Elements] --> D1[Missing layers / obligations]
    W0[Weak Links] --> W1[Isolated proofs / tiny components]

    C1 --> T[Connection Truth Report]
    D1 --> T
    W1 --> T
```
