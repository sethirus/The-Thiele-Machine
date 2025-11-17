# Coq proof audit — November 2025

## Methodology

- Installed Coq 8.18.0 with `apt-get` (see system log) and attempted a fresh build via `make -C coq -j2`. The build now progresses through the bridge helper lemmas but still fails inside `thielemachine/coqproofs/ThieleUniversalBridge.v` while unifying the concrete `run_n` execution trace with the symbolic state abbreviation expected by the proof script.【35dec9†L1-L38】
- Captured the RTL fetch/decode skeleton in `coq/thielemachine/coqproofs/HardwareBridge.v`, packaging the opcode decoder, partition counters, and small-step transition helpers that downstream proofs and the Python tooling use to align hardware traces with the abstract Thiele machine.【F:coq/thielemachine/coqproofs/HardwareBridge.v†L1-L148】
- Established the categorical packaging of Thiele programs in `coq/thielemachine/coqproofs/ThieleProc.v`, exposing closed-run semantics (`run_closed`), the receipt trace witness `trace_of_prog`, and the observational equivalence lemmas needed to treat sequential composition as categorical composition for the geometric roadmap.【F:coq/thielemachine/coqproofs/ThieleProc.v†L1-L240】
- Added `tools/verify_end_to_end.py` so the Coq core build, RTL simulation, and receipt metrics are exercised together when checking regressions.【F:tools/verify_end_to_end.py†L1-L206】
- Enumerated live admits directly from the sources. The active `_CoqProject` tree is now admit-free; only the archived `debug_no_rule.v` reproduction (excluded from the build) retains local admits for experimentation. The hyper-halting experiment continues to phrase its oracle requirement as a section hypothesis rather than a global axiom.【495e62†L1-L20】【F:coq/thielemachine/coqproofs/HyperThiele_Halting.v†L1-L35】
- Reviewed the partially completed universal-interpreter development. `ThieleUniversalBridge.v` documents that the transition lemmas are still unfinished, while `thieleuniversal/coqproofs/ThieleUniversal.v` now serves as a thin wrapper around the completed Simulation lemmas for downstream users.【96a0c1†L1-L28】【0249db†L47-L63】

## Build tiers and recommended workflow

| Tier | Scope | Role in repository | Build expectation | Notes |
| --- | --- | --- | --- | --- |
| **Core** | `coq/kernel/` | Mechanises the audited VM↔kernel simulation and ledger invariants that underpin the “kernel” certificate pipeline.【2fc38d†L1-L27】 | ✅ Compiles today; keep in CI. |
|  | `coq/thielemachine/coqproofs/` (excluding archival experiments) | Defines the abstract Thiele machine, its concrete VM, the new RTL bridge, and the subsumption theorem wrapper that imports simulation and separation results.【890263†L1-L40】【F:coq/thielemachine/coqproofs/HardwareBridge.v†L1-L148】 | ✅ Builds cleanly with Coq 8.18.0; keep the debug reproduction isolated so the zero-admit status persists.【495e62†L1-L20】 |
|  | `coq/modular_proofs/` | Supplies encoding bounds and Minsky-machine infrastructure consumed by the simulation development.【04dda2†L31-L48】 | ✅ Compiles; treat as required when touching simulation. |
| **Bridging / investigative** | `coq/thielemachine/coqproofs/ThieleUniversalBridge.v` + `coq/thieleuniversal/coqproofs/` | Provide the concrete universal TM implementation that the simulation proof references; still mid-refactor and failing in symbolic-execution lemmas.【96a0c1†L1-L28】【0249db†L47-L63】 | ❌ Currently fails; isolate from default workflows until the symbolic execution is repaired. |
| **Applied studies** | `coq/project_cerberus/coqproofs/` | Security-oriented case study that builds on the Thiele framework.【e34533†L1-L24】 | ✅ Optional; build on demand. |
|  | `coq/shor_primitives/` | Arithmetic and modular components used by the “Project Sovereign” quantum experiments.【42e690†L1-L24】 | ✅ Optional; compile when maintaining the quantum demo. |
|  | `coq/catnet/coqproofs/` | Category-theoretic network formalisation referenced by documentation.【f7d028†L1-L20】 | ✅ Optional. |
|  | `coq/isomorphism/coqproofs/` | Universe-isomorphism witness illustrating structural equivalence claims.【0998d7†L1-L20】 | ✅ Optional. |
|  | `coq/p_equals_np_thiele/` | Philosophical sketch rather than a rigorous complexity proof; does not feed the flagship theorems.【43b046†L1-L17】 | ✅ Optional; exclude from regression budget. |
|  | `coq/test_vscoq/coqproofs/` | Minimal lemma used to validate VSCoq editor integration.【2b2322†L1-L3】 | ✅ Optional. |

## Immediate documentation fixes

1. Update the admit/axiom inventory to reflect the two-step Simulation backlog (tape length + configuration equality) and the fact that the halting-oracle requirement now lives as a section hypothesis rather than a global axiom.【495e62†L1-L20】【F:coq/thielemachine/coqproofs/HyperThiele_Halting.v†L1-L35】
2. Revise the completion plan to focus on auditing whether optional studies should stay in the default build, and to document the precise failure mode in `ThieleUniversalBridge.v` before attempting further proof work.【35dec9†L1-L38】
3. Refresh contributor guidance (`coq/AGENTS.md` and `coq/README_PROOFS.md`) so new work items flow from this audit rather than the superseded milestone checklist.【96a0c1†L1-L28】【495e62†L1-L20】

## Suggested next steps

- **Stabilise the core build**: add a `make core` target that builds only the kernel, modular proofs, and the non-bridge thielemachine modules so CI can report regression status independently of the failing universal-interpreter experiments.【2fc38d†L1-L27】【890263†L1-L40】
- **Wire the hardware trace harness**: extend the Python/Verilog regression to dump instruction words and feed them through the `HardwareBridge` decode helpers so the automated end-to-end check confirms the RTL receipts match the Coq semantics without relying on hand-written instrumentation.【F:coq/thielemachine/coqproofs/HardwareBridge.v†L34-L145】【F:tools/verify_end_to_end.py†L1-L206】
- **Quarantine experimental directories**: when iterating on optional studies, use the forthcoming `make optional` target (or explicit `.vo` invocations) so these proofs do not block the core pipeline.
- **Plan universal-interpreter repairs deliberately**: treat the symbolic execution backlog as a dedicated project—capture invariants required by `pc_29_implies_registers_from_rule_table` and the `find_rule_*` lemmas, then re-enable the build once those proofs are complete.【0249db†L47-L63】
- **Scope the Thiele geometry programme**: follow `docs/THIELE_GEOMETRIC_UNIFICATION_PLAN.md` to build the symmetric monoidal category `ThieleProc` and embed logic, Turing computation, and Bell-style processes inside it, turning the existing proofs into categorical theorems stakeholders can cite precisely.【F:docs/THIELE_GEOMETRIC_UNIFICATION_PLAN.md†L1-L158】
