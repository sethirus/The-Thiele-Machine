# Realization assurance

This account supplies Gate C3's artifact-specific assurance classification. It does not close the separate C1/C2 or E contracts. Exact source and generated-file hashes are in `artifacts/rtl_pipeline_manifest.json`; the review source patch/manifest pins the surrounding proof contracts. Historical timing/resource reports are not measurements of the changed hardware. Gate C1/C2 remains open.

| Edge or object | Evidence and classification | Limit |
| --- | --- | --- |
| VM instruction semantics to intermediate Gallina snapshot model | Checked `GraphReconstructionBridge.driven_step_wf` and `driven_trace_commutes`, under `WFDrivenPrecondition`/`WFDrivenRun`. | These functions are not the synthesizable FSM; range and opcode premises remain mathematical arguments. |
| Actual Kami dispatch and reset | `DispatchExecution` connects the executable evaluator exactly to the actual rule's `SemAction` and selected `Multistep`. `DispatchReset` establishes 13 actual initialization facts. | Supported linear-action semantics; reset facts and concrete fault observations do not establish all reachable-state invariants or abstract retirement correspondence. |
| All 12 actual CPU rules | `CoreRules` and `CoreExecution` establish executable semantics and finite selected Kami traces; `CoreTyping` preserves the complete register-name/kind schema from reset. Compilation and direct probes pass. | Schema preservation does not establish value/resource invariants, fairness or abstract observation correspondence. CoreTyping dependency-enabled rechecking completed successfully; the subsequent typed dispatch bridge also passed dependency-enabled rechecking. |
| Actual Kami normalization and MORPH loading rules | Checked `NormalizationRetirement.normalization_retirement` and `MorphRetirement.morph_retirement`, with direct types/assumptions and source reviews. | Selected schedules from explicit typed phase states. No dispatch/reset invariant, arbitrary scheduler theorem, or full graph/label correspondence. |
| Actual dispatch fetch and tensor/CSR writes | Checked fetch-frame and actual tensor set/get update-map facts (`DispatchFetch`, `TensorDispatch`), plus all-opcode dispatch CSR preservation; complete contracts in `c2_dispatch/`. | Canonical tensor encodings and successful dispatch premises; full snapshot refinement, heap execution proofs and FSM invariants/progress remain open. Inherited equality/extensionality assumptions are explicit. |
| Actual module to canonical backend AST | Checked `CanonicalCPUProof.canonical_cpu_module_from_source`, a definitional source-generation equality. | Establishes which AST is generated; the equation alone does not establish semantic preservation of lowering. |
| Coq extraction to OCaml artifacts | **Trusted semantic preservation; tested extraction.** Executed extraction and byte-freshness checks for eight outputs; the native source-only reproduction records its own results. | Extraction/toolchain behavior is an assurance boundary. A well-typed extracted definition does not automatically have the intended correctness specification. |
| OCaml printer to BSV | **Trusted semantic preservation; tested pipeline execution.** Pinned `PP.ml`, `Main.ml`, extracted input and BSV output; actual pipeline execution and identity checks. | Semantic preservation of printing is trusted here, not proved by the provenance manifest. |
| Project BSV transformations | **Trusted semantic preservation; tested byte replay.** Pinned scripts and replayed byte transformations in `rtl_text_transform_audit.json`. | Replay establishes reproducibility of the transformation, not semantic equivalence. |
| Bluespec compiler to raw Verilog | **Trusted semantic preservation; tested compiler execution.** Pinned generated output and recorded toolchain execution. | Compiler semantic preservation remains trusted for this path. |
| Project Verilog transformations and tracked RTL | **Trusted semantic preservation; tested byte replay and identity.** Replayed transformations and byte identity of generated synthesis RTL with tracked `thiele_cpu_kami.v`. | Text identity/provenance is distinct from a proof of the transformation's circuit behavior. |
| Simulated physical RTL behavior | 154 current runtime/encoding regressions pass, including nine tensor/CSR cases and both dispatch-fault suites (`c2_dispatch/final-runtime-tests.json`). The historical 163-test assertion-dispatch checkpoint and reproduced failures remain recorded separately. | Finite tested traces; no extrapolation to all input states, overflow cases or unlimited traces. |
| Synthesis, place-and-route, timing and bitstream | No new measurements for this candidate. | Historical numbers retain their historical source; no new physical performance claim. |

The abstract interface proposition `bsc_kami_compilation_trusted` is a conjunction of supplied printer/compiler propositions. Merely naming or supplying that interface does not verify a concrete compiler run. Similarly, assigning `Abstraction.kami_step` to a field named `verilog_step` does not define the generated circuit's behavior.

The [implementation contract](C1_IMPLEMENTATION_CONTRACT.md) now specifies admission, initialization, raw workspace bounds, observations and scheduling. Execution proofs for descriptor freshness, preserved old readouts, regions/endpoints/labels, failures, accounting and progress remain open. Raw MORPH loading has no region filter or label decoder. Any connection to the kernel's filtered, labelled coupling must handle that difference explicitly; the raw-pair theorem does not erase it.

## Unbounded software results

B3 is closed for the twelve-instruction, four-register guest fragment implemented by the fixed 122-instruction `VMSelfProgram.U`. The executable encoding, positive step simulation, raw result soundness/completeness, malformed-word behavior and live divergence contracts are checked. Guest structural state is ambient and preserved because this fragment has no structural instructions. See [SELF_INTERPRETER_REVIEW.md](SELF_INTERPRETER_REVIEW.md).

B4 is closed under the alternative-construction clause by the checked Rice reduction over that guest model. `self_rice` and `self_rice_dual` cover extensional predicates separating the divergent program from a well-formed program; `self_rice_representable` covers guest-program deciders. Named instances are halting on zero and returning zero. No internal recursion theorem is claimed; `total_run_obstruction` excludes the proposed total `Substrate.run` realization. These software results do not establish finite hardware correspondence. See [RICE_REVIEW.md](RICE_REVIEW.md).

## Current artifact audit

The current C3 object is the exact set of 22 source/backend/generated files in
`artifacts/rtl_pipeline_manifest.json`, copied with hashes into
`c3_audit/validation.json`. Any change to those files invalidates this audit.
The current synthesis RTL has SHA-256
`2bcf9200ef7027b8d3cff38d49c33127efe8c775e47cda4be3952a86579f3b34`.

The tensor/CSR checkpoint regenerated OCaml, BSV and Verilog with BSC 2024.07.
`module_tensors` remains a nested 16x16 BSV register and a flat 8192-bit Verilog
register; it is explicitly excluded from the RegFile transform. Both CSR
registers are present. The audit now checks those storage invariants.

The earlier 22-file audit and manifests are retained under `c3_audit/pre_tensor/`.
The first new test run found stale complete-root extraction; the full integration
build refreshed it. That build also changed OCaml declaration order, so downstream
artifacts were regenerated again before final manifest/replay checks. Both detected
staleness failures are retained. The final pipeline, transform replay and all 18
canonical pipeline/provenance tests pass in `c3_audit/validation.json`.

`python3 artifacts/review_revision/c3_audit/validate.py` checks the pinned
pipeline manifest, replays both project transformations, and runs the canonical
pipeline/provenance regression tests. Exact commands, exit codes and artifact
hashes are in `c3_audit/validation.json`. No edge is classified as semantic
translation validation merely because bytes match. The only formally proved
backend source-generation claim is the explicitly identified Coq equality;
semantic compiler/lowering preservation retains the stated trust boundary.

Synthesis and place-and-route are **not executed or measured for these pinned
artifacts**. No corresponding timing, LUT, routing, or bitstream claim is made.
Historical measurements remain historical. This satisfies the classification
and claim/evidence alignment requirement; it does not discharge the requested
physical refinement in C1/C2 or final local candidate validation in E. Independent reproduction/review
are optional under the 2026-09-14 user amendment.
