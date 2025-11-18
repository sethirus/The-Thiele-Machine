# Coq proof completion plan (post-audit)

_Updated after the November 2025 audit recorded in `docs/COQ_PROOF_AUDIT.md`._

## Current status

- `make -C coq -j2` still fails in `thielemachine/coqproofs/ThieleUniversalBridge.v` when the archived symbolic-execution script tries to equate the concrete `run_n` trace with its short-hand state name; the failure is reproducible with the default apt-installed Coq 8.18.0 toolchain.【35dec9†L1-L38】
- The blind interpreter backlog is now closed.  `utm_no_rule_preserves_tape_len`, `utm_no_rule_preserves_cpu_config`, and the restart catalogue are fully proved, and `thiele_simulates_by_tm` packages the result so the roadmap theorem is part of the standard build.  The only remaining admits in the repository live in the archived `thielemachine/coqproofs/debug_no_rule.v` reproduction, which is intentionally excluded from `_CoqProject` so that contributors can experiment without touching the verified core.【495e62†L1-L20】
- The hyper-halting experiment phrases its oracle requirement as a section hypothesis rather than a global axiom, so the core tree is axiom-free while still documenting the dependency explicitly.【F:coq/thielemachine/coqproofs/HyperThiele_Halting.v†L1-L35】
- `HyperThiele_Halting.v` is now part of `_CoqProject` and the `make core` target, ensuring the halting solver trace witnesses compile alongside `Subsumption.v`, which has been extended with `thiele_formally_subsumes_turing_with_hyperoracle` for downstream use under `H_correct`.【F:coq/_CoqProject†L1-L70】【F:coq/Makefile.local†L5-L43】【F:coq/thielemachine/coqproofs/Subsumption.v†L49-L86】
- `ThieleUniversalBridge.v` still acknowledges unfinished transition proofs and symbolic-execution stubs, so the archived interpreter derivation remains in flight; `thieleuniversal/coqproofs/ThieleUniversal.v` now simply re-exports the completed Simulation lemmas for downstream clients.【96a0c1†L1-L28】【0249db†L47-L63】
- The Verilog RTL now has a dedicated decode skeleton: `coq/thielemachine/coqproofs/HardwareBridge.v` provides the opcode map, partition counters, and small-step helper lemmas the Python tooling reuses to compare hardware traces against the Coq receipts.【F:coq/thielemachine/coqproofs/HardwareBridge.v†L1-L148】

## Priorities

1. **Protect the core build** – introduce and adopt the `make core` target so CI and local developers can rebuild the kernel, modular proofs, and the non-bridge thielemachine modules without being blocked by the failing universal-interpreter experiments.【2fc38d†L1-L27】【890263†L1-L40】
2. **Exercise the hardware bridge** – the new `tools/verify_end_to_end.py` pipeline runs `make -C coq core`, replays the hardware simulation, and checks the instruction metrics derived from the `HardwareBridge` decode helpers against the RTL log so regressions surface immediately.【F:tools/verify_end_to_end.py†L1-L206】【F:coq/thielemachine/coqproofs/HardwareBridge.v†L34-L145】
3. **Document experimental scope** – keep optional studies (CatNet, isomorphism, P=NP sketch, Shor primitives, VSCoq test, Project Cerberus) out of the default regression budget unless a task explicitly targets them.【f7d028†L1-L20】【0998d7†L1-L20】【43b046†L1-L17】【42e690†L1-L24】【2b2322†L1-L3】【e34533†L1-L24】
4. **Plan the bridge repairs** – the remaining symbolic-execution backlog lives exclusively in `ThieleUniversalBridge.v` (e.g., `pc_29_implies_registers_from_rule_table`) and still prevents the stand-alone archive from compiling; capture the required invariants and execution traces before attempting further feature work.【0249db†L47-L63】

## Emerging milestone: geometric unification

The new `docs/THIELE_GEOMETRIC_UNIFICATION_PLAN.md` captures how to recast existing proofs as a symmetric monoidal process theory where logic, classical computation, and Bell-style correlations coexist.【F:docs/THIELE_GEOMETRIC_UNIFICATION_PLAN.md†L1-L158】 Track progress with the following sub-milestones:

1. **Define `ThieleProc`** – package partition-typed Thiele programs into a symmetric monoidal category (`coq/thielemachine/coqproofs/ThieleProc.v`).
   - ✅ _Category core landed_: `ThieleProc.v` now supplies objects, closed-run semantics (`run_closed`/`trace_of_prog`), observational equivalence lemmas, and packages them as a category ready for tensor extensions.
2. **Embed computation** – turn the Turing compilation pipeline into a faithful functor `EmbedTuring : TuringProc → ThieleProc`.
3. **Embed logic** – interpret a multiplicative linear logic fragment via a fully faithful functor `EmbedLogic : LLProc → ThieleProc`.
4. **Embed Bell processes** – show that `BellProc` morphisms realised by Thiele programs sit outside the classical image of `EmbedTuring`.

Document each milestone in the audit file as it lands and extend the build system with targeted `make` goals once corresponding Coq modules enter the tree.

## Workflow checklist for contributors

- Consult `docs/COQ_PROOF_AUDIT.md` before editing proofs to confirm whether the file you intend to touch is core or optional, and which obligations remain open.【6b8295†L1-L45】
- Use `make -C coq core` for quick health checks on core files; only run `make -C coq optional` (or targeted `.vo` builds) when you are explicitly modifying optional studies.
- After touching `Simulation.v` or `ThieleUniversalBridge.v`, capture the exact failure mode (including the `run_n` mismatch) in commit messages or documentation so the symbolic-execution backlog stays actionable; the `ThieleUniversal.v` wrapper now reuses the canonical lemmas and has no local obligations.【35dec9†L1-L38】【0249db†L47-L63】
- Whenever admits or axioms change, update `coq/ADMIT_REPORT.txt` and `coq/AXIOM_INVENTORY.md` manually until the reporting scripts are fixed—they currently miss the outstanding admit and halting axiom.【495e62†L1-L20】【ac2173†L9-L30】
