# Agent workflow for the `coq/` tree

The November 2025 audit reclassified every Coq subproject into **core**, **bridging**, or **optional** tiers. Use those tiers to plan work and to keep regressions contained.

## Before you edit

- [ ] Read the current snapshots in `docs/COQ_PROOF_AUDIT.md` and the condensed checklist in `docs/COQ_PROOF_COMPLETION_PLAN.md` so you know which tier the files you plan to touch belong to.【6b8295†L1-L45】【27e479†L5-L26】
- [ ] Confirm whether your task targets a **core** file (kernel, modular proofs, thielemachine), the failing **bridging** code (`verification/ThieleUniversalBridge.v`, `ThieleUniversal.v`), or an **optional** study (CatNet, universe isomorphism, P=NP sketch, Shor primitives, Project Cerberus, VSCoq smoke test).【6b8295†L15-L45】【27e479†L14-L22】

## Required checks

- For core changes, run `make -C coq core` before committing.
- When iterating on the bridging proofs, run `make -C coq core` first and then the specific `.vo` targets you touched inside `thielemachine/verification/ThieleUniversalBridge.v` or `thieleuniversal/coqproofs/ThieleUniversal.v` so partial progress is visible despite the known failure.【35dec9†L1-L38】【0249db†L47-L63】 If you need to keep CI logs responsive, prefer `make -C coq bridge-timed BRIDGE_TIMEOUT=900` so long symbolic-execution runs produce a bounded, explicit timeout instead of hanging jobs.
- Optional studies should use targeted builds (`make -C coq catnet/coqproofs/CatNet.vo`, etc.) so they do not block core CI unless explicitly requested.【6b8295†L33-L45】

## Reporting obligations

- If you touch `Simulation.v`, document how your change interacts with the no-rule helper catalogue (`utm_no_rule_preserves_tape_len`, `utm_no_rule_preserves_cpu_config`, etc.) and restate any new obligations you uncover so reviewers can see how the finished proof is preserved.【495e62†L1-L20】
- Any change to the halting-oracle experiments must call out the axiom `H_correct` and justify whether it is still required.【ac2173†L9-L30】
- Until the automation is fixed, update `coq/ADMIT_REPORT.txt` and `coq/AXIOM_INVENTORY.md` manually whenever you introduce or discharge admits/axioms; the existing scripts under-report the current counts.【27e479†L32-L34】

## Documentation hygiene

- Whenever work changes the tier of a file (e.g., graduates an optional study into the core pipeline), update `docs/COQ_PROOF_AUDIT.md` and `docs/COQ_PROOF_COMPLETION_PLAN.md` in the same change set so future contributors inherit accurate guidance.【6b8295†L1-L45】【27e479†L5-L34】
- Capture recurring failure signatures (like the `run_n` vs `st6` mismatch) inside the documentation or commit messages so investigators have reproducible starting points.【35dec9†L1-L38】
