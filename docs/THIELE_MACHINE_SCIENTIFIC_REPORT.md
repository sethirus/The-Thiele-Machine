# Legacy Formal Verification Status (April 2025)

This note replaces the earlier manifesto-style report. It summarises the status of the
large Coq development under `coq/thielemachine/` and clarifies how it relates to the
actively maintained microcosms (`coq/sandboxes/`). The goal is to distinguish the
historical proof sketches from the artefacts that currently compile without axioms.

## 1. Active, Mechanically Checked Artefacts

- `coq/kernel/` formalises the minimalist shared-tape universe. `KernelTM.v` and
  `KernelThiele.v` share the classical clauses; only the Thiele interpreter
  executes `H_ClaimTapeIsZero`, zeroing the tape and incrementing `mu_cost`.
  `Subsumption.v` proves that Thiele executions reproduce all classical runs and
  reach a state the classical kernel cannot.【F:coq/kernel/Kernel.v†L4-L66】【F:coq/kernel/KernelTM.v†L12-L37】【F:coq/kernel/KernelThiele.v†L7-L26】【F:coq/kernel/Subsumption.v†L36-L118】
- `coq/sandboxes/ToyThieleMachine.v` implements the "ClaimLeftZero" microcosm: a
  Thiele interpreter spends one µ-bit to achieve a tape that the classical
  write-only interpreter provably cannot reach.【F:coq/sandboxes/ToyThieleMachine.v†L1-L94】
- `coq/sandboxes/VerifiedGraphSolver.v` encodes the triadic cascade graph and
  proves the classical backtracker needs 18 branch attempts while the Thiele
  solver records 1,288 description bits plus nine `log₂ 3` gains (≈1302.26 µ-bits)
  and performs zero additional arithmetic steps, matching the empirical
  receipts.【F:coq/sandboxes/VerifiedGraphSolver.v†L9-L177】【F:graph_demo_output/triadic_cascade/analysis_report.json†L1-L45】
- `scripts/prove_it_all.sh` and `scripts/translate_receipts_to_coq.py` generate
  `coq/sandboxes/GeneratedProof.v`, linking the Act III receipts to the sandbox
  solver with a direct Coq replay.【F:scripts/prove_it_all.sh†L1-L24】【F:coq/sandboxes/GeneratedProof.v†L1-L66】

These artefacts constitute the "working" portion of the formal stack today; the
kernel delivers the mechanical subsumption proof, while the sandboxes and bridge
mirror the empirical graph-colouring experiment.

## 2. Status of the Legacy Universal Development

The older containment/separation proof attempt remains in
`coq/thielemachine/coqproofs`. Key modules still rely on unfinished lemmas:

- `Simulation.v` retains multiple `Admitted` placeholders around the universal
  interpreter simulation lemmas, reflecting the unsolved "sphere made of lines"
  barrier.【F:coq/thielemachine/coqproofs/Simulation.v†L3574-L3839】
- `verify_subsumption.sh` now terminates immediately with an archival notice;
  none of the make targets rebuild the historic development by default.【F:coq/verify_subsumption.sh†L1-L24】
- The archived directory `archive/research/incomplete_subsumption_proof/` records
  why the proof stalled and confirms that no live targets depend on it.【F:archive/research/incomplete_subsumption_proof/README.md†L1-L12】

Files such as `Separation.v` and `ThieleMachine.v` remain available for reference
but are not included in the current continuous verification pipeline. They
assume axioms about blind search costs and rely on the unresolved simulation
lemmas, so they should be treated as research notes rather than finished proofs.

## 3. Relationship to Repository Claims

- The README, audit reports, and `docs/final_fact_check.md` now characterise the
  sandboxes as existence proofs and emphasise that no asymptotic separation has
  been mechanised in the general development.【F:README.md†L1-L125】【F:docs/final_fact_check.md†L1-L60】
- Empirical evidence for the graph-colouring laboratory documents constant-factor
  collapses with host-side reasoning; it does not back a universal theorem.

## 4. Recommended Verification Workflow

Auditors should:

1. Run `scripts/prove_it_all.sh` to regenerate the triadic cascade receipts and
   recompile the sandbox proofs.
2. Inspect the archived universal development for research context, but treat it
   as incomplete until the admitted lemmas are resolved.

This split preserves transparency: the legacy files remain available for future
work, while the repository clearly identifies the smaller artefacts that are
fully mechanised today.
