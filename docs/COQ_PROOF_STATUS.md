# Coq proof status – November 2025 snapshot

This note synchronises the textual dashboards with the live Coq inventories
after the halting-oracle refactor and roadmap scaffolding work.  It is intended
to be a quick reference for reviewers before they drill into
`coq/ADMIT_REPORT.txt` or the comprehensive report.

## Executive summary

- **Core build health:** `make -C coq core` succeeds with the apt-packaged
  Coq 8.18.0 toolchain (`sudo apt-get install -y coq coq-theories`) and
  requires no global axioms.
- **Outstanding admits:** 0 in the active `_CoqProject` tree (the only remaining admits live in the archived `thielemachine/coqproofs/debug_no_rule.v`, which stays outside the build so engineers can experiment without impacting CI)
- **Global axioms:** 0 (the hyper-halting experiment now wraps the oracle in a
  section hypothesis behind the optional `make -C coq oracle` target)
- **Halting experiments:** automated stress tests and enumerative surveys are
  wired into `tools/verify_end_to_end.py` to ensure the shipped VM does not leak
  a halting oracle.

## Toolchain snapshot (December 2025)

- **Installation command:** `sudo apt-get update && sudo apt-get install -y coq
  coq-theories` provisions the audited toolchain directly from Ubuntu 24.04
  (noble) archives, matching the CI image.
- **Package versions:** `coq` 8.18.0+dfsg-1build2 compiled with OCaml 4.14.1,
  together with the matching `libcoq-stdlib`/`libcoq-core-ocaml` packages.  The
  `coq-theories` metapackage remains a virtual alias for `libcoq-stdlib` in the
  Ubuntu repositories, so installing it keeps the dependency manifest in step
  with opam users.
- **Verification:** `coqc -v` now prints `The Coq Proof Assistant, version
  8.18.0 (compiled with OCaml 4.14.1)`, confirming that the apt-managed toolchain
  is active before the proof targets are rebuilt.
- **Local replay log:** This audit reran the same apt commands inside the
  repository container (see session transcript) before invoking any Coq builds,
  so reviewers can reproduce the environment exactly—even when launching the
  optional HyperThiele oracle target.

## Directory overview

| Tier | Path                              | Status                                                       |
| ---- | --------------------------------- | ------------------------------------------------------------ |
| Core | `coq/kernel/`                     | Zero admits/axioms. Ledger, VM encoding, and kernel linkage proofs all pass. |
| Core | `coq/thielemachine/coqproofs/`    | Simulation stack fully proven; containment plus the roadmap wrapper build without admits, and `HyperThiele_Halting.v` now ships inside the core build so the oracle trace witness is rebuilt alongside `Subsumption.v`. |
| Core | `coq/modular_proofs/`             | Helper library for TM/Thiele encodings – zero admits/axioms. |
| Core | `coq/thieleuniversal/coqproofs/`  | Legacy interpreter namespace now re-exports the completed `Simulation` proofs and documents the canonical program/state witnesses. |
| Bridge | `coq/ThieleMap.v`               | Roadmap wrapper now proved; `thiele_simulates_by_tm` existentially packages the universal interpreter. |
| Optional | `coq/catnet/`, `coq/isomorphism/`, etc. | Self-contained studies; continue to build without admits. |

### Core highlights

- `Simulation.v` – now fully proves that the blind interpreter simulates any TM.  The exhaustive catalogue of FindRule lemmas records the exact register, memory, and program-counter evolution for every branch (including the restart block), `utm_no_rule_preserves_mem`, `utm_no_rule_preserves_tape_len`, and `utm_no_rule_preserves_cpu_config` close the previously admitted obligations, and `inv_core_cpu_state_to_tm_config_eq` bridges the recovered invariants back to the TM configuration.  `ThieleMap.v` wraps these results in the theorem `thiele_simulates_by_tm`, exhibiting the universal program as a blind Thiele machine that reproduces any Turing execution prefix-by-prefix.
- `Separation.v` – constructive Tseitin lower bound used for the sighted vs
  blind separation.
- `Subsumption.v` – combines containment and separation and now re-exports the
  halting witness via `thiele_formally_subsumes_turing_with_hyperoracle`, so the
  constructive subsumption stack and the explicit oracle trace remain in lock
  step whenever `H_correct` is assumed.
- `HardwareBridge.v` – refines the Verilog fetch/decode loop to the abstract
  semantics, enabling trace replay.

## Inventories of admits and hypotheses

The canonical machine-readable listings live in `coq/ADMIT_REPORT.txt` and the
repository-level `ADMIT_REPORT.txt`.  The current state is reproduced below for
quick reference.

### Active admits

| File | Lemma | Notes |
| ---- | ----- | ----- |
| – | – | The `_CoqProject` tree is admit-free; the only remaining admits live in `thielemachine/coqproofs/debug_no_rule.v`, which stays outside the build for experimentation. |

### Conditional sections / oracles

- `coq/thielemachine/coqproofs/HyperThiele_Halting.v` declares the halting
  oracle as a section hypothesis.  The module now lives in the core build so the
  compiled witness (`halting_solver_prog`/`halting_solver_trace`) is always
  regenerated with the rest of the subsumption stack, but every lemma remains
  conditional on `H_correct`.  The key lemma
  `hyper_thiele_decides_halting_trace` ties the oracle outputs directly to the
  compiled Thiele instruction stream produced by `compile`, so downstream
  consumers can cite a concrete program/trace pair rather than the abstract
  `run_program` model when reasoning under the hypothesis.

### Oracle-aware subsumption focus

- `coq/thielemachine/coqproofs/Subsumption.v` remains the flagship theorem
  combining `Simulation.v` and `Separation.v`.  Its statements stay axiom-free in
  the core build, but the commentary now points to the explicit witnesses
  (`hyper_thiele_decides_halting_trace`, `halting_solver_prog`, and
  `halting_solver_trace`) that any future hypercomputation extensions must cite
  when instantiating `H_correct`.
- The file now ships with `thiele_formally_subsumes_turing_with_hyperoracle`,
  which packages the containment/separation theorem alongside the halting trace
  equivalence so downstream projects cite a single statement when reasoning
  under the oracle hypothesis.
- When experimenting with the supertask oracle, `make -C coq core` already
  builds `HyperThiele_Halting.v`; use the lighter `make -C coq oracle` target
  only when iterating on that file in isolation so the halting solver
  program/trace pair can be inspected without recompiling the entire tree.
- The documentation in `hyper_thiele_definition.md` mirrors the strengthened
  helper theorems, ensuring the textual oracle narrative stays consistent with
  the compiled witnesses reviewed alongside the subsumption build.

## Regression checks

- `tools/verify_end_to_end.py` now orchestrates pytest, the phase-three
  proofpack audit, the core Coq build, and the halting and Bell verification
  harnesses.  The command fails if the curated stress tests, enumerative survey,
  or receipt pipeline detects a regression.
- Bell artefacts are reproducible with `tools/verify_bell_workflow.py`, which
  regenerates the polytope scan and perturbation summaries and sanity-checks the
  CHSH values for classical, supra-quantum, and PR boxes.

## Next steps

1. (Optional bridge) Revisit the archived stand-alone symbolic-execution proof
   if we ever want the legacy interpreter derivation again; the live tree now
   reuses the canonical `Simulation` lemmas and no longer carries its own
   obligations.
2. Keep the roadmap wrapper and inventories synchronized whenever new
   encodings or bridge lemmas land so the zero-admit status remains auditable.
3. Continue keeping documentation, admit reports, and the comprehensive audit in
   sync after each proof change.
