# Coq proof status – November 2025 snapshot

This note synchronises the textual dashboards with the live Coq inventories
after the halting-oracle refactor and roadmap scaffolding work.  It is intended
to be a quick reference for reviewers before they drill into
`coq/ADMIT_REPORT.txt` or the comprehensive report.

## Executive summary

- **Core build health:** `make -C coq core` succeeds with Coq 8.19.2 and
  requires no global axioms.
- **Outstanding admits:** 0 in the active `_CoqProject` tree (the only remaining admits live in the archived `thielemachine/coqproofs/debug_no_rule.v`, which stays outside the build so engineers can experiment without impacting CI)
- **Global axioms:** 0 (the hyper-halting experiment now wraps the oracle in a
  section hypothesis behind the optional `make -C coq oracle` target)
- **Halting experiments:** automated stress tests and enumerative surveys are
  wired into `tools/verify_end_to_end.py` to ensure the shipped VM does not leak
  a halting oracle.

## Directory overview

| Tier | Path                              | Status                                                       |
| ---- | --------------------------------- | ------------------------------------------------------------ |
| Core | `coq/kernel/`                     | Zero admits/axioms. Ledger, VM encoding, and kernel linkage proofs all pass. |
| Core | `coq/thielemachine/coqproofs/`    | Simulation stack fully proven; containment plus the roadmap wrapper build without admits. |
| Core | `coq/modular_proofs/`             | Helper library for TM/Thiele encodings – zero admits/axioms. |
| Core | `coq/thieleuniversal/coqproofs/`  | Legacy interpreter namespace now re-exports the completed `Simulation` proofs and documents the canonical program/state witnesses. |
| Bridge | `coq/ThieleMap.v`               | Roadmap wrapper now proved; `thiele_simulates_by_tm` existentially packages the universal interpreter. |
| Optional | `coq/catnet/`, `coq/isomorphism/`, etc. | Self-contained studies; continue to build without admits. |

### Core highlights

- `Simulation.v` – now fully proves that the blind interpreter simulates any TM.  The exhaustive catalogue of FindRule lemmas records the exact register, memory, and program-counter evolution for every branch (including the restart block), `utm_no_rule_preserves_mem`, `utm_no_rule_preserves_tape_len`, and `utm_no_rule_preserves_cpu_config` close the previously admitted obligations, and `inv_core_cpu_state_to_tm_config_eq` bridges the recovered invariants back to the TM configuration.  `ThieleMap.v` wraps these results in the theorem `thiele_simulates_by_tm`, exhibiting the universal program as a blind Thiele machine that reproduces any Turing execution prefix-by-prefix.
- `Separation.v` – constructive Tseitin lower bound used for the sighted vs
  blind separation.
- `Subsumption.v` – combines containment and separation.  Downstream theorems
  now mention the halting-oracle hypothesis explicitly when needed.
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
  oracle as a section hypothesis.  Any theorem in that module is conditional on
  `H_correct` and is no longer counted as part of the axiom-free core.  The new
  lemma `hyper_thiele_decides_halting_trace` ties the oracle outputs directly to
  the compiled Thiele instruction stream produced by `compile`, so downstream
  consumers can cite a concrete program/trace pair rather than the abstract
  `run_program` model when reasoning under the hypothesis.

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
