# Coq proof status – November 2025 snapshot

This note synchronises the textual dashboards with the live Coq inventories
after the halting-oracle refactor and roadmap scaffolding work.  It is intended
to be a quick reference for reviewers before they drill into
`coq/ADMIT_REPORT.txt` or the comprehensive report.

## Executive summary

- **Core build health:** `make -C coq core` succeeds with Coq 8.19.2 and
  requires no global axioms.
- **Outstanding admits:** 2
  1. `coq/thielemachine/coqproofs/Simulation.v:3797` –
     `utm_interpreter_no_rule_found_halts`
  2. `coq/ThieleMap.v:52` – `thiele_simulates_by_tm` (planning stub, excluded
     from the default build)
- **Global axioms:** 0 (the hyper-halting experiment now wraps the oracle in a
  section hypothesis)
- **Halting experiments:** automated stress tests and enumerative surveys are
  wired into `tools/verify_end_to_end.py` to ensure the shipped VM does not leak
  a halting oracle.

## Directory overview

| Tier | Path                              | Status                                                       |
| ---- | --------------------------------- | ------------------------------------------------------------ |
| Core | `coq/kernel/`                     | Zero admits/axioms. Ledger, VM encoding, and kernel linkage proofs all pass. |
| Core | `coq/thielemachine/coqproofs/`    | Simulation stack mostly proven; only the universal-interpreter lemma above remains admitted. |
| Core | `coq/modular_proofs/`             | Helper library for TM/Thiele encodings – zero admits/axioms. |
| Core | `coq/thieleuniversal/coqproofs/`  | Universal interpreter scaffolding; still failing symbolic execution obligations. |
| Bridge | `coq/ThieleMap.v`               | Planning wrapper for the subsumption statement (admitted). |
| Optional | `coq/catnet/`, `coq/isomorphism/`, etc. | Self-contained studies; continue to build without admits. |

### Core highlights

- `Simulation.v` – proves the blind interpreter simulates any TM.  The only
  remaining gap is `utm_interpreter_no_rule_found_halts`, which requires
  finishing the symbolic execution of the universal program when no rule
  matches.
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
| `coq/thielemachine/coqproofs/Simulation.v:3797` | `utm_interpreter_no_rule_found_halts` | Pending symbolic execution of the universal interpreter when `find_rule` fails |
| `coq/ThieleMap.v:52` | `thiele_simulates_by_tm` | Roadmap stub capturing the intended subsumption wrapper; file is excluded from the automated build |

### Conditional sections / oracles

- `coq/thielemachine/coqproofs/HyperThiele_Halting.v` declares the halting
  oracle as a section hypothesis.  Any theorem in that module is conditional on
  `H_correct` and is no longer counted as part of the axiom-free core.

## Regression checks

- `tools/verify_end_to_end.py` now runs the halting boundary verification
  (`tools/verify_halting_boundary.py`) by default.  The command fails if either
  the curated stress tests or the enumerative survey finds a VM/baseline
  disagreement.
- Bell artefacts are reproducible with `tools/verify_bell_workflow.py`, which
  regenerates the polytope scan and perturbation summaries and sanity-checks the
  CHSH values for classical, supra-quantum, and PR boxes.

## Next steps

1. Finish `utm_interpreter_no_rule_found_halts` so the containment theorem is
   axiom/assumption free.
2. Once the universal interpreter is fully mechanised, discharge
   `ThieleMap.v` by wrapping the existing simulation theorem.
3. Continue keeping documentation, admit reports, and the comprehensive audit in
   sync after each proof change.
