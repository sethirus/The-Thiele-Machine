# Coq Formalization: Thiele CPU Empirically Subsumes Turing

This directory contains a formalization (in Coq) of the claim that the Thiele CPU empirically subsumes the Turing machine model. The goal is to provide machine-checkable definitions and a theorem statement, with a roadmap for a full proof.

## Structure
- `TuringMachine.v`: Definition of the classical Turing machine.
- `ThieleCPU.v`: Definition of the Thiele CPU (as implemented in `thielecpu/`).
- `Subsumption.v`: Statement of the main theorem: every Turing machine can be simulated by the Thiele CPU.
- `EmpiricalEvidence.v`: (Optional) Extraction of empirical evidence from Python models.

## Status
- [ ] Definitions stubbed
- [ ] Theorem stated
- [ ] Proof in progress

## Instructions
- To build: `coqc Subsumption.v`
- Dependencies: Coq 8.16+ (install with `apt install coq` or see https://coq.inria.fr/)

---
This is a work in progress. See `README_CPU.md` for the Python implementation and empirical results.
