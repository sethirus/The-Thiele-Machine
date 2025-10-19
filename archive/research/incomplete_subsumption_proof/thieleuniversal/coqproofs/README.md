# Turing Machine Helper Module

This directory packages the fully mechanised Universal Turing Machine that the
containment pillar (`Simulation.v`) imports.  It provides the canonical
definitions of classical configurations together with the blind interpreter that
the Thiele Machine replays inside a single partition.  All files compile
without admits and no axioms remain; the proofs connect directly to the
interface lemmas consumed by the flagship subsumption development.

## Highlights

- **Purpose:** supply the classical baseline required to state and prove that
  every Turing Machine execution is reproducible by a blind Thiele program.
- **Compilation:** `make thieleuniversal/coqproofs/ThieleUniversal.vo` (invoked
  automatically by `coq/verify_subsumption.sh`).
- **Admitted statements:** none.
- **Axioms:** none – the historical placeholders have been mechanised.
- **Deliverables:** encoding scheme, universal program, helper lemmas, and the
  packaged documentation of the interpreter interface used by
  `Simulation.v`.

## File guide

| File | Role | Key facts |
| --- | --- | --- |
| `TM.v` | Classical TM definition | Records the state/tape/head configuration type and deterministic `tm_step`/`tm_run` relations. |
| `CPU.v` | Simple register machine | Implements the finite instruction set, register file, and memory model used by the interpreter. |
| `UTM_Program.v` | Universal program layout | Enumerates the instruction sequence, memory addresses, and decoding lemmas for the interpreter code. |
| `UTM_Encode.v` | Rule-table encoder | Proves correctness of the rule encoding/decoding pipeline. |
| `UTM_CoreLemmas.v` | Helper lemmas | Establishes the register, memory, and list invariants required by the main proof. |
| `ThieleUniversal.v` | Universal interpreter proof | Mechanises the fetch/search/apply loop, culminating in the specification exported to `Simulation.v`. |
| `ThieleUniversal_Axioms.v` | Historical notes | Preserves the original proof roadmaps; the axioms described there are now theorems. |
| `ZCPULemmas.v` | Documentation pointer | Links CPU lemmas used across the development. |

## Relationship to the subsumption proof

`Simulation.v` imports the interpreter packaged here and instantiates it as a
blind Thiele Machine.  The encode/decode interface and the step-count lemma
(`utm_simulation_steps`) are proven in this directory and re-exported by the
containment theorem.  Together they deliver the first pillar of the subsumption
result without introducing new axioms.

The directory remains useful beyond subsumption: any experiment that needs a
formal Turing Machine baseline can reuse these components as the canonical
definition of classical computation within the repository.
