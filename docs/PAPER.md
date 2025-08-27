# Toward a Thiele Machine

## Introduction
This note summarises the current state of the Thiele Machine project. The aim is to model computation where discovery cost is explicit.

## Formal Definitions
Core definitions and the role of the logic oracle are collected in [SPECIFICATION.md](SPECIFICATION.md).

## Proof Sketches
- A Thiele CPU executing `RunTMStep` faithfully simulates a single transition of the encoded Turing machine【F:coq/thielemachine/coqproofs/ThieleMachine.v†L176-L188】.
- If the oracle reports a contradiction, the accumulated μ-cost becomes infinite【F:coq/thielemachine/coqproofs/ThieleMachine.v†L190-L199】.
- The universal program admits an existential subsumption theorem: for any number of TM transitions there exists a CPU state representing the same configuration【F:coq/thieleuniversal/coqproofs/ThieleUniversal.v†L254-L263】.  A concrete operational simulation proof remains open.

## Experimental Setup
Two small experiments accompany the proofs. `attempt.run_engine_and_law()` explores partitions of a paradox, and `run_single_experiment` solves structured Tseitin instances. The helper script `scripts/run_all_experiments.py` reproduces all receipts in one pass across multiple problem sizes. Details appear in [EXPERIMENTS.md](EXPERIMENTS.md).

## Results and Conclusions
The engine finds multiple valid partitions with finite MDL, while the blind model incurs infinite information debt【F:results/engine_output.txt†L24-L34】【F:results/engine_output.txt†L56-L58】. The Tseitin experiments show a tangible gap between blind and sighted reasoning across sizes 8, 10 and 12【F:results/tseitin_output_n8.json†L1-L19】【F:results/tseitin_output_n10.json†L1-L19】【F:results/tseitin_output_n12.json†L1-L19】. Together, these pieces outline a roadmap: extend the oracle, prove universality, and investigate whether Thiele machines truly outrun classical models.
