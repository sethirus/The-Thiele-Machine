# Supplementary Proofs and Parity Checks

This directory collects the artefacts requested for the bounded-model µ-ledger
proof and the cross-compilation of FPGA run logs.

* `mu_ledger_conservation.md` summarises the Coq development that formalises
  per-step µ-conservation for bounded executions.
* `fpga_parity.md` documents the log cross-compilation pipeline and the
  resulting parity report (`hardware_software_parity.json`).
* `cross_compile_fpga_logs.py` is the script that translates the synthesis log
  into the structured parity report consumed by the documentation.
