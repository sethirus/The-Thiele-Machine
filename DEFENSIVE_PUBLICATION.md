# Thiele Machine — Defensive Publication (Enabling Disclosure)

Purpose: place enabling prior art into the public domain to prevent patenting of
the architecture and its ordinary embodiments.

Scope (non-exhaustive, intentionally broad):
1. Deterministic, classical VM ("thielecpu") emitting step-receipts with µ-bit ledger.
2. Mechanised replay: receipts -> Coq bridge (concrete_receipts_sound, etc.).
3. Bell/CHSH pipeline achieving 2 < S ≤ 2√2 with rational witnesses; solver-audited.
4. Verilog reference pipeline implementing the same instruction semantics end-to-end.
5. Operation "Cosmic Witness": data-conditioned rule induction with SMT proofs of correctness/robustness.
6. Embodiments: CPU, GPU-style fabric, FPGA, ASIC; in-memory compute; multi-partition; networked co-processors.
7. Variants: different receipt encodings, different solvers (Z3/CVC5), different formal kernels (Coq/Lean/Isabelle),
   alternative µ-bit metering, hardware counters/TPM sealed logs.
8. General method claims: (a) deriving constants with exact arithmetic; (b) enumerating classical bounds with QF_LIA;
   (c) constructing rational Tsirelson witnesses; (d) regenerating Coq obligations from JSON receipts and proving replay.

Artifacts: link the exact git tag (v1.0.1), SHA-256 checksums of source tarballs (883372fd799e98a9fd90f8feb2b3b94d21bf917843745e80351ba52f7cf6d01d), and the Zenodo DOI/SWHID here.

This document is intended to be enabling disclosure: a skilled practitioner can implement the system without undue
experimentation, thereby barring later patents on the same subject matter and routine variations.