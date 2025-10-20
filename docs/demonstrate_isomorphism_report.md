> **ARCHIVAL NOTICE:** This document is preserved for historical context. The final, unified proof and analysis are now complete. For the authoritative summary, see `README.md` and `docs/final_fact_check.md`.

# Demonstrate Isomorphism: Formal Thesis Report

> **Status update (October 2025):** This document is preserved for historical context. For the current analysis of the kernel, μ-spec v2.0, and reproducible evidence see `docs/kernel_analysis.md` and `docs/final_fact_check.md`.

## Abstract
This report documents the full execution of `demonstrate_isomorphism.py`, the six-act dissertation that accompanies the Thiele Machine case study. The script orchestrates numerical derivations, solver-backed audits, mechanised receipt replay, and cosmological prediction proofs while emitting an auditable Markdown ledger. Each act is summarised together with its evidence sources, solver guarantees, and reproducibility controls.

## Experimental Environment
* **Deterministic controls** – The run pins `TZ`, `LC_ALL`, `LANG`, and `PYTHONHASHSEED` before any acts execute, recording the overrides in the ledger so replays inherit the exact locale and hashing behaviour.【F:demonstrate_isomorphism.py†L130-L147】【F:BELL_INEQUALITY_VERIFIED_RESULTS.md†L4-L19】
* **Formal toolchain** – Python 3.12.10, Z3 4.15.3 (CLI), and Coq 8.18.0 are captured alongside the repository commit hash, giving auditors concrete binaries to reproduce the proofs.【F:demonstrate_isomorphism.py†L150-L187】【F:BELL_INEQUALITY_VERIFIED_RESULTS.md†L12-L17】
* **Network policy** – Operation Cosmic Witness defaults to offline mode; attempting a live fetch without `--allow-network` aborts, and the ledger records the enforced isolation.【F:demonstrate_isomorphism.py†L1601-L1670】【F:BELL_INEQUALITY_VERIFIED_RESULTS.md†L18】
* **Artifact binding** – After all acts complete, the script emits a SHA-256 manifest covering the ledger, prediction receipt, and SMT certificates so later audits can confirm bit-for-bit integrity.【F:demonstrate_isomorphism.py†L1064-L1074】【F:BELL_INEQUALITY_VERIFIED_RESULTS.md†L569-L572】【F:artifacts/MANIFEST.sha256†L1-L5】

## Trusted Computing Base
The workflow explicitly scopes its trust assumptions: Coq’s kernel (and `coqc`) for receipt replay, Z3’s QF_LIA engine with optional CVC5 corroboration, Python’s exact `Decimal`/`Fraction` arithmetic, and the filesystem delivering the recorded manifest hashes.【F:BELL_INEQUALITY_VERIFIED_RESULTS.md†L20-L26】【F:demonstrate_isomorphism.py†L150-L204】 Auditors need only accept these components; everything else is mechanically verified.

## Act I – Deriving the Constants
The first act derives witnesses for π and √2 using the Chudnovsky and Babylonian methods, then multiplies the latter to obtain the Tsirelson bound 2√2. These sequences furnish rational anchors that all later comparisons reference.【F:BELL_INEQUALITY_VERIFIED_RESULTS.md†L27-L45】【F:demonstrate_isomorphism.py†L600-L625】

## Act II – Classical Deterministic Bound
All sixteen deterministic CHSH strategies are generated, rendered as SMT-LIB, and shown unsatisfiable by Z3 when a violation `|S| > 2` is asserted. The convex-hull query over all strategies is likewise UNSAT, and the script is prepared to cross-check every certificate with CVC5 when the binary is present.【F:demonstrate_isomorphism.py†L626-L685】【F:BELL_INEQUALITY_VERIFIED_RESULTS.md†L46-L447】 Convex coverage is then closed mechanistically by the Coq lemma `local_CHSH_bound`, proving every local box—including probabilistic mixtures—respects the classical ceiling.【F:coq/thielemachine/coqproofs/BellInequality.v†L701-L707】

## Act III – Tsirelson Witness Construction
A rational approximation `γ = 1/√2` is constructed symbolically, yielding a CHSH value strictly between 2 and 2√2. Z3 validates the witness, and (when available) CVC5 is asked to agree, demonstrating that the approximation approaches the Tsirelson bound while remaining auditably rational.【F:demonstrate_isomorphism.py†L688-L724】【F:BELL_INEQUALITY_VERIFIED_RESULTS.md†L448-L480】

## Act IV – Consolidated Ledger
The narrator collates the transcripts from the first three acts into the canonical ledger `BELL_INEQUALITY_VERIFIED_RESULTS.md`, ensuring that every intermediate computation is preserved for downstream audit and hashing.【F:demonstrate_isomorphism.py†L726-L733】【F:BELL_INEQUALITY_VERIFIED_RESULTS.md†L1-L480】

## Act V – Receipt Verification
Fresh execution receipts are regenerated, signatures are revalidated, and a Coq proof script is synthesised. The helper shell script compiles the Thiele Machine modules up front so `coqc` can replay the canonical receipts without missing `.vo` artifacts.【F:scripts/verify_truth.sh†L1-L47】 The ledger records the receipt schema, the successful mechanised replay, and the policy that only canonical JSON layouts are accepted.【F:BELL_INEQUALITY_VERIFIED_RESULTS.md†L512-L546】

## Act VI – Operation Cosmic Witness
A cosmological sample is ingested (falling back to the embedded Planck patch when HEALPix tooling is absent) and distilled into interpretable features. The induced rule, its provenance, the correctness proof, and a robustness certificate over the recorded ε-ball are all logged and persisted as SMT-LIB files and a JSON receipt.【F:demonstrate_isomorphism.py†L1579-L1712】【F:BELL_INEQUALITY_VERIFIED_RESULTS.md†L548-L565】【F:RESULTS.md†L1-L23】 “Correctness” captures that the rule outputs the logged CHSH setting, while “robustness” proves the prediction remains stable under the documented noise model.

## Conclusion
The thesis run is accepted only when every SMT-LIB obligation reproduces its recorded disposition, the Coq replay finishes without error, and the artifact manifest’s hashes match recomputed values.【F:demonstrate_isomorphism.py†L1050-L1074】【F:BELL_INEQUALITY_VERIFIED_RESULTS.md†L566-L572】 With those gates satisfied, `demonstrate_isomorphism.py` delivers a hostile-auditor-ready reproduction package spanning classical limits, quantum witnesses, mechanised receipts, and Operation Cosmic Witness.