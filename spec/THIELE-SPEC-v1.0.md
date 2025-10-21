# Thiele Spec v1.0 (Normative)

> **Status update (October 2025):** This specification is archived; the live μ-cost definition is in `spec/mu_spec_v2.md` and the complete mechanical subsumption proof is in `coq/kernel/SimulationProof.v`.
## 1. Machine Core
- State `S = (Modules, Ledger, Cert, CSRs)`
- Instruction set: PNEW, PSPLIT, PMERGE, LASSERT, LJOIN, MDLACC, EMIT
- Audited small-step: `s --[t,c]--> s'` iff transition `t` valid and certificate `c` verifies.

## 2. μ-bit Meter (Canonical)
- MDL encoding: SMT-LIB2 axioms byte-length + partition description bits.
- μ = μ_operational + μ_discovery; paradox ⇒ μ = ∞.
- Allowed variants: prefix-free encodings differing by at most +K bits. **K is fixed here: K=64.**

## 3. Receipts (Normative JSON)
- Canonical serialization rules: sorted keys, UTF-8, `separators=(",",":")`, no whitespace variability.
- Per-step record and global digest (see schema).
- Verification procedure is **normative** (no alternatives).
- Proof artifact requirement: **SAT ⇒ model_blob_uri required, UNSAT ⇒ proof_blob_uri required (DRAT/LRAT)**

## 4. Soundness/Completeness (Statements)
- **Soundness**: No invalid run can produce receipts that pass §3 checks.
- **Completeness**: Every valid run yields receipts that pass §3 checks.
- Proof obligations: see `coq/SpecSound.v`.

## 5. Order Invariance
- Church–Rosser: different valid orders with same witnesses yield same verdict and μ.
- Operational corollary: identical global digest from semantically equivalent traces.

## 6. Versioning
- This file is v1.0; changes bump minor/major with changelog.