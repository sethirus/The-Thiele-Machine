# Spike Demonstrations for the Thiele Machine

This note distills three "spike" experiments that can be implemented with the existing Thiele Machine toolchain to produce crisp, auditable paradox receipts in distinct domains.  Each demo isolates a single contradiction, proving the broader applicability of the ledger, logic engine, and partition semantics without requiring large-scale brute-force runs.

## Demo A: Verifiable & Auditable AI ("Glass Box")
- **Objective:** Show that the VM can enforce an inviolable safety axiom on a model's output and issue an auditable paradox certificate when the model violates the axiom.
- **Setup:**
  - Partition `AI_ModelOutput` captures JSON emitted by a stub classifier via `PYEXEC`.
  - Partition `SafetyPolicy` stores SMT-LIB axioms formalizing the rule `∀x.\ is_kitten(x) \rightarrow \neg is_dangerous(x)`.
- **Program skeleton:**
  1. `PYEXEC` within `AI_ModelOutput` prints a JSON blob; the VM records the stdout hash and binds it to the partition state.
  2. `LASSERT` evaluates an SMT2 file that asserts both the JSON-derived facts (`(assert (> is_kitten 0.9))`, etc.) and the safety axiom.
  3. The program repeats for multiple inputs; use `MDLACC` after each run to log the µ-bit charge for auditing the policy.
- **Expected results:**
  - Safe inputs lead to `SAT` proofs, and the ledger records finite µ-bit cost with no paradox flag.
  - Contradictory inputs yield `UNSAT`, halting the VM with `paradox_detected = true` and persisting the unsat core as a certificate.
- **Artifacts to emit:** `trace.log`, `summary.json`, and the hashed Z3 certificates demonstrate the paradox detection pipeline end-to-end.

## Demo B: Universal Bug Finder
- **Objective:** Demonstrate that API misuse is a logical contradiction caught before execution, reframing bugs as paradoxes between caller state and callee axioms.
- **Setup:**
  - Partition `Caller` uses `PYEXEC` to define the argument environment (e.g., `x = -9`).
  - Partition `SafeMathLib` holds SMT axioms encoding documented preconditions such as `(assert (>= x 0))`.
- **Program skeleton:**
  1. Load the caller state via `PYEXEC`.
  2. Invoke `LASSERT` with the library's precondition SMT file.
  3. Optionally call `MDLACC` to charge the ledger for validating the contract.
- **Expected results:** Any violation of the precondition produces an immediate paradox with an unsat core pointing to the offending assumption.  Conforming inputs complete with zero paradox and a finite ledger charge.
- **Artifacts to emit:** A minimal `trace.log` that ends on `LASSERT` for the failing case plus the unsat core certificate is sufficient evidence of the machine's bug-finding capability.

## Demo C: Automated Scientist
- **Objective:** Use the VM as a discovery engine that resolves apparent data contradictions by partitioning observations and certifying the simplest consistent theories.
- **Setup:**
  - Reuse the four-point dataset from `attempt.py` to mimic the "hidden color" puzzle.
  - A driver script enumerates candidate partitions and generates per-partition SMT2 constraints representing candidate linear laws.
- **Program skeleton:**
  1. For each candidate theory, synthesize a temporary `.thm` program that issues two `LASSERT` calls—one per partition—to Z3.
  2. Record whether the VM halts normally or with `paradox_detected`.
  3. Invoke `MDLACC` after successful assertions to measure the µ-bit cost of the accepted theory.
- **Expected results:**
  - Most partitions fail with paradox, mirroring rejected scientific hypotheses.
  - The valid partition(s) complete with proofs and finite µ-bit charges, supplying a ledger-backed receipt of discovery cost.
- **Artifacts to emit:** A tabulated run log listing each partition, paradox status, and µ-bit total, plus the associated certificates, constitutes the experimental receipt.

## Implementation Notes
- All demos reuse the existing `thielecpu` modules; no new VM features are required.
- Each `.thm` program should commit its `PYEXEC` outputs, logic results, and ledger updates so that the Ouroboros Seal can hash the entire transcript for reproducibility.
- Publishing the scripts alongside their generated receipts in `results/` will extend the current RSA and Tseitin evidence with additional, domain-specific paradox demonstrations.
