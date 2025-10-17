# Formal Guarantees and Axiomatic Bridge

## What is Formally Proven

The Coq development provides machine-checked proofs that the Thiele Machine
implements the small-step semantics, receipt replay, and μ-bit accounting model
described in the accompanying papers—**assuming** the axioms declared in
`coq/thielemachine/Axioms.v` hold. Under these assumptions the proof stack shows
that:

* any classical Turing machine can be simulated by the blind interpreter with a
  predictable step overhead;
* canonical receipts accepted by the checker correspond to valid VM transitions;
* μ-bit charges recorded during execution are sufficient for the abstract
  information model; and
* the universal reconstruction theorems bridge symbolic encodings to concrete
  register states.

These properties are fully mechanised and replayable via the Coq scripts in
`coq/thielemachine/coqproofs/`. The hardened toolchain compiles on Linux with
Coq 8.18.0, and `scripts/verify_thiele_machine.py` invokes the proofs using the
system `coqc` without platform-specific paths.

## The Axiomatic Bridge to the Prototype

The Python reference implementation realises the axioms as documented in
`coq/AXIOM_INVENTORY.md`. The inventory now records, for each assumption:

* the precise Coq axiom identifier (e.g. `decode_encode_id`),
* its justification inside the proof,
* the concrete runtime component that attempts to realise the behaviour, and
* the Ed25519-signed receipts or compression-derived μ-bit ledgers that provide
  observable evidence.

Auditors can reproduce the evidence underpinning each assumption by following
the audit logs in `audit_logs/`, re-running the orchestrators after `pip install
-e .`, and executing `scripts/verify_receipt.py`/`scripts/challenge.py` to
confirm signature and μ-bit integrity. When a formal proof replaces an axiom,
the inventory will retire the entry and the new proof artifact will appear
alongside the existing Coq modules.
