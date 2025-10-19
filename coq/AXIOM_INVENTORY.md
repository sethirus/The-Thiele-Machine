# Foundational Assumptions

> **Status update (October 2025):** The active, axiom-free kernel lives under `coq/kernel/`. This inventory documents the archived `coq/thielemachine` development and remains for historical reference.
**Total Axioms:** 9  
**Admitted Statements:** 0  
**Last Updated:** 2025-10-17

The Coq development for the Thiele Machine isolates nine interface axioms. Each
axiom connects the mechanised proofs to executable artefacts shipped in this
repository. Every entry below records the formal claim, why the axiom is
required, and how the current Python prototype realises the behaviour in
practice.

---

## Blind Interpreter Interface

### Axiom: `decode_encode_id`
**Formal Statement**  
For every program `p`, `decode (encode p) = p` under the canonical encoding used
by the universal blind interpreter (Coq file
`thielemachine/coqproofs/Simulation.v`).

**Justification**  
The containment proof moves between encoded programs and their semantic form.
Round-tripping through the encoder and decoder ensures that the interpreter
operates on the intended program rather than an artefact of the encoding.

**Prototype Realization**  
`thielecpu/assemble.py` implements the instruction encoder/decoder used by the
Python VM. Unit tests in `tests/test_assemble.py` exercise representative
programs, and the migration tooling in `scripts/migrate_legacy_receipts.py`
round-trips receipts through the same encoder. These components operationalise
the axiom until the Coq development proves the round-trip directly.

### Axiom: `utm_catalogue_static_check`
**Formal Statement**  
The boolean guard `catalogue_static_check` succeeds for the catalogued universal
interpreter, providing the witness required by the simulation bounds pipeline.

**Justification**  
The interpreter proof relies on a finite catalogue of digit/write/move
inequalities. Collapsing the witness to a boolean guard avoids re-deriving the
inequalities in every lemma.

**Prototype Realization**  
`docs/encoding/15-UTM-BOUNDS-CATALOG.md` enumerates the inequalities and
`attempt.py` evaluates the guard during the catalogue replay phase. The ledger
and audit logs (for example `audit_logs/demonstrate.log`) capture the boolean
evaluation that substantiates the axiom outside Coq.

### Axiom: `utm_head_lt_shift_len`
**Formal Statement**  
Any configuration presented to the blind interpreter satisfies the strengthened
head bound `tm_config_head < SHIFT_LEN`.

**Justification**  
The strengthened bound keeps the encoded tape inside the modular packing limits
when preservation is replayed. Without it the interpreter could exceed its tape
budget.

**Prototype Realization**  
`attempt.py` constructs interpreter configurations with explicit head margins,
and the VM trace (`audit_logs/attempt.log`) records the guard before simulation
begins. A reduced version of the invariant is checked in `tests/test_vm_halt.py`
by replaying guard failures.

### Axiom: `utm_simulation_steps`
**Formal Statement**  
The abstract universal interpreter simulates a target machine within a bounded
number of interpreter steps per simulated step.

**Justification**  
This axiom underpins the containment theorem relating blind interpreter cost to
the source machine. It keeps asymptotic reasoning sound.

**Prototype Realization**  
`attempt.py` benchmarks the blind interpreter against a ground-truth small-step
model. The resulting traces (see `audit_logs/attempt.log`) provide empirical
upper bounds while the Coq development chases a constructive proof.

---

## Concrete VM Interface

### Axiom: `check_step_sound`
**Formal Statement**  
If the concrete receipts checker accepts a step, that step is a valid transition
under the abstract Thiele semantics (Coq file `thielemachine/coqproofs/ThieleMachine.v`).

**Justification**  
Every replayed receipt relies on this soundness: without it the bridge from
runtime to proof artefacts collapses.

**Prototype Realization**  
The Python implementation in `thielecpu/receipts.py` assembles and verifies
signatures, and `tools/receipts.py` replays the hash chain. Regression tests in
`tests/test_receipts.py` feed canonical and adversarial steps through the
checker, providing empirical support for the axiom.

### Axiom: `check_step_complete`
**Formal Statement**  
Any semantically valid abstract step admits a concrete receipt accepted by the
checker.

**Justification**  
Completeness ensures that constructive proofs can rely on runtime traces without
missing valid transitions.

**Prototype Realization**  
`scripts/migrate_legacy_receipts.py` and the regression suite emit canonical
receipts and confirm acceptance. The audit logs in `audit_logs/demonstrate.log`
and `audit_logs/verify_thiele_machine.log` illustrate full-trace acceptance.

### Axiom: `mu_lower_bound`
**Formal Statement**  
Concrete μ-bit charges recorded in receipts are lower bounds on the abstract
μ-information cost used in the Coq model.

**Justification**  
The computational separation hinges on accurate accounting. Undercharging μ-bits
would invalidate the claimed gap.

**Prototype Realization**  
`spec/mu_spec_v2.md` defines the canonical information-theoretic accounting.
`thielecpu/mu.py` implements the shared calculator that is used by
`thielecpu/vm.py`, the demo pipelines, and the receipt generator.  The ledger
summaries produced by `demonstrate_isomorphism.py` and recorded in
`audit_logs/demonstrate.log` now derive directly from the μ-spec v2.0 rules.

### Retired Axiom: `state_eqb_refl`
The lemma was proved directly in `thielemachine/coqproofs/ThieleMachine.v` on
2025-11-16. It no longer contributes to the trusted base.

---

## Universal Witness Extraction

### Axiom: `pc_29_implies_registers_from_rule_table`
**Formal Statement**  
A specific program-counter value (e.g. 29) corresponds to a deterministically
reconstructed register assignment derived from the universal rule table.

**Justification**  
The universal-machine proof needs a concise bridge between symbolic encodings
and register-level state.

**Prototype Realization**  
The reconstruction pass in `attempt.py` uses the recorded rule table (see
`documents/encoding/`) to materialise register states. The `audit_logs/attempt.log`
transcript records each reconstruction alongside the originating rule entry.

### Axiom: `find_rule_from_memory_components`
**Formal Statement**  
Given the symbolic memory components and encodings, there exists a deterministic
procedure that identifies the corresponding rule in the universal table.

**Justification**  
The universality proof needs this mapping to translate memory snapshots into
rule semantics without replaying the entire search in Coq.

**Prototype Realization**  
`attempt.py` implements the rule finder, and the test harness exercises it over
the recorded universal traces. The resulting lookups are archived in
`audit_logs/attempt.log`, providing executable evidence for the Coq bridge.
