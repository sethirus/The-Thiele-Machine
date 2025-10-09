# FOUNDATIONAL ASSUMPTIONS

**Total Axioms:** 8
**Admitted Statements:** 0
**Last Updated:** October 2025

---

The Thiele Machine development is now completely mechanised in Coq with the
exception of the deliberately documented assumptions listed below.  The quantum
non-locality scaffolding, structured-instance placeholders, and classical lower
bound previously recorded here have all been replaced by constructive proofs.
What remains are the interface axioms that connect the mechanised core to
executable artefacts and the historical universal-machine reconstruction.

---

## 1. Blind Interpreter Interface (2 axioms)

**File:** `thielemachine/coqproofs/Simulation.v`

The containment proof packages the universal blind interpreter as an abstract
component.  The following axioms characterise its encode/decode interface and
bounded execution semantics:

- `decode_encode_id`
- `utm_simulation_steps`

They tie the Coq development to the executable interpreter in the Python VM;
mechanising them would amount to formally verifying that implementation.

---

## 2. Concrete VM Interface (4 axioms)

**File:** `thielemachine/coqproofs/ThieleMachine.v`

The abstract Thiele Machine relies on four interface axioms that summarise the
behaviour of the concrete checker and μ-accounting used in production code:

- `check_step_sound`
- `check_step_complete`
- `mu_lower_bound`
- `state_eqb_refl`

These axioms stand in for a fully verified implementation of the concrete VM
and receipts checker.  The module signature `ThieleMachineSig.v` restates them as
part of the interface, but they represent the same four assumptions listed
above.

---

## 3. Universal Witness Extraction (2 axioms)

**File:** `thieleuniversal/coqproofs/ThieleUniversal.v`

The historical universal-machine reconstruction still relies on two interface
axioms while its symbolic search procedures are being ported to constructive
proofs:

- `pc_29_implies_registers_from_rule_table`
- `find_rule_from_memory_components`

They summarise the final missing bridge between the universal instruction table
and the concrete register-level reconstruction in the classical proof.  All
other axioms referenced in earlier documentation have now been eliminated in
favour of explicit constructive witnesses.
