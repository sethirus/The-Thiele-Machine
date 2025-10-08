# FOUNDATIONAL ASSUMPTIONS

**Total Axioms:** 19  
**Admitted Statements:** 0  
**Last Updated:** October 2025

---

The Thiele Machine development is now completely mechanised in Coq with the
exception of the deliberately documented assumptions listed below.  Every
legacy "pending mechanisation" or "technical utility" axiom has been replaced
by a proven lemma—most notably the universal interpreter's rule-search loop
(`find_rule_loop_preserves_inv`, `pc_29_implies_registers_from_rule_table`, and
`find_rule_from_memory_components`) and the concrete machine existence theorem
(`ConcreteThieleMachine_exists`).  What remains are the foundational premises
that tie the formal model to external theory or executable artefacts.

---

## 1. Complexity-Theoretic Assumption (1 axiom)

### `turing_tseitin_is_exponential`  
**File:** `thielemachine/coqproofs/Separation.v`

> Blind DPLL-style search on Tseitin expanders requires exponentially many
> steps.

This is the standard lower-bound hypothesis drawn from decades of
proof-complexity literature (Haken 1985; Ben-Sasson & Wigderson 2001).  The
strictness pillar (`Separation.v`) depends on it to compare blind and sighted
architectures.

---

## 2. Quantum Non-Locality Model (8 axioms)

**File:** `thielemachine/coqproofs/BellInequality.v`

These axioms introduce the Bell/CHSH framework used when reasoning about the
μ-accounting of non-classical oracles.  They encode accepted physical facts
(local bounds, no-signalling constraints, and the properties of the PR box):

- `local_deterministic_CHSH_bound`
- `local_CHSH_bound`
- `PR_norm`
- `PR_nonneg`
- `PR_nosig_A`
- `PR_nosig_B`
- `PR_S`
- `PR_not_local`

---

## 3. Structured Benchmark Families (4 axioms)

**File:** `thielemachine/coqproofs/StructuredInstances.v`

The structured-instance library summarises empirical benchmark families used by
the Python tooling.  Each axiom names a family and records the intended
performance gap; they function as specifications for the data shipped in
`spec/golden/`.

- `tseitin_speedup_example`
- `modular_circuit_speedup`
- `coloring_structure_exploitation`
- `structured_classes_exist`

---

## 4. Blind Interpreter Interface (2 axioms)

**File:** `thielemachine/coqproofs/Simulation.v`

The containment proof packages the universal blind interpreter as an abstract
component.  The following axioms characterise its encode/decode interface and
bounded execution semantics:

- `decode_encode_id`
- `utm_simulation_steps`

They tie the Coq development to the executable interpreter in the Python VM;
mechanising them would amount to formally verifying that implementation.

---

## 5. Concrete VM Interface (4 axioms)

**File:** `thielemachine/coqproofs/ThieleMachine.v`

The abstract Thiele Machine relies on four interface axioms that summarise the
behaviour of the concrete checker and μ-accounting used in production code:

- `check_step_sound`
- `check_step_complete`
- `mu_lower_bound`
- `state_eqb_refl`

These axioms stand in for a fully verified implementation of the concrete VM
and receipts checker.  The surrounding Coq development—the separation proof,
containment theorem, and subsumption capstone—now rests entirely on the
assumptions listed in this document.
