
# FOUNDATIONAL ASSUMPTIONS

**Total Axioms:** 8
**Admitted Statements:** 0
**Last Updated:** 2025-10-10

The Thiele Machine development is mechanised in Coq with a deliberately small
and explicit set of assumptions. The axioms below are interface-level
assumptions that connect the mechanised core to executable artifacts or
summarise reconstruction steps that are pending full constructive proofs. For
each axiom we provide: a precise name, a concise natural-language explanation,
the reason it is needed, potential validation strategies (how an auditor can
test or reduce reliance on the axiom), and a risk assessment.

---

## 1. Blind Interpreter Interface (2 axioms)

**File:** `thielemachine/coqproofs/Simulation.v`

The containment proof packages the universal blind interpreter as an abstract
component. The interpreter is the formalised interface that claims: "given a
canonical encoding of programs, decoding then interpreting yields behaviour
faithful to the encoded semantics, and the interpreter runs within bounded
steps appropriate for simulation arguments."  These axioms connect the Coq
semantic statement to the actual executable interpreter used for replay.

- `decode_encode_id`
	- Explanation: Encoding a program and then decoding it yields the original
		program (up to the canonical representation used in the development).
	- Reason needed: Many simulation and containment lemmas assume a
		round-trip property to align encoded artifacts with the interpreter's
		expected input format.
	- Validation strategies: (a) unit tests comparing encoder/decoder outputs;
		(b) property-based tests (QuickChick/SmallCheck) asserting identity on a
		broad set of generated program encodings; (c) a separate verified
		encoding/decoding implementation to cross-check outputs.
	- Risk assessment: Low-to-medium. This is an implementation-level
		interface; if it fails, the containment proof requires rework but the
		conceptual separation may still hold under a corrected encoding.

- `utm_simulation_steps`
	- Explanation: The abstract universal interpreter simulates a target machine
		within a bounded (reasonably computable) number of interpreter steps per
		simulated step of the target machine.
	- Reason needed: This axiom underlies the containment theorem that a blind
		Thiele interpreter can simulate a Turing machine with predictable cost
		overheads.
	- Validation strategies: (a) empirical benchmarking of the interpreter vs
		a ground-truth small-step interpreter on canonical micro-programs; (b)
		constructing a certified cost model for the interpreter for small program
		classes; (c) formalising a reduced model of the interpreter and proving
		the bound for that reduced model as a way to reduce reliance on the
		axiom.
	- Risk assessment: Medium. This affects asymptotic cost claims in the
		containment direction; strengthening empirical evidence mitigates the
		concern even if a full constructive proof is delayed.

---

## 2. Concrete VM Interface (4 axioms)

**File:** `thielemachine/coqproofs/ThieleMachine.v`

These axioms summarise the behaviour of the concrete checker and μ-accounting
in the production VM and receipts checker. They are intentionally conservative
interface assertions that capture correctness and soundness properties of the
checker rather than full implementations.

- `check_step_sound`
	- Explanation: If the concrete receipts checker accepts a single-step
		receipt, then that step is a semantically valid VM transition according
		to the abstract Thiele semantics.
	- Reason needed: The Coq replay uses the checker to trust runtime steps.
	- Validation strategies: (a) formal verification of the checker; (b)
		exhaustive tests for small step domains and cross-checks with
		an independent reference implementation; (c) proof that the checker is a
		conservative approximation of an executable specification.
	- Risk assessment: High. Unsoundness here undermines the entire bridge
		between runtime and proof artifacts. Mitigation should prioritise
		mechanical checking and strong unit-test coverage.

- `check_step_complete`
	- Explanation: If a step is semantically valid in the abstract semantics,
		then the concrete checker will accept an appropriately formed receipt for
		that step (completeness relative to canonical receipts).
	- Reason needed: Enables proofs that rely on replaying runtime traces to
		re-derive properties proven at the abstract level.
	- Validation strategies: (a) generate canonical abstract steps and ensure
		the checker accepts their assembled receipts; (b) property-based testing
		and fuzzing of receipt encodings; (c) attempt mechanised proof that the
		checker implements the abstract step relation for a reduced subset.
	- Risk assessment: High-to-medium. Completeness failures imply some valid
		steps would not be recorded/accepted, weakening the replay argument; but
		such failures are detectable by targeted test generation.

- `mu_lower_bound`
	- Explanation: Relates concrete accounting (bits charged on receipts) to a
		conservative lower bound on abstract μ-information costs used in proofs.
	- Reason needed: Links runtime accounting (used to claim polynomial
		μ-costs) to the abstract μ-bit model in Coq.
	- Validation strategies: (a) unit tests that check accounting against
		hand-calculated examples; (b) formalise the accounting lemma for a
		restricted family and prove the lower bound constructively for that
		family; (c) independent audit of receipt generation and size metrics.
	- Risk assessment: High. The separation relies on accurate accounting; a
		subtle mismatch would force re-evaluation of empirical claims.

- `state_eqb_refl`
	- Explanation: A convenience axiom asserting that the state equality test
		(`state_eqb`) correctly recognizes identical states (reflexivity on the
		representation used by the checker).
	- Reason needed: Simplifies proofs when comparing snapshots and pre/post
		states in receipts.
	- Validation strategies: (a) property-based tests asserting
		`state_eqb s s = true` for many states; (b) small proof that the equality
		function is correct for a reduced representation.
	- Risk assessment: Low. This is a representation-level convenience axiom
		and is easily testable.

---

## 3. Universal Witness Extraction (2 axioms)

**File:** `thieleuniversal/coqproofs/ThieleUniversal.v`

These axioms capture the final bridges used in the universal-machine
reconstruction. They are engineering/porting assumptions that stand in for
symbolic search and rule-table decoding steps that are being mechanised.

- `pc_29_implies_registers_from_rule_table`
	- Explanation: In the universal reconstruction, a program counter value
		(e.g., 29) corresponds to a specific distribution of registers derived
		deterministically from the universal rule table.
	- Reason needed: Allows compact statements that reconstruct register-level
		state from a table-driven encoding without expanding the full symbolic
		search in the proof.
	- Validation strategies: (a) formalise and prove the decoding lemma for a
		subset of rules; (b) test the reconstruction on the concrete universal
		program traces produced by the interpreter.
	- Risk assessment: Medium. This is targeted to the universal-machine
		construction; if it fails, the universal embedding needs refinement but
		other separation derivations may remain intact.

- `find_rule_from_memory_components`
	- Explanation: Given a set of memory components and encodings, there is a
		deterministic procedure that finds the corresponding rule in the
		universal table.
	- Reason needed: Bridges symbolic memory encodings and the universal
		instruction semantics in the proof of universality.
	- Validation strategies: (a) unit-tests for the rule-finder; (b) a
		constructive proof for small, canonical memory encodings; (c) independent
		cross-checks with the runtime universal interpreter.
	- Risk assessment: Medium.

---

## Ledger and mitigation priorities

To help auditors triage work, the following short ledger ranks axioms by
urgency for removal or mechanisation:

1. `check_step_sound` — high priority. Mechanise or independently verify
	 the receipts checker; without this the runtime→proof bridge is fragile.
2. `check_step_complete` — high priority. Completeness ensures proofs
	 reflect all valid runtime steps.
3. `mu_lower_bound` — high priority. Core to the μ-bit accounting used in the
	 separation argument.
4. `utm_simulation_steps` — medium priority. Formalising the interpreter cost
	 model is desirable for a containment theorem with fully constructive
	 costs.
5. `pc_29_implies_registers_from_rule_table` — medium priority for the
	 universal-machine formalisation.
6. `find_rule_from_memory_components` — medium priority.
7. `decode_encode_id` — low priority; unit tests and a verified encoder/decoder
	 reduce the risk quickly.
8. `state_eqb_refl` — low priority; easy to validate with property tests or
	 small mechanised lemmas.

Auditors should prioritise constructing mechanised proofs or independent
verification harnesses for the top-priority axioms; the repository includes
unit-test scaffolding and example receipts to assist that work.

---

If you discover a counterexample to an axiom, open an issue referencing the
axiom label, the minimal counterexample (or test case), and the proposed
resolution path (fixing the runtime, providing a mechanised proof for the
reduced fragment, or replacing the axiom with a weaker statement). The project
maintainer commits to triage and respond to such reports.
