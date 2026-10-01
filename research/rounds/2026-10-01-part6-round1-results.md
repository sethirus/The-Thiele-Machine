# Part 6 results: the pointer question

Date: 2026-10-01

| Item | Outcome | Exact result |
|---|---|---|
| 6.1 | PROVED BUT KNOWN | Existing `records`, `redundantly_proliferating`, and `unique_pointer_among` give the precise binary measure. |
| 6.2 | PROVED | `twelve_candidate_measurements_checked` proves all twelve frozen predictions; the TSV records every result. |
| 6.3 | MODEL COUNTEREXAMPLE PROVED; real-system conclusion MODEL-DEPENDENT | The event labeled MAC authenticity does not proliferate in the frozen observer map. Treating it as forgery-relevant and as a counterexample to the real-system strong criterion is a separate modeling premise. |
| 6.4 | PROVED | `swapped_event_is_pointer_checked` makes the second event, not the originally named first event, the unique pointer when fragments mirror it. |

Every prediction matched. The formal results are observer-map calculations.
Whether a map faithfully represents a deployed system remains a modeling judgment;
Coq does not establish deployment, independent evolution, or
cryptographic security. The measurements nevertheless answer the frozen
question without selecting events after the result.

## Hollowness checks

- 6.1: definitional by design and labeled PROVED BUT KNOWN; the toy witness in
  `PointerObservable.v` supplies satisfiability; swapping names alone changes
  nothing.
- 6.2: five positive projections are built to mirror their selected bit, so
  positive rows are structural. Six negative rival rows and the MAC row have
  explicit distinguishing states. All twelve candidates exist.
- 6.3: not definitional; one in-range blind observer refutes universal
  proliferation. It refutes only the modeled strong criterion, not a theorem
  of cryptographic security.
- 6.4: the second event proliferates by construction, while an explicit state
  refutes first-event proliferation. This is the required swap behavior.
- Adversarial read: PASS only with the modeling-judgment limitation above and
  with Chapter 26 remaining a conjectural empirical interpretation.

Literature call: public verifiability, MAC key restriction, CT replication,
PCC checking, consensus finality, and attestation precede this project. No
novelty is claimed for their individual structural readings.
