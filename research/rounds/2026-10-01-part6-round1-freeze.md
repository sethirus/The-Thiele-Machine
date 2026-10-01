# Part 6 round 1 freeze: the pointer question

Date: 2026-10-01

## Exact definitions and statements

`PointerObservable.v` already defines `records`,
`redundantly_proliferating`, and `unique_pointer_among`. The operational
measure in this round is binary per named observer map: an event measures YES
exactly when every in-range observer fragment decides it, and NO when a witness
observer/state breaks that condition.

The exact twelve-result conjunction and swap theorem are frozen in
`RecordProliferationSurveyTarget.v`, SHA-256
`fb9a7d09e247f005a87a941a47553a3392ea59384f14e254353de2bc54b3e989`.
Receipt label: `record-proliferation-survey-target.v.sha256`.
The propositions are `twelve_candidate_measurements` and
`swapped_event_is_pointer`.

The twelve candidates are finalized block, proposer work, committed gas state,
scratch work, TEE attestation, TEE measurement noise, CT inclusion, CT prover
effort, checked PCC certificate, PCC prover effort, MAC authenticity, and
digital-signature authenticity. These span five deployed-discipline
projections plus the adversarial authentication controls. Part 5's detailed CT,
PCC, and TPM results constrain the prose reading; this round reuses the already
frozen observer projections rather than pretending their Boolean flags are the
full protocols.

## Predictions

Predicted measurements, in order: YES, NO, YES, NO, YES, NO, YES, NO,
YES, NO, NO, YES. Predicted 6.3 formal outcome: MODEL COUNTEREXAMPLE PROVED;
the event labeled MAC authenticity does not proliferate in the frozen observer
map. Treating that event as forgery-relevant, and therefore as a counterexample
to the real-system strong criterion, is a separate modeling premise. Predicted
6.4 outcome: PROVED; changing
the mirrored field from the first event to the second must make the second the
unique pointer.

Success: closed Coq proofs of both exact propositions, a twelve-row table, and
explicit separation of formal observer-map calculations from real-system
modeling judgments. Failure: fewer than twelve candidates, selecting winners
after seeing unrecorded predictions, or claiming Coq proves deployment facts.
