# Part 7 top-five round 1 freeze: real-system consequences

Date: 2026-10-01

The field survey ranks ten candidates by directness to proved projection,
permanence, and verifier results. The exact top-five Coq targets are frozen in
`RealSystemConsequencesTarget.v`, SHA-256
`3b7115c48ab170b80d582dbca381d5be1ffe410cc19f7bd8fe742c5deb46642d`.
Receipt label: `real-system-consequences-target.v.sha256`.

The exact propositions are:

1. `ct_local_view_cannot_decide_global_consistency`.
2. `incomplete_quote_check_accepts_selection_mismatch`.
3. `suffix_cannot_decide_trusted_anchor`.
4. `ack_without_durable_commit_can_be_lost`.
5. `current_local_log_cannot_decide_history`.

Primary specifications and reports are linked in the survey. Each target is a
narrow countermodel to a local-information or missing-durability claim, not a
complete protocol model.

Predictions: all five exact propositions are PROVED BUT KNOWN. RFC 9162 already
says global-view consistency requires sharing log responses and leaves gossip
undefined. The TPM2-tools advisory documents the PCR-selection binding flaw.
Ethereum's spec requires a recent out-of-band checkpoint. WAL documentation
states the durability ordering. NIST identifies log integrity, availability,
and distributed retention as existing log-management problems. Therefore none
is predicted to pass Part 7 novelty criterion (c), even if the Coq statement
closes.

Success: prove the five frozen statements, retain their known status, then
assess ranks 6--10 without manufacturing novelty. Failure: calling a two-state
information counterexample a complete security proof or claiming novelty over
the cited specifications.

