# Part 7 results: consequences outside the framework

Date: 2026-10-01

No candidate passed all four criteria. The ranked list is exhausted after ten
candidates. This is a negative research result, not permission to advertise a
generic projection lemma as a new systems theorem.

## Items 7.1--7.7

- 7.1 PROVED operationally: the survey covers transparency logs, blockchain
  finality, remote attestation, database WAL, audit trails, persistent storage,
  storage energy, and PCC.
- 7.2 PROVED operationally: each row states a concrete design question or
  specification gap and links a primary RFC, specification, advisory,
  standards page, documentation page, or original thesis.
- 7.3 PROVED operationally: all ten are ranked by directness to projection
  collision, permanence, pricing/calibration, or verifier results.
- 7.4 PROVED operationally: the first five exact statements were frozen before
  proof with users and literature outcomes predicted.
- 7.5: the top five exact Coq statements are PROVED BUT KNOWN. They also fail
  criterion (a), because each is a generic two-state collision or durability
  counterexample that does not need the record axis to state or prove.
- 7.6 NOT APPLICABLE: there is no result passing (a)--(d), so no qualifying
  practitioner paragraph is written.
- 7.7 PROVED operationally: ranks 6--10 were frozen, received three strategies
  each below, and remain BLOCKED; the list exhausted condition is reached.

## Top-five exact results and novelty checks

1. CT local view, PROVED BUT KNOWN. `ct_local_view_insufficient` exhibits two
   worlds with one STH and different global consistency. RFC 9162 Section 11.3
   already says checking global consistency requires sharing responses and
   leaves gossip as active research.
2. TPM selection binding, PROVED BUT KNOWN.
   `tpm_selection_binding_is_necessary` exhibits an incomplete digest-only
   checker accepting mismatched selections. The tpm2-tools advisory
   GHSA-8rjm-5f5f-h4q6 documents precisely this verifier class and its fix.
3. Weak subjectivity, PROVED BUT KNOWN.
   `weak_subjective_suffix_insufficient` exhibits equal local suffixes with
   different trusted-anchor labels. Ethereum's weak-subjectivity guide already
   requires a recent checkpoint obtained out of band.
4. WAL durability, PROVED BUT KNOWN. `wal_ack_requires_durability` exhibits an
   acknowledgement with no durable commit record. PostgreSQL 18 Section 28.3
   states WAL must be flushed to permanent storage before the dependent data
   and that flushing WAL guarantees commit.
5. Audit history, PROVED BUT KNOWN. `audit_local_snapshot_insufficient`
   exhibits one state where `audit_event_occurred = true` and another where it
   is `false`, both having the same `audit_current_local_log` bit. NIST SP 800-92 already treats confidentiality, integrity,
   availability, retention, and distributed log management as core problems.

## Hollowness checks for ranks 1--5

For each theorem: (a) it is a genuine two-witness contradiction or concrete
counterexample, but mathematically elementary; (b) the hidden Boolean is not
available to the decision function, while the TPM and WAL witnesses deliberately
omit required checks; (c) both sides of every collision and every accepted bad
state are explicit inhabitants; (d) swapping field names preserves the generic
collision, proving these are structural and not system-name results; (e) the
adversarial reading is PASS only with “narrow model” and PROVED BUT KNOWN. None
is a full security, consensus, database, or audit-log theorem.

## Ranks 6--10, three strategies each

6. CT gossip, BLOCKED. Strategy 1 used the local-view collision, proving only
necessity of communication. Strategy 2 considered pairwise STH exchange but
lacked topology, scheduling, and privacy semantics. Strategy 3 followed RFC
9162's full adversarial goal, but the RFC explicitly leaves gossip undefined;
a protocol and security definition are needed.

7. Checkpoint distribution, BLOCKED. Strategy 1 proved suffix insufficiency.
Strategy 2 modeled a trusted provider bit, which defines trust into a premise.
Strategy 3 attempted to follow the consensus guide, whose distribution section
does not specify a protocol. Provider identity, freshness, compromise, and
network assumptions are needed.

8. Persistent-memory barriers, BLOCKED. Strategy 1 treated `pmem_wmb` as an
axiom, violating R4. Strategy 2 reduced it to list ordering, losing cache and
durability domains. Strategy 3 sought a platform model in the repository; none
models flush completion or power failure. A verified hardware persistence model
is needed. The operational contract itself is known Linux documentation.

9. Storage energy calibration, BLOCKED. Strategy 1 reused the conditional
Landauer scale, which is not a device measurement. Strategy 2 mapped μ to one
Emerald metric by definition, violating the calibration target. Strategy 3
sought measurements, but none were performed and workload/device parameters
are absent. Physical experiments and a correspondence model are needed.

10. Complete PCC embedding, BLOCKED. Strategy 1 reused the toy address checker,
which is not SAL/LFi. Strategy 2 reused the carried-natural wrapper, which
stipulates honesty. Strategy 3 scoped the original thesis components, revealing
missing SAL execution, VC generator, LFi typing, and both soundness translations.
Those formal source systems and VM adapters are needed.

Wrong prediction: the survey's preliminary rank-8 prediction was PROVED BUT
KNOWN; the later exact target strengthened the question to a formal
hardware-model derivation, predicted BLOCKED, and remained BLOCKED. Calls made:
reject novelty for all five closed statements; do not write a 7.6 action
paragraph; exhaust the frozen ten-row list instead of extending it opportunistically.
