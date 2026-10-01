# Ground-truth plan final report

Date: 2026-10-01

This report uses the plan's outcome vocabulary. `PARTIAL` appears only where
R4 requires it for a result whose full real-system or physical claim retains a
missing premise or model. The Part 5--8 commit is the commit containing this
report; a Git commit cannot contain its own hash. The external execution tracker
records that hash after commit creation.

## Outcomes and hollowness checks

R6 columns are D (definitional), B (built in), V (vacuity/instance), S (swap),
and A (independent adversarial read). `pass/scope` means the theorem is valid
but the report explicitly limits a structurally built-in or definitional fact. `fail` marks a check the item's own results record as failed
(2.1's threshold decomposition is true by definition).

| Item | Outcome | Exact result or obstacle | D | B | V | S | A |
|---|---|---|---|---|---|---|---|
| 0.1 | PROVED operationally | repository baseline committed | pass | pass | pass | pass | pass |
| 0.2 | PROVED operationally | gates and isolated rebuild passed | pass | pass | pass | pass | pass |
| 1.1 | PROVED; four rows BOUNDARY; Mu-Chaitin functor REFUTED for the VM, trace-local form PROVED | 472 identities classified; 45 of 49 event-generic rows have their premises discharged on the two-state door machine (five of them use Coq's standard real-number axioms); four keep the physical Landauer premise; trace-local Mu-Chaitin instantiated on one VM run | pass | scope | pass | pass | pass |
| 1.2 | 19 PROVED, 36 REFUTED | every frozen certification-only generalization has a closed wrapper or counterexample | scope | pass | scope | pass | pass |
| 1.3 | REFUTED | universal event swap fails for zero-cost fixed-width graph allocation; certification sanity bundle proved | pass | pass | pass | pass | pass |
| 1.4 | PROVED | 8,156-line publication audit and 41 corrections | pass | pass | pass | pass | pass |
| 1.5 | REFUTED then PROVED | Round 1 found a README overclaim; Round 2 corrected all 40 frozen occurrences | pass | pass | pass | pass | pass |
| 2.1 | PROVED and REFUTED | threshold decomposition proved; single-latch decomposition refuted | fail | scope | pass | pass | pass |
| 2.2 | PROVED and REFUTED | actual revocation lies outside permanence; price-transfer claim refuted | scope | pass | scope | pass | pass |
| 2.3 | REFUTED | probabilistic uniqueness up to schedule fails | pass | pass | pass | pass | pass |
| 2.4 | PROVED | frozen equivalence laws and all four adapters (TM, VM, Cook-Reckhow RAM, L) proved | scope | pass | pass | scope | pass |
| 3.1 | PROVED; Rice PROVED | vm_guest_recursion_theorem_closed: the evaluator relation is extracted to L, compiled to a Minsky machine, run by guest code through the MMA pipeline; the diagonal program is g_pair_specialize e (guest_program_code e); closed under the global context | pass | pass | pass | pass | pass |
| 4.1 | PROVED BUT KNOWN | under exact forced-price class, no price is forced beyond merges | pass | scope | pass | pass | pass |
| 4.2 | PROVED at the logical level; BOUNDARY beyond it | permanent finite write implies logical noninjectivity (permanent_write_has_logical_payment); economic, cryptographic, and heat payment each need a premise about that level | pass | pass | pass | pass | pass |
| 4.3 | REFUTED intrinsic scale; calibration BOUNDARY | mu has no intrinsic joule value (mu_has_no_intrinsic_joule_value); the protocol's count of one mu equals the VM's minimal certification charge, with no state map between the two; joule calibration needs thermal and device premises | pass | pass | pass | pass | pass |
| 4.4 | PROVED BUT KNOWN | conditional finite-state logarithmic heat floor and entropy permutation invariance | pass | pass | pass | pass | pass |
| 5.1 | PROVED boundary checks; BOUNDARY cryptographic premises | RFC 9162 iterative verifier boundary checks close; collision resistance and STH authenticity are cryptographic premises; the full binding statement formalizes RFC 9162 itself and is not pursued | pass | scope | pass | pass | pass |
| 5.2 | PROVED BUT KNOWN toy fragment; full PCC not pursued | toy address-policy checker equivalence and typed-certificate implication close; a full SAL/LF/PCC model formalizes another system and is not pursued | pass | scope | pass | pass | pass |
| 5.3 | PROVED | addressed RAM tied/untied steps and reversible-update cores close; tied and untied RAMs classified on the record axis over one base (RAMRecordAxis.v) | scope | scope | pass | pass | pass |
| 5.4 | REFUTED unconditional authenticity; BOUNDARY trust premise | an unconstrained sign/verify interface does not entail quote authenticity; authenticity needs a trusted-key premise | pass | pass | pass | pass | pass |
| 5.5 | NOT PURSUED | a full embedding of the four named calculi formalizes other systems; the earlier BLOCKED label had no genuine strategies | pass | pass | pass | pass | pass |
| 6.1 | PROVED BUT KNOWN | binary redundant-proliferation measure already formalized | scope | scope | pass | pass | pass |
| 6.2 | PROVED | twelve frozen candidate measurements match predictions | pass | scope | pass | pass | pass |
| 6.3 | MODEL COUNTEREXAMPLE PROVED; real conclusion BOUNDARY | the MAC-labelled event is non-proliferating in the frozen observer map; forgery relevance is a prose premise | pass | pass | pass | pass | pass |
| 6.4 | PROVED | swapped observer map selects the newly proliferating event | pass | scope | pass | pass | pass |
| 7.1 | PROVED operationally | eight fields surveyed | pass | pass | pass | pass | pass |
| 7.2 | PROVED operationally | ten real design questions linked to primary sources | pass | pass | pass | pass | pass |
| 7.3 | PROVED operationally | ten candidates ranked by directness | pass | pass | pass | pass | pass |
| 7.4 | PROVED operationally | top five exact targets frozen with users and literature outcomes | pass | pass | pass | pass | pass |
| 7.5 | five PROVED BUT KNOWN; four BOUNDARY; one not pursued | top-five narrow countermodels close but are known; ranks 6 to 9 need protocol or hardware semantics the specs do not give; rank 10 formalizes full PCC and is not pursued | pass | scope | pass | pass | pass |
| 7.6 | NOT APPLICABLE | no result passed all four acceptance criteria | pass | pass | pass | pass | pass |
| 7.7 | PROVED operationally | next five received three strategies each; ranked list exhausted | pass | pass | pass | pass | pass |
| 8.1 | PROVED operationally | six public documents reconciled to Parts 1--7 outcomes | pass | pass | pass | pass | pass |
| 8.2 | PENDING GATE | final gate and isolated rebuild evidence is filled below | pending | pending | pending | pending | pending |
| 8.3 | PENDING COMMIT | stop before merge or tag | pending | pending | pending | pending | pending |
| 8.4 | PROVED operationally when committed | this report contains items, R6, wrong predictions, calls, and hashes | pass | pass | pass | pass | pass |

## Part 7 practitioner results

None. No candidate passed all four required criteria, so writing a practitioner
paragraph as if one had passed would violate 7.6. The five closed statements
are useful sanity countermodels but do not need the record axis and are already
known from their governing sources.

## Wrong predictions

- Item 1.2 predicted 21 PROVED and 34 REFUTED; actual was 19 and 36. The two
  wrong predictions were generalized billed and surcharged schedule equivalence.
- Item 1.3 predicted the universal swap theorem; a fixed-width graph-allocation
  event refuted it.
- Part 4's first 4.4 formulation was rejected by Inquisitor as tautological and
  replaced only through an immutable later round.
- Part 5.1's example proof draft preceded its second freeze; it remains evidence
  but is not counted as clean preregistration.
- Part 5.3's first “RAM” was only a scalar state. The independent read rejected
  that classification and round 2 supplied addressed list memory.
- Part 7's preliminary rank-8 survey prediction was PROVED BUT KNOWN; the exact
  later target strengthened it to a hardware-model derivation, predicted
  BLOCKED, and remained BLOCKED.
- No other recorded outcome prediction was wrong.

## Calls made on the user's behalf

- Batch commits and full gates at Part boundaries replaced per-item commits,
  while dated freezes, TDD, R2/R4 labels, R6 checks, and final gates remained.
- Contaminated or late freezes were disclosed, never backdated.
- Existing generic writer, potential, and counting lemmas were not renamed as
  full cost-framework embeddings.
- Symbolic Merkle constructors were used only to execute RFC control flow, not
  as collision-resistance evidence.
- The PCC checker was described as a toy role mirror, not Necula's complete
  system; the TPM result was limited to interface insufficiency.
- Part 7 novelty was rejected where primary sources already state the result.
- No practitioner paragraph was fabricated after the ranked list was exhausted.
- No checker, gate, or acceptance threshold was weakened.

## Commits and boundary evidence

- Part 0 operational baseline: `5d1245e6`, `bcd4df1e`.
- Part 1: `0b32407d`, `1b6e8c5b`, `66feb214`, `3f745351`, `10aeb40d`, `d5cb4e7e`.
- Part 2: `dc43689f`.
- Part 3: `2438ae9c`.
- Part 4: `fd953dc1`.
- Parts 5--8: the commit containing this report; recorded externally after creation.

Final gate evidence: PENDING.
