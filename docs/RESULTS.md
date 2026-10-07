# Results

This file states the settled results about the small machine, Thiele
completeness, the universal machine, the record axis and the events it can
carry, recursion and undecidability, pricing and physics, and the real systems
the repository models. Further settled results are stated, with their premises
and declarations, in the mathematical specification
(monograph/thiele_machine_math_spec.tex) and are not repeated here: the CHSH bounds and the bound named for Boris Tsirelson, who showed
in 1980 that quantum correlations give a CHSH value of at most 2√2, the lifting of every universal base of every model of
computation, the composition of Thiele-complete machines, the priced host's
program U_P and the computably presented machines it runs, the verified
compiler and its extraction to OCaml, the theorem of the logician Henry Rice (1953) and the recursion
theorem of the logician Stephen Kleene (1938) for the two-counter machine, the record over any order, and the results showing that
each premise and each clause is needed. Each result below names the Coq
declarations that carry it and has one of four statuses:

- **Proved.** A Coq theorem states the result.
- **Refuted.** A Coq theorem states its negation, and a named declaration
  supplies the counterexample.
- **Conditional.** A Coq theorem states the result under a named premise
  that no machine fact discharges. The premise is a hypothesis of the
  statement; no axiom is added for it.
- **Not formalized here.** The question lies outside the formal development.
  The reason is given in one line.

Every theorem cited below is closed under the global context, except the ones
listed under "Standard-library axioms" at the end, which use only the Coq
standard library's real-number, classical-logic and functional-extensionality
axioms. No cited theorem uses a project axiom. `tests/test_results_doc.py`
checks that every cited declaration exists in `coq/` or `minimal/` and that
each cited theorem's axiom status (closed, or using only the standard-library
axioms listed at the end) agrees with the assumption receipt in
`artifacts/print_assumptions_all_proofs.txt`, which the receipt generator
writes on Linux.

## The small machine

The small machine of minimal/EarnedCore.v has two counters, a table of
checked facts, a certification flag and a ledger. Its counter instructions are
a two-counter machine and cost nothing; CHECK, COMMIT and CERTIFY cost one
each.

- **Proved.** From a clean start, every certified run contains a passing
  CHECK, then a passing COMMIT of that same claim with the counter untouched
  in between, then CERTIFY. Coq: `earned_certification_provenance`.
- **Proved.** On a run from a clean start, a fact whose counter has not been
  written since its check names a true claim about that counter.
  Coq: `checker_soundness`.
- **Proved.** From a clean start a certified run costs at least three, and
  three is reached. Coq: `certified_run_min_cost`, `min_cost_tight`.
- **Proved.** The showcase check can fail, and a run whose check fails is
  refused forever. Coq: `earned_run_check_can_fail`,
  `earned_run_refused_forever`.
- **Proved.** The machine runs any two-counter program, halting exactly when
  the program halts. Coq: `simulation_run`, `halting_correspondence`.
- **Proved.** Its halting problem is undecidable, by reduction from the
  vendored two-counter result; it satisfies the certification floor, is
  adequate as a record-carrying machine, is an honest extension of its base
  (program and core, everything but the ledger and the flag), and moves its
  record as a latch. Coq: `earned_core_halting_undecidable`,
  `earned_core_floor`, `earned_core_adequate`, `earned_core_honest`,
  `earned_core_is_latch`.
- **Proved.** For the machine over any property language with an exact
  equality test and a proved checker, provenance, checker soundness, no
  forging, the floor and the minimum cost of three hold, and its
  certification system is sound. Sorted lists are one instance, with a run
  that certifies and a run that is refused. Coq:
  `generic_earned_certification_provenance`, `generic_checker_soundness`,
  `generic_no_forging`, `generic_nfi_floor`, `generic_certified_run_min_cost`,
  `earned_generic_cs_sound`, `sorted_cs_sound`, `sorted_cs_demo_certifies`,
  `sorted_cs_demo_refused`.

## Thiele completeness

A machine is weakly Thiele-complete when a step that raises its record costs
at least one and its base is universal. Thiele-complete
asks for four clauses (minimal/ThieleComplete.v): a universal base whose moves
are free and cannot touch the record; a record that rises only after a passing
check of a claim, a commitment to that same claim with nothing it is about
changed in between, and a certificate; an exact toll, one mark for each of
those three acts and nothing for anything else; and a claim whose check could
have failed.

- **Proved.** The small machine is Thiele-complete, and so are the same
  machine over any property language with an exact equality test, a proved
  checker and some property true of one number and false of another, and the
  sorted-list machine.
  Coq: `earned_core_thiele_complete`, `earned_generic_thiele_complete`,
  `sorted_machine_thiele_complete`.
- **Proved.** In every Thiele-complete machine the ledger counts the record
  moves, a certificate costs at least three, the claim a certificate stands
  on holds at its CHECK and still holds at its COMMIT, the check can fail,
  some run certifies, and only CERTIFY raises the record.
  Coq: `ledger_counts_record_moves`, `certificate_costs_three`,
  `committed_claim_holds` (the theorem of that name in `ThieleComplete.v`),
  `check_can_fail`, `some_run_certifies`, `only_certify_raises`.
- **Refuted.** Weak Thiele completeness implies Thiele completeness. Every
  clock-style machine is weakly Thiele-complete and fails the definition,
  whatever its record; so do a latched clock, a paid latch and a silent
  machine. Coq: `clock_weakly_thiele_complete`, `clock_not_thiele_complete`,
  `latch_clock_weakly_thiele_complete`, `latch_clock_not_thiele_complete`,
  `paid_latch_weakly_thiele_complete`, `paid_latch_not_thiele_complete`,
  `silent_weakly_thiele_complete`, `silent_not_thiele_complete`.
- **Proved.** Every Thiele-complete machine hides its record and its ledger
  from its own window: two runs from one clean start end at the same window,
  one certified with its ledger at least three marks higher, the other
  uncertified with its ledger unchanged. No function of the window recovers
  either. Coq: `complete_two_runs`, `complete_hides_record`,
  `complete_hides_ledger`, `thiele_complete_hides`.
- **Proved.** Every Thiele-complete machine is a certification system whose
  window is blind to its reading. Coq: `thiele_complete_floor`,
  `complete_cs_window_blind`.

## The universal machine

- **Proved.** A host built on the small machine runs any of its programs as a
  guest, keeps a mirror equal to the guest's certified flag, and raises the
  mirror only in a guest step that passed CERTIFY, charged in that step, for
  every sequence of host moves. Coq: `record_agreement`,
  `no_free_host_certification_step`, `no_free_host_certification`, with the
  host's certification floor `host_nfi`. On this host, a machine from
  elsewhere enters through the two-counter encoding, and its own price list is
  not kept. On the priced host's program U_P, a computably presented machine
  keeps its own ledger plus a surcharge, which is at most 2 when the machine's
  reading starts at no (see the specification).
- **Proved.** U is one fixed program of the small machine's own instruction
  kinds, with no guest step built into anything. It runs every program of the
  small machine from every start: each guest step is matched by a later U
  state, or both have halted. Coq: `U_simulation`.
- **Proved.** U halts exactly when its guest halts, with the guest's answer in
  its first two registers. Coq: `universal_halting`, `universal_output`.
- **Proved.** U's flag goes up exactly when the guest's would, by its own
  check, its own commit and its own certificate. Coq: `universal_flag_iff`,
  `universal_earned`.
- **Proved.** U's ledger equals the guest's wherever the two runs line up, and
  lies between two consecutive guest ledgers everywhere else.
  Coq: `universal_ledger_exact`.
- **Proved.** The machine U runs on is Thiele-complete.
  Coq: `universal_thiele_complete`.

## The record axis

The questions here ask how much of a machine the record axis pins down.

- **Proved.** Over any deterministic base, a computation-driven, priced,
  permanent, written record factors as a latch: the next record is the old
  record or a function of the base state (`record_axis_is_latch`). Two
  permanent records factor as two latches, each reading the other
  (`record_pair_is_two_latches`). Coq: `record_axis_is_latch_holds`,
  `record_pair_is_two_latches_holds`.
- **Proved.** Both premises do work: a record that can switch back off is not
  a latch, and a record switched on by a hidden clock
is permanent and is not driven by the computation. Coq: `toggle_not_latch`, `toggle_not_permanent`,
  `clock_record_permanent`, `clock_record_not_driven`.
- **Proved.** Every base can carry the axis: the base plus a latch on any
  event it reaches, charging one unit when the latch sets, is an honest
  extension. A reversible base with unbounded memory can carry one and stay
  reversible; with finite memory a step that writes a permanent record is not
  injective. Coq: `latch_core_honest`, `history_latch_honest`,
  `history_latch_injective`, `finite_reversible_cannot_write`.

## Growing records

A growing record takes values in a partial order and only moves up
(`HonestGrowingExtension`).

- **Proved.** Every honest growing record satisfies a complete family of
  permanent threshold-update equations, one per lower threshold, and keeps its
  price schedule (`growing_record_decomposes`). This is a representation
  lemma: the threshold events are built from the driving function, and the
  schedule is a premise carried through. Coq: `growing_record_decomposes_holds`.
- **Proved.** The complete family of lower thresholds determines the record
  value (`thresholds_determine_record`). Coq: `thresholds_determine_record_holds`.
- **Proved.** On a growing record, pricing every strict value change is
  equivalent to pricing every false-to-true threshold flip
  (`record_price_iff_threshold_price`).
  Coq: `record_price_iff_threshold_price_holds`.
- **Refuted.** One Boolean latch carries every honest growing record
  (`one_latch_suffices`). Counterexample: a fully priced three-value chain
  over a one-state base (`ThreeMachine`, `OneBase`, `ThreeCover`, with honesty
  proved by `three_honest`). Three values cannot be decoded from one base
  state and one bit. Coq: `one_latch_refuted`.
- **Proved.** A pairwise-distinct, pointwise-monotone chain of k-bit vectors
  has at most k + 1 members (`chain_needs_bits`). A chain through n
  distinct values in this representation needs at least n - 1 bits. The
  bound concerns monotone Boolean-vector encodings only; other encodings are
  outside it. Coq: `chain_needs_bits_holds`.

## Accountable finality

- **Proved.** In the Casper FFG model, two finalized blocks on conflicting
  branches imply a quorum whose votes satisfy a slashing condition. The proof
  is constructive. Coq: `accountable_safety`, `conflicting_records_are_priced`,
  with the key step `distinct_justified_same_epoch_slashes`. This is the
  accountable-safety theorem of Casper FFG, the finality gadget Vitalik
  Buterin and Virgil Griffith proposed for Ethereum in 2017. It shows that
  slashable votes exist. Whether a slash is executed, or finality deleted, is
  outside the model.
- **Proved.** The premise of accountable safety is inhabited: a concrete
  three-validator fork finalizes two conflicting blocks and its slashed
  quorum is computed. Coq: `casper_fork_exists`, `casper_fork_slashable`.
- **Proved.** Writing a finalization record need not slash anyone: a
  one-validator setting finalizes with no slashing.
  Coq: `finalization_without_slashing`.

Accountable conflict fits the permanent-record axis when a contradiction
entails a stated penalty. A record that is actually revoked does not: a
revocable flip escapes the finite-state price (`revocable_certificate_escapes`).

## Probabilistic records

In a finite positive-weight branching model:

- **Refuted.** A deterministic latch handles branching
  (`deterministic_latch_handles_branching`). Counterexample:
  `fair_branch_kernel`, whose two positive branches force one event value to
  be both false and true. Coq: `deterministic_latch_handles_branching_refuted`.
- **Refuted.** Equal branch support and equal branch charges determine the
  branch weights (`schedule_determines_probabilities`). Counterexample:
  `fair_branch_kernel` (weights 1 and 1) against `biased_branch_kernel`
  (weights 1 and 2), both honest by `fair_branch_honest` and
  `biased_branch_honest`. Coq: `schedule_determines_probabilities_refuted`.
  Uniqueness up to the schedule fails; the probability kernel has to be
  preserved as well.
- **Proved.** The relation that preserves ordered weight lists exactly is
  reflexive. This is a well-formedness check only.
  Coq: `probability_preserving_equivalence_reflexive_holds`.

## Bases and granularity

`weak_base_equiv` relates two observed bases when they agree on the chosen
observations and on halting, and a step on either side matches zero or more
steps on the other.

- **Proved.** `weak_base_equiv` is an equivalence relation.
  Coq: `weak_base_equiv_refl_holds`, `weak_base_equiv_sym_holds`,
  `weak_base_equiv_trans_holds`.
- **Proved.** Weakly equivalent bases agree on whether the record axis is a
  latch over them. The statement does not use its equivalence premise, since
  `record_axis_is_latch_holds` proves both sides for every deterministic base.
  Coq: `weak_equiv_preserves_record_latch_holds`.
- **Proved.** The record axis is a latch over three concrete bases: the toy
  Turing machine, the Cook and Reckhow unit-cost RAM over natural numbers
  (the random-access machine Stephen Cook and Robert Reckhow defined to
  measure time bounds, Journal of Computer and System Sciences 7, 1973;
  indirect load and store, conditional jumps), and the lambda calculus L
  under weak call-by-value reduction.
  Coq: `record_axis_is_latch_on_tm_holds`, `record_axis_is_latch_on_ram_holds`,
  `record_axis_is_latch_on_l_holds`.
  The RAM is a separate machine with random access through registers
  (`ram_store_then_load`, `ram_jump_pos_taken`, `ram_halted_stutters`,
  `ram_pointer_demo_runs`). The L step function is computed by structure and
  agrees with the reduction relation (`l_step_fun_correct`,
  `l_base_halted_iff_irreducible`, `l_base_run_is_star`, `star_is_l_base_run`).

## Concrete record machines

- **Proved.** A tied RAM appends the overwritten value to its record on every
  write; an untied RAM leaves its record unchanged, and equal base values do
  not determine an untied record. Coq: `ram_tied_overwrite_records_old_value`,
  `ram_untied_overwrite_has_no_record`, `ram_untied_record_not_determined_by_base`.
- **Proved.** Unbounded and modular arithmetic updates are undone by their
  syntactic inverses. These are reversible cores in the style of Janus, the
  reversible programming language that Christopher Lutz and Howard Derby
  wrote at Caltech in 1982 and that Tetsuo Yokoyama and Robert Glück gave a
  formal semantics in 2007. The full Janus language is outside the model.
  Coq: `janus_like_unbounded_inverse`, `janus_like_bounded_inverse`.
- **Proved.** In list memory, a write to an existing cell reads back, the
  tied step appends exactly the address and old value, the untied record never
  changes, and both machines agree on memory and program counter. Coq:
  `concrete_ram_write_reads_back`, `concrete_tied_ram_records_overwrite`,
  `concrete_untied_ram_record_unchanged`, `concrete_tied_and_untied_same_base`,
  with the executed example `concrete_ram_two_cell_witness`.

## Recursion and undecidability

- **Proved.** Over any substrate with a recursion theorem, a representable
  two-way branch, and a shortcut predicate that respects behavior and is
  nontrivial, no decider the substrate can run returns true exactly when the
  predicate holds.
  Coq: `structural_shortcut_undecidable`, `admits_shortcut_not_decidable`.
  The natural-number substrate meets the recursion premise by construction:
  `nat_structural_shortcut_undecidable`, `nat_self_undecidable`.
- **Proved.** The lambda calculus L, built from its reduction rules, has the
  second recursion theorem, Rice's theorem and an undecidable halting problem.
  Coq: `second_recursion`, `L_rice`, `L_halting_undecidable`. L is the
  calculus Yannick Forster and Gert Smolka presented as a model of
  computation for computability theory in Coq (Interactive Theorem Proving,
  ITP 2017), and Yannick Forster, Fabian Kunze, Gert Smolka and Maximilian
  Wuttke later checked in Coq that L and Turing machines simulate each other
  (ITP 2021). The Turing-completeness of L is not re-proved in the
  repository's own files; it comes from the models-equivalence theorem of the
  vendored Coq Library of Undecidability Proofs
  (vendor/coq-undecidability/theories/Synthetic/Models_Equivalent.v), which is
  checked with the build.
- **Proved.** The complement of two-counter halting is undecidable, from the
  vendored two-counter result. Coq: `MM2_HALTING_compl_undec`.

## Pricing and physics

- **Proved.** Under every cost schedule that prices merges, no injective
  instruction is forced to have positive price; forced price is exactly
  non-injectivity (`no_price_beyond_merges`). It is a direct corollary of
  `forced_priced_iff_merges` and says nothing about schedules outside that
  class. Coq: `no_forced_price_beyond_merges`.
- **Proved** at the logical level. A permanent finite write is a many-to-one
  step, so it pays logically (`permanent_flip_logical_payment`).
  Coq: `permanent_write_has_logical_payment`. Economic, cryptographic, and
  heat payment each need a premise about that level and are not derived.
- **Proved.** An eight-state machine with four program slots and a
  certification flag meets the three premises of the finite argument as theorems:
  it is finite, its certificate is permanent, its certify step and its jumps
  merge states, its advance step does not, and its cost rule prices exactly
  the merges, so A2 holds. Coq: `fin_finite`, `fin_permanent`,
  `fcertify_merges`, `fnext_injective`, `fin_merging_priced`,
  `fin_a2_from_merging_price`.
- **Refuted.** Mu has an intrinsic joule value (`no_intrinsic_joule_scale`
  states the refutation). Two distinct external scales fit the same
  natural-number ledger. Coq: `mu_has_no_intrinsic_joule_value`.
- **Proved**, with the scale supplied as an argument: at the Landauer scale
  `k_B T ln 2`, one mu unit is `k_B T ln 2` (`mu_landauer_calibration`), the
  product of the ledger and the scale. Coq: `calibrated_mu_landauer_energy`.
  The scale is named for Rolf Landauer, who argued at IBM in 1961 that a step
  that cannot be run backwards requires a minimal heat generation.
  Fixing the scale is a premise; nothing here measures it.
- **Conditional.** Given the `landauer_heat` premise and `0 <= kT`, flipping a
  permanent reading on a finite state space, with m certified states and k > 0
  flipping ones and starting from the uniform distribution on those m + k
  states, releases heat at least `kT ln((m + k)/m)`
  (`landauer_permanence_heat_floor`). Coq:
  `permanence_heat_floor_uses_landauer`, through `permanent_flip_heat_floor`.
  The finite-state entropy is invariant under permutation of the state
  enumeration: `semantics_entropy_permutation_invariant`. The heat floor is
  Landauer's principle applied to this step; the checked content is the link
  from a permanent record write to a many-to-one step.
- **Proved.** A two-state calorimeter protocol: a canonical reset from
  half-excited to ground satisfies a discrete master equation exactly, and at
  fixed Hamiltonian the bath receives `Delta / 2`.
  Coq: `canonical_reset_satisfies_master_equation`, `canonical_reset_heat_exact`.
- **Proved**, with the scale built in: choosing the gap `2 k_B T ln 2` gives
  heat `k_B T ln 2`. Coq: `selected_gap_gives_landauer_heat`.
- **Refuted.** The master equation and a one-unit ledger change force the
  Landauer bound. Counterexample: the same reset with gap `k_B T ln 2` releases
  half that heat; two different gaps give the same dynamics, which do not
  depend on the gap, and different heat.
  Coq: `smaller_gap_refutes_unconditional_landauer_floor`,
  `master_equation_does_not_fix_heat_scale`. Ruling the smaller gap out needs
  a thermal premise such as local detailed balance, or device evidence.
- **Proved.** The protocol's ledger change is one unit, the price of one
  certification step on the small machine. No state map between the protocol
  and the machine is claimed. Coq: `canonical_reset_is_one_mu`.

## Real-system models

Each model below is narrow. None is a full security, consensus, database, or
audit-log theorem.

- **Proved** boundary checks for RFC 9162 Certificate Transparency: the
  iterative inclusion and consistency verifiers of RFC 9162 Sections 2.1.3.2
  and 2.1.4.2 reject the boundary cases, and symbolic runs accept the
  Section 2.1.5 examples. Coq: `rfc9162_inclusion_boundary_safe`,
  `rfc9162_consistency_boundary_safe`, `rfc9162_example_inclusion_d0`,
  `rfc9162_example_consistency_4_7`. Appending to a log history keeps old
  entries and grows the size (`ct_extension_preserves_entries`,
  `ct_extension_size_monotone`). Collision resistance and signed-tree-head
  authenticity are cryptographic premises and are not proved; the symbolic
  digests rule collisions out by construction and serve only to run the RFC
  control flow.
- **Proved** for a toy proof-carrying-code fragment: the executable checker
  accepts exactly the address-bound verification condition, a typed
  certificate entails it, and an out-of-range access is rejected.
  Coq: `pcc_checker_accepts_iff_vc`, `pcc_certificate_implies_vc`,
  `pcc_unsafe_program_rejected`, `pcc_safe_instance`. This mirrors the roles
  in George C. Necula's proof-carrying code (PCC, POPL 1997), where a program
  ships with a proof that it is safe. The full system is outside this model.
- **Refuted.** A bare sign/verify interface implies the authenticity of a
  Trusted Platform Module (TPM) quote.
  Counterexample: a scheme that always signs false and accepts every
  signature accepts true (`degenerate_accepts_forgery`).
  Coq: `tpm_interface_authenticity_refuted`. Authenticity needs a trusted-key
  or unforgeability premise.
- **Proved**: five narrow countermodels, each for a point that a governing
  source already addresses. A Certificate Transparency client's local view cannot
  detect a split log (`ct_local_view_insufficient`; RFC 9162, Section 11.3,
  "Misbehaving Logs", <https://www.rfc-editor.org/rfc/rfc9162.html>). A quote
  checker must bind its selection of platform configuration registers, the
  PCR selection (`tpm_selection_binding_is_necessary`;
  tpm2-tools advisory GHSA-8rjm-5f5f-h4q6, CVE-2024-29039, on
  tpm2_checkquote and an altered PCR selection,
  <https://www.tenable.com/cve/CVE-2024-29039>). A local chain suffix does not
  fix the trusted anchor (`weak_subjective_suffix_insufficient`; Ethereum's
  weak-subjectivity guidance,
  <https://ethereum.org/en/developers/docs/consensus-mechanisms/pos/weak-subjectivity/>).
  An acknowledged commit needs a durable commit record
  (`wal_ack_requires_durability`; PostgreSQL documentation, Write-Ahead
  Logging (WAL), <https://www.postgresql.org/docs/current/wal-intro.html>). A
  current local log does not establish a past event
  (`audit_local_snapshot_insufficient`; NIST SP 800-92, Guide to Computer
  Security Log Management, Karen Kent and Murugiah Souppaya, 2006,
  <https://csrc.nist.gov/pubs/sp/800/92/final>). Each is a generic
  two-state collision or durability counterexample that does not need the
  record axis. No surveyed consequence is both new and specific to the
  record axis.

## The pointer criterion

The pointer-observable criterion is a conjecture. Choosing the observers and
the event is a modeling choice that proofs cannot make. The formal
definitions and the selected model instances are proved only inside their
observer maps.

- **Proved.** Twelve candidate events over seven observer maps proliferate
  exactly as follows. Coq: `twelve_candidate_measurements_checked`.

  | Event | Observer map | Proliferates |
  |---|---|---|
  | finalized block | proof of stake | yes |
  | proposer work | proof of stake | no |
  | committed state | gas metering | yes |
  | scratch work | gas metering | no |
  | attestation issued | trusted execution | yes |
  | measurement noise | trusted execution | no |
  | certificate included | Certificate Transparency | yes |
  | prover effort | Certificate Transparency | no |
  | certificate checked | proof-carrying code | yes |
  | prover effort | proof-carrying code | no |
  | MAC authenticity | symmetric MAC | no |
  | signature authenticity | digital signature | yes |

  The MAC row is a model counterexample to universal proliferation
  (`mac_model_not_proliferating`). Reading it as a statement about forgery in
  deployed systems is a separate modeling premise.
- **Proved.** Swapping which event the fragments mirror swaps the unique
  pointer: the second event becomes the pointer and the first does not
  proliferate. Coq: `swapped_event_is_pointer_checked`,
  `first_event_not_proliferating`.
- **Refuted.** Consensus among authenticated observers that update by a
  local rule forces the observed event to be permanent. Counterexample:
  `toggle_game`, two observers that agree and update by negation, so the
  event turns false. Coq: `toggle_game_refutes_strong_pointer_necessity`.
- **Conditional.** If at least one observer exists, every view is sound and
  complete for the event, and a true view stays true (`durable_views`), the
  event is permanent. The persistence premise carries the conclusion.
  Coq: `durable_consensus_implies_permanence`.

## Not formalized here

- **Full proof-carrying code.** Necula's system (SAL execution, the LF
  encoding, the verification-condition generator, and both soundness
  translations) is another system; formalizing it is outside the Thiele
  Machine.
- **Full embeddings of four cost calculi.** Graded modal effect semantics
  (Dominic Orchard, Vilem Liepelt and Harley Eades, who put grades into the
  types of a working language, ICFP 2019), the cost translation of the
  programming-language researchers Norman Danner, Daniel Licata and Ramyaa
  (ICFP 2015), automatic amortized resource analysis, and linear-logic
  resource semantics are other systems. The repository proves the fragments
  it uses: `a2_and_aara_iff_exact`, `flips_le_cost`,
  `certification_system_is_potential_method`, `nfi_by_potential`.
- **Certificate Transparency gossip and checkpoint distribution.** RFC 9162
  leaves gossip undefined, and the weak-subjectivity guidance specifies no
  distribution protocol, so there is no protocol semantics to formalize.
- **Persistent-memory durability barriers.** This needs a hardware model of
  flush completion and power failure that the platform documentation does
  not give.
- **Storage-energy and joule calibration.** These need physical measurement
  on a device; none is part of this repository.
- **Cryptographic hardness.** Collision resistance, signature
  unforgeability, and signed-tree-head authenticity appear only as premises.

## Standard-library axioms

These cited theorems depend on axioms drawn only from the Coq standard library:
the real-number axioms `ClassicalDedekindReals.sig_forall_dec` and
`ClassicalDedekindReals.sig_not_dec`,
`Classical_Prop.classic`, and
`FunctionalExtensionality.functional_extensionality_dep`.

- `calibrated_mu_landauer_energy`
- `canonical_reset_heat_exact`
- `canonical_reset_satisfies_master_equation`
- `master_equation_does_not_fix_heat_scale`
- `mu_has_no_intrinsic_joule_value`
- `permanence_heat_floor_uses_landauer`
- `permanent_flip_heat_floor`
- `selected_gap_gives_landauer_heat`
- `semantics_entropy_permutation_invariant`
- `smaller_gap_refutes_unconditional_landauer_floor`
