# Results

The Thiele Machine is an abstract model. A priced record system has states, moves, a step, a price on each move, a reading into a preorder, and the toll: a move that carries the reading out of its down-set costs at least 1. A Thiele machine is a priced record system whose reading no move lowers and some run from a designated start raises. Each result below names its class: every Thiele machine, every system that obeys the toll, or every certification system (the two-point record with the toll alone).

This file states the settled results about the definition and its members,
the record axis and the events it can carry, recursion and undecidability,
pricing and physics, and the real systems the repository models. Further
settled results are stated, with their premises and declarations, in the
mathematical specification (monograph/thiele_machine_math_spec.tex) and are
not repeated here: the record over any order, and the results showing that
each premise is needed. Each result below names the Coq declarations that carry it and has one
of four statuses:

- **Proved.** The result has a proof, written out in the monograph for the
  results the monograph states, and a named Coq theorem states it formally.
  The formal version is a tool for catching mistakes; the argument is the
  reason to believe the result.
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

## The definition and its members

A Thiele machine is a priced record system (states, moves, a step, a
price on each move, a reading into a preorder) whose reading some run raises
and no move lowers: the toll, permanence, and a designated start from which
some run carries the reading out of its down-set. Coq: `ax_thiele` in
`AxThiele.v`, over `AxSys` in `AxCore.v`. A reading no move carries out of
its down-set is flat. Flat is a property of the reading, and the same step
function can be flat under one reading and a member under another.

- **Proved.** A flat reading obeys the toll, because the toll charges
  nothing of it, and it fails the member predicate for every choice of
  designated starts. Coq: `flat_obeys_toll`, `flat_has_no_distinction`,
  `flat_is_not_thiele`.
- **Proved.** Every member has a move that costs at least one, and every
  member has the floor: a run that ends outside the down-set of its start
  costs at least one. Coq: `thiele_has_a_priced_move`, `thiele_floor`.
- **Proved.** The latch, two states and one move that sends both to yes at
  price one, is a member, and its move is not injective: two states land
  on one. Coq: `latch_is_thiele`, `latch_merges`.
- **Proved.** No member has a constant reading, so a member has at least
  two states; over the two-point order every member has a move that raises
  the reading from some no-state and keeps every yes-state at yes; on two
  states read as themselves every member has the latch's move; and the
  toggle, whose move swaps the states, is not a member, because it fails
  permanence. Coq: `no_one_state_member`, `two_point_member_raising_move`,
  `two_state_member_has_latch_move`, `toggle_is_not_thiele`.
- **Proved.** Every machine with a Boolean equality test on its states and
  a run that ends on a state other than its start is the shadow of a
  member: fit a bit that goes up when a move lands on the state the run
  ends on and never comes down, price every move one, and read the bit.
  Dropping the bit gives back the original run. Above every shadow sit two
  lifted states with different readings, and no function of the shadow
  recovers the reading. Coq: `history_lift`, `history_lift_shadow`,
  `history_lift_is_thiele`, `moving_machine_is_a_shadow`,
  `shadow_hides_history`.
- **Proved.** Over a finite base the least price list for the lift is one
  on every move that can land on the lifted state and zero elsewhere; the
  toll holds for the lift exactly when its prices are at least that list,
  and the lift priced by that list is a member. Coq: `lift_can_raise_iff`,
  `lift_toll_iff_least`, `least_lift_is_thiele`, `AxThieleLeast.v`.

## The record axis

The questions here ask how much of a machine the record axis pins down.

- **Proved.** Over any deterministic base, a computation-driven, priced,
  permanent, written record factors as a latch: the next record is the old
  record or a function of the base state (`record_axis_is_latch`). Two
  permanent records factor as two latches, each reading the other
  (`record_pair_is_two_latches`). Coq: `record_axis_is_latch_holds`,
  `record_pair_is_two_latches_holds`.
- **Proved.** Both premises do work: a record that can switch back off is not
  a latch, and a record switched on by a hidden clock is permanent and is not
  driven by the computation. Coq: `toggle_not_latch`, `toggle_not_permanent`,
  `clock_record_permanent`, `clock_record_not_driven`.
- **Proved.** Every base can carry the axis: the base plus a latch on any
  event it reaches, charging one unit when the latch sets, is a base-driven
  record. A reversible base with unbounded memory can carry one and stay
  reversible, paying a fresh state at every step; with finite memory a step that writes a permanent record is not
  injective. Coq: `latch_core_honest`, `history_latch_honest`,
  `history_latch_injective`, `finite_reversible_cannot_write`.

## Growing records

A growing record takes values in a partial order and only moves up
(`HonestGrowingExtension`).

- **Proved.** Every base-driven growing record satisfies a complete family of
  permanent threshold-update equations, one per lower threshold, and keeps its
  price schedule (`growing_record_decomposes`). This is a representation
  lemma: the threshold events are built from the driving function, and the
  schedule is a premise carried through. Coq: `growing_record_decomposes_holds`.
- **Proved.** The complete family of lower thresholds determines the record
  value (`thresholds_determine_record`). Coq:
  `thresholds_determine_record_holds`.
- **Proved.** On a growing record, pricing every strict value change is
  equivalent to pricing every false-to-true threshold flip
  (`record_price_iff_threshold_price`).
  Coq: `record_price_iff_threshold_price_holds`.
- **Refuted.** One Boolean latch carries every base-driven growing record
  (`one_latch_suffices`). Counterexample: a fully priced three-value chain
  over a one-state base (`ThreeMachine`, `OneBase`, `ThreeCover`, with the base-driven
  conditions proved by `three_honest`). Three values cannot be decoded from one base
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
revocable flip is not forced to pay the finite-state price, and it keeps
nothing (`revocable_certificate_escapes`).

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
  `ram_untied_overwrite_has_no_record`,
  `ram_untied_record_not_determined_by_base`.
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
  (ITP 2021). The Turing-completeness of L is theirs and is not proved in
  this repository.

## What keeping costs

The monograph's point is that nothing becomes something for free: a
distinction that comes into being dissipates by happening, and keeping it is
paid on top, in a merge or in fresh states. The dissipation is physics, on two counts.
Any real device dissipates in finite time, with one proved instance below. And
a fixed device that sends K inputs to one output produces at least k_B ln K of
entropy, at least k_B T ln K of dissipated work, on its worst input, however
slowly it runs and whatever anyone knows; only a device chosen knowing the
input avoids it, and that device is where the knowing is kept. Certification
is the sharpest case.

- **Proved.** Every step of a deterministic run on any set of states is fresh,
  a merge (two distinct states with one next state), or a revisit from the
  same state after which the run is periodic. No finiteness is assumed.
  Coq: `step_law`, `merge_is_collision`, `revisit_means_loop`.
- **Proved.** On any set of states, a run that raises a permanent reading
  either merges two of its states or visits a fresh state at every step; an
  injective raising move visits a fresh state every time. Coq:
  `run_merges_or_fresh`, `permanent_flip_iterates_distinct`. A finite memory
  keeps the history of a reset through at most (M - N)/(N - 1) repetitions,
  and the bound is attained. Coq: `retention_bound`, `tight_exact`.
- **Proved.** Writing a 0 on a blank cell merges blank with zero, and a
  finite extension of the cell still merges; an endless tape avoids the merge
  only by paying a fresh cell every write. Coq: `write_is_a_merge`,
  `four_state_escape_fails`, `tape_write_injective`.
- **Proved.** An injective step on finitely many states returns every run to
  its start, so a reversible finite machine keeps nothing. Coq:
  `returns_to_start`, `reversible_keeps_nothing`.
- **Proved.** A biased Brownian walk produces strictly positive entropy per
  tick at any nonzero speed, and heat times time is at least the distance
  squared. Coq: `heat_at_any_speed`, `heat_time_floor`.
- **Proved** in the monograph and in Coq: one unit per crossing of the reading
  from no to yes, `flips_le_cost` (coq/kernel/nfi/CostFrameworks.v).
- **Proved** in the monograph, with no Coq counterpart: the certainty bound (under entropy pricing,
  the uncertainty about the start is the part the run destroyed, at most its
  cost in bits, plus the part the end state still holds); and every scale
  paying the same way (a coarse merge forces a fine merge, unless the fine step leaves
  the described states or there are endlessly many of them).

## Pricing and physics

- **Proved.** For instructions with decidable equality, under every cost
  schedule that prices merges, no injective instruction is forced to have
  positive price (`no_price_beyond_merges`); with `forced_priced_iff_merges`,
  forced price is exactly non-injectivity. It is a direct corollary of
  `forced_priced_iff_merges` and says nothing about schedules outside that
  class. Coq: `no_forced_price_beyond_merges`.
- **Proved** at the logical level. A permanent finite write is a many-to-one
  step, so it pays logically (`permanent_flip_logical_payment`).
  Coq: `permanent_write_has_logical_payment`. Economic, cryptographic, and
  heat payment each need a premise about that level and are not derived.
- **Proved.** An eight-state machine with four program slots and a
  certification flag meets the three premises of the finite argument as
  theorems: it is finite, its certificate is permanent, its certify step and
  its jumps merge states, its advance step does not, and its cost rule prices
  exactly the merges, so A2 holds. Coq: `fin_finite`, `fin_permanent`,
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
  Landauer's principle applied to this step; the proved content is the link
  from a permanent record write to a many-to-one step.
- **Proved.** From a known start, Landauer's premise gives no heat floor: the
  entropy before and after the step are both zero, and the premise reads heat
  at least zero. Coq: `known_state_flip_forces_no_heat`. The device floor
  stated under "What keeping costs" still holds for a fixed device that merges inputs,
  on its worst input.
- **Proved.** A two-state calorimeter protocol: a canonical reset from
  half-excited to ground satisfies a discrete master equation exactly, and at
  fixed Hamiltonian the bath receives `Delta / 2`. Coq:
  `canonical_reset_satisfies_master_equation`, `canonical_reset_heat_exact`.
- **Proved**, with the scale built in: choosing the gap `2 k_B T ln 2` gives
  heat `k_B T ln 2`. Coq: `selected_gap_gives_landauer_heat`.
- **Refuted.** The master equation and a one-unit ledger change force the
  Landauer bound. Counterexample: the same reset with gap `k_B T ln 2` releases
  half that heat; two different gaps give the same dynamics, which do not
  depend on the gap, and different heat.
  Coq: `canonical_reset_heat_below_landauer_at_small_gap`,
  `master_equation_does_not_fix_heat_scale`. The canonical reset is a
  bookkeeping toy with no second law: its rates (up 0, down 1) are in detailed
  balance at no gap (`canonical_rates_break_detailed_balance`), and with rates
  that are, a fixed-gap relaxation settles at `1 / (1 + exp (Delta / kT))`,
  which is `1/5` at the gap `2 k_B T ln 2`, and never below it
  (`detailed_balance_never_empties`, `landauer_gap_settles_at_one_fifth`).
- **Proved.** A driven reset with rates in detailed balance pays `k_B T ln 2`
  in work: raising the gap in steps and letting the register settle at each,
  the work is never below the free-energy change and exceeds it by at most the
  step size times the fall in population; for `N` equal raises from gap 0 to
  `D` it lies between `kT ln 2 - kT exp (- D / kT)` and `kT ln 2 + D / (2 N)`,
  with at most `exp (- D / kT)` left excited. Work minus heat is the change in
  mean energy. Coq: `detailed_balance_settles_at_gibbs`,
  `detailed_balance_thermalizing_step`, `driven_first_law`,
  `driven_work_second_law`, `driven_work_near_free_energy`,
  `driven_reset_work_window`.
- **Proved.** The protocol's ledger change is one unit, the price of the
  latch's raising move. No state map between the protocol and a machine is
  claimed. Coq: `canonical_reset_is_one_mu`.

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
  source already addresses. A Certificate Transparency client's local view
  cannot detect a split log (`ct_local_view_insufficient`; RFC 9162, Section
  11.3, "Misbehaving Logs", <https://www.rfc-editor.org/rfc/rfc9162.html>). A
  quote checker must bind its selection of platform configuration registers,
  the PCR selection (`tpm_selection_binding_is_necessary`; tpm2-tools advisory
  GHSA-8rjm-5f5f-h4q6, CVE-2024-29039, on tpm2_checkquote and an altered PCR
  selection, <https://www.tenable.com/cve/CVE-2024-29039>). A local chain
  suffix does not fix the trusted anchor
  (`weak_subjective_suffix_insufficient`; Ethereum's weak-subjectivity
  guidance, <https://ethereum.org/en/developers/docs/consensus-mechanisms/pos/weak-subjectivity/>). An acknowledged commit needs a durable commit record
  (`wal_ack_requires_durability`; PostgreSQL documentation, Write-Ahead
  Logging (WAL), <https://www.postgresql.org/docs/current/wal-intro.html>). A
  current local log does not establish a past event
  (`audit_local_snapshot_insufficient`; NIST SP 800-92, Guide to Computer
  Security Log Management, Karen Kent and Murugiah Souppaya, 2006,
  <https://csrc.nist.gov/pubs/sp/800/92/final>). Each is a generic two-state
  collision or durability counterexample that does not need the record axis.
  No surveyed consequence is both new and specific to the record axis.

## The pointer criterion

The pointer-observable criterion is a thesis. Choosing the observers and
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
- **The second law as the toll.** The monograph sets the shapes side by
  side (a window as coarse-graining, a fibre as the states under one
  picture, a record and a ledger that only climb, a toll on the climb) and
  states the correspondence as a thesis. Entropy's numbers, Landauer's
  principle and any physical claim are outside the formal development.

## Standard-library axioms

These cited theorems depend on axioms drawn only from the Coq standard library:
the real-number axioms `ClassicalDedekindReals.sig_forall_dec` and
`ClassicalDedekindReals.sig_not_dec`,
`Classical_Prop.classic`, and
`FunctionalExtensionality.functional_extensionality_dep`.

- `calibrated_mu_landauer_energy`
- `canonical_rates_break_detailed_balance`
- `canonical_reset_heat_below_landauer_at_small_gap`
- `canonical_reset_heat_exact`
- `canonical_reset_satisfies_master_equation`
- `detailed_balance_never_empties`
- `detailed_balance_settles_at_gibbs`
- `detailed_balance_thermalizing_step`
- `driven_first_law`
- `driven_reset_work_window`
- `driven_work_near_free_energy`
- `driven_work_second_law`
- `heat_at_any_speed`
- `heat_time_floor`
- `known_state_flip_forces_no_heat`
- `landauer_gap_settles_at_one_fifth`
- `master_equation_does_not_fix_heat_scale`
- `mu_has_no_intrinsic_joule_value`
- `permanence_heat_floor_uses_landauer`
- `permanent_flip_heat_floor`
- `selected_gap_gives_landauer_heat`
- `semantics_entropy_permutation_invariant`
