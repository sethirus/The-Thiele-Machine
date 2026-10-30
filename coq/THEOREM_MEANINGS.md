# What each cited theorem says

This file sits beside the Coq development, which is a tool for catching
mistakes, not the reason to believe anything; the arguments are in the
monograph. Coq checks that a proof matches its statement. It does not check
that the name or the prose around a theorem means what the statement says.
Each entry here is one plain sentence saying what a Coq statement asserts,
premises included, for every theorem a document names (today only the
technical disclosure, which records where each concept was implemented).

`tests/test_theorem_meanings.py` fails when a document cites a theorem that
has no entry here, or when an entry names a theorem that does not exist.
The entries describe the current statements. Their accuracy requires reading
the quantified premises and conclusion; the gate checks coverage and names.
Where several modules use the same short name, the parenthesized qualified
name identifies the theorem meant by unqualified citations in these documents.
An explicitly qualified citation keeps its own module identity.

Entries are grouped by where they sit in the model: the definition and its
price, what stays, what a window forgets, the room a kept distinction needs,
records over any base and the diagonal, the world, and verifiers and finite
premises.

## The definition and the price in the move

### The member, the flat reading and the smallest machine

- `flat_obeys_toll`: In any priced record system, if no move carries the reading out of its down-set, the toll holds, because no move is ever charged by it.
- `flat_has_no_distinction`: In any priced record system whose reading no move carries out of its down-set, no run from any start ends outside the down-set of where it started.
- `flat_is_not_thiele`: In any priced record system whose reading no move carries out of its down-set, the member predicate `ax_thiele` fails for every choice of designated starts.
- `thiele_has_a_priced_move`: In any priced record system that meets the member predicate, some move costs at least one.
- `thiele_floor`: In any priced record system that meets the member predicate, every run that ends outside the down-set of its start costs at least one.
- `two_point_member_raising_move`: In any priced record system over the two-point order that meets the member predicate, some move sends a state reading no to a state reading yes and sends every state reading yes to a state reading yes.
- `latch_is_thiele`: The two-state system whose one move sends both states to yes at price one, read as its state, meets the member predicate with no as its designated start.
- `latch_merges`: The latch's one move is not injective: two different states land on one.
- `no_one_state_member`: In any priced record system that meets the member predicate, there are two different states with different readings.
- `two_state_member_has_latch_move`: For any set of moves, step function, prices and designated starts on the two states read as themselves, meeting the member predicate gives a move that sends no to yes and yes to yes.
- `toggle_is_not_thiele`: The two-state system whose one move swaps the states fails the member predicate for every choice of designated starts, because it fails permanence.
- `history_lift_shadow`: For any priced record system, a Boolean equality test on its states and a chosen state, running the history lift from a state with any bit and dropping the bit gives the run of the original system from that state.
- `history_lift_is_thiele`: For any priced record system with a Boolean equality test on its states that agrees with equality, a chosen state x, and a run from a start other than x that ends at x, the history lift at x meets the member predicate with every state whose bit is down as a designated start.
- `moving_machine_is_a_shadow`: For any priced record system with a Boolean equality test on its states that agrees with equality, and a run that ends on a state other than its start, the history lift at the state the run ends on meets the member predicate with every state whose bit is down as a designated start.
- `shadow_hides_history`: For any history lift, every lifted state has another lifted state with the same shadow and a different reading, and no function of the shadow equals the reading on every lifted state.
- `shadow_hides_history_reachable`: For the history lift at x, with a Boolean equality test on states that agrees with equality and a run from a start other than x that ends at x, the lifted states (x, down) and (x, up) are both reached by some run from a state whose bit is down, and no function of the shadow equals the reading on every state so reached.
- `ax_a2_two_point_iff`: For any priced record system over the two-point order, the axis toll holds exactly when every step from a state reading no to a state reading yes costs at least one.
- `lift_can_raise_iff`: For the history lift at x, with a Boolean equality test on states that agrees with equality, over a finite covering list of states, a move can raise the bit from some lifted state exactly when some state of the base lands on x under that move.
- `lift_toll_iff_least`: For the history lift at x over a finite covering list of states and any price list, the toll holds exactly when the list is at least one on every move that can land on x and at least zero elsewhere.
- `least_lift_is_thiele`: For the history lift at x, with a Boolean equality test on states that agrees with equality, over a finite covering list of states, with a run from a start other than x that ends at x, the lift priced by the least list meets the member predicate with every state whose bit is down as a designated start.

### Certification cost

- `universal_nfi_any_substrate`: In any `CertificationSystem`, whose record includes the rule that a step switching certification on costs at least one, a trace from an uncertified state to a certified one has total cost at least one.
- `every_toll_system_pays_the_floor`: The same statement as `universal_nfi_any_substrate`, under a name that says it quantifies over every system with the toll built in as a field, and over no other.
- `universal_nfi_quantitative`: For every `QuantitativeCertificationSystem` QCS, trace, and start state whose witness value `qcs_witness` is zero, if the state reached by running the trace in the underlying certification system is certified, then the trace's total cost is at least `qcs_threshold QCS`.
- `honest_cost_tracking_strict_restriction`: Some cost-bearing system certifies at total cost zero, while every `CertificationSystem` needs cost at least one; the cost rule is what separates them.
- `free_forgery_violates_A2`: In any cost-bearing system, if some step switches certification from false to true at cost zero, the system fails the rule that every such step costs at least one.
- `commitment_cost_not_reducible_to_erasure_cost`: Some trusted erasure-accounting system certifies at total cost zero with no erasure reported, while every `CertificationSystem` needs cost at least one.
- `scs_run_embed`: For a `SimulatingCertificationSystem` over a host certification system, embedding the state its base system reaches on a trace equals the host's run of the concatenated decoded trace from the embedded start state.
- `host_represents_simulating_cert_system`: For a `SimulatingCertificationSystem` over a host certification system, a trace that goes from uncertified to certified in the base system has total cost at least one there, the host run of its decoded trace from the embedded start ends certified, and that host run has total cost at least one.

### Pricing the event

- `paid_entry_free_idle` (`Minimal.AccountingBridge.paid_entry_free_idle`): For the natural-number step that sends zero to one and fixes every positive number, charging one at zero and zero elsewhere has an exact zero-or-one ledger, covers collisions among the first two source states of the run from zero, and lets state one idle for free.
- `exact_commitment_pricing_characterization`: In a `LocalPredicatePricedSystem`, a charge meets the certification floor and never overcharges exactly when it charges on the certification flips and nowhere else, one unit each.
- `substitution_test_rejects_non_a2_exact_substitute`: A charging predicate that differs from the certification-flip predicate cannot both meet the floor and never overcharge.
- `joint_floor_is_least`: A cost meets every event floor in a finite family exactly when it is at least the joint floor, which is one when any event fires and zero otherwise.
- `calibrated_model_exists_iff_positive_cost`: A calibrated positive model exists exactly when every eligible operation costs at least one.
- `gas_schedule_exactness`: A gas schedule meets the commitment floor and never overcharges exactly when it charges the commitment predicate at unit price.
- `overcharge_breaks_exactness`: A gas schedule that charges a step that does not flip certification violates no-overcharge.
- `undercharged_opcode_admits_free_commitment`: A gas schedule that does not charge a certifying step lets that one-step trace certify at cost zero.
- `nothing_at_stake_is_free_forgery`: The finality gadget whose finalize step carries zero stake cannot satisfy the certification cost rule.
- `slashing_finality_floor`: In the slashing gadget, where finalizing carries at least one unit of stake, a run from unfinalized to finalized carries total stake at least one.
- `undercharged_opcode_breaks_certification_floor`: In a gas schedule, if some step switches certification from false to true and the schedule does not charge it, the schedule fails the universal certification floor.
- `bit_model_has_satisfiable_calibration`: In the one-bit model where idle costs zero and reset (which sends both values to false) costs one, some dissipation function is at least one on every operation that maps two distinct states to one state and at most the cost on every operation.

### The least toll and the observable lift

- `every_reading_toll_iff_free_moves_are_identity`: For a fixed transition and natural instruction price on a state type with decidable equality, the actual toll holds for every Boolean reading exactly when every zero-cost instruction fixes every state.
- `free_reading_invariance`: For any deterministic transition with natural instruction prices, the actual toll and global permanence imply that every zero-cost instruction preserves the selected Boolean reading.
- `toll_exactly_dominates_least_price`: Given a finite list covering all states, a natural instruction schedule satisfies the actual toll exactly when it pointwise dominates the Boolean-search schedule charging one for instructions with a crossing witness and zero for the others.
- `trace_floor_exactly_dominates_least_price`: Under the same covering-list premise, the finite-trace crossing floor from every starting state holds exactly for schedules dominating that least instruction schedule.
- `unique_least_valid_price`: For fixed dynamics, reading and a finite covering list, every valid schedule pointwise no larger than every other valid schedule agrees with the constructed least schedule on every instruction.
- `future_equivalence_coarsest`: For a deterministic transition and specified observation, any relation preserving current observations and stable under each instruction is contained in equality of observations after all finite continuations.
- `coarsest_relation_unique`: Two relations satisfying the stated coarsest observation-preserving and step-stable characterization agree pointwise as propositions.
- `unique_factorization_iff_kernel_inclusion`: For two pointed deterministic machines over one alphabet, with supplied access words reaching every source state, a pointwise unique start- and step-preserving map exists exactly when equality of endpoints of source words implies equality of the corresponding target endpoints.
- `minimal_realizations_uniquely_isomorphic`: Two reachable deterministic machines with the same initial output behavior, supplied access words for the first and future-observation separation in both admit a bijective start-, step- and output-preserving map, pointwise unique among start- and step-preserving maps.
- `encoding_cannot_merge_distinguishable_states`: A deterministic implementation whose encoding preserves the declared steps and whose decoder preserves the required observation cannot identify two source states separated by a common finite continuation.

### Why A2 on finite hardware

- `permanent_flip_is_not_injective`: On a finite state space where certification is never revoked, a step that switches certification on is not injective.
- `permanent_at_flip_is_not_injective`: The same, needing permanence only for the one instruction that flips.
- `a2_from_merging_price_and_permanence`: On a finite state space with permanent certification, if every non-injective instruction costs at least one, then every certifying step costs at least one.
- `permanent_certification_trace_floor`: Under the same premises, a trace from uncertified to certified costs at least one.
- `permanent_flip_iterates_distinct`: On any state space, if a move never merges two states and a reading the move never turns off goes from no to yes at a state `s`, then the iterates of `s` under the move are pairwise distinct.
- `permanent_flip_no_finite_list`: Under the same premises, no finite duplicate-free list contains every state.
- `run_merges_or_fresh`: For any step `f`, a reading `P` that `f` never turns off, and a run from `x0` in which the reading goes from no at step `r` to yes at step `r + 1`: if no two different states among the run's first `n` steps share a next state under `f` (states can be told apart), then those states are pairwise distinct.
- `run_bounded_by_room`: Under the same premises, if a duplicate-free list contains every state, a run whose first `n` steps never merge has `n` below the list's length.
- `retention_bound`: For a finite implementation of a reset, with representatives of the reset state and of `N - 1` further distinct abstract states, whose move is injective on the states reached from the representatives in fewer than `T` applications, the state space has at least `1 + (T+1)(N-1)` elements.
- `retention_horizon`: Under the same premises, with at least one non-reset representative, either `T = 0` or `T` is at most `(|X|-1)/(N-1) - 1`.
- `tight_exact`: The path construction with `n` non-reset representatives and horizon `T` has exactly `1 + (T+1)n` states, the value of the retention bound.
- `tight_closed`: That construction's state list is closed under its move.
- `tight_retain`: On that construction, the move is injective on the states reached from the representatives in fewer than `T` applications.
- `tight_merges_next`: On that construction with at least one non-reset representative, after `T` applications the first path's state differs from the fixed state while their images under the move coincide.
- `permanent_flips_collapse_at_least`: On a finite state space with permanent certification, a step that switches `k` distinct uncertified states on, beside all the certified states, has at least `k` fewer distinct images than inputs.
- `honest_erasure_accounting_implies_a2`: In a trusted erasure-accounting system on a finite state space with permanent certification, if the erasure flag reports every merge, every certifying step costs at least one.
- `commit_without_erasure_system_is_not_honest`: The zero-cost commit-without-erasure system does not report its own merge.
- `unbounded_history_escapes`: Keeping the full history makes a step injective while it still switches certification on, using unbounded memory. It walks past the finiteness premise of the merge theorem by paying in fresh states: a new one at every step.
- `revocable_certificate_escapes`: Flipping a bit is injective and switches the reading on, because it also switches it off, so it keeps nothing.
- `free_merge_escapes`: With merges unpriced, a stamping machine on a finite, permanent state space certifies at cost zero: a price list that skips the merge.
- `permanent_flips_compression_bound`: On a finite state space with permanent certification and costs where cost `c` allows at most a `2^c`-fold squeeze, switching `k` states on beside `m` certified ones satisfies `m + k <= 2^cost * m`.
- `permanent_flips_log_bound`: The same bound in rounded base-2 logarithms: `log2_up(m + k) <= cost + log2_up(m)`.
- `a2_from_compression_price_and_permanence`: Under finiteness, permanence, and the squeeze price, every certifying step costs at least one.
- `quad_stamp_cost_two_is_priced`: The four-state stamp priced at two meets the squeeze price.
- `quad_stamp_needs_two`: Every squeeze-priced cost for the four-state stamp is at least two.
- `forced_priced_iff_merges`: With decidable equality on instructions, an instruction is charged by every merge-pricing cost exactly when its step is not injective.
- `flip_merges_or_revokes`: On a finite state space, an instruction that switches a reading on somewhere either is not injective or switches the reading off somewhere.
- `injective_flip_revokes`: On a finite state space, an injective instruction that switches a reading on somewhere also switches it off somewhere.
- `permanent_record_write_is_forced_priced`: On a finite state space whose instruction names can be decided equal or different, an instruction that never switches the reading off and switches it on somewhere is charged by every merge-pricing cost.
- `forced_price_without_permanent_record`: A three-state instruction is charged by every merge-pricing cost and still revokes the reading, so forced pricing does not imply a permanent record.
- `record_axis_is_latch_holds`: For any base machine and any record-carrying machine that covers it step for step, whose record never switches off, satisfies A2 with a monotone ledger, is written by some reachable step, and has its next value determined by the base state and its current value, there is a base event h such that the base state and record evolve exactly as the latch "switch on where h holds, never switch off."
- `record_axis_is_latch_on_tm_holds`: The record axis is a latch on the executable toy Turing-machine base for every program.
- `record_axis_is_latch_on_ram_holds`: The record axis is a latch on the Cook-Reckhow RAM base (unbounded natural-number registers, indirect load and store, conditional jumps) for every program.
- `record_axis_is_latch_on_l_holds`: The record axis is a latch on the L base, whose next function is L's weak call-by-value step on reducible terms and stutters on irreducible ones.
- `l_step_fun_correct`: For all L terms `s` and `t`, `s` takes one weak call-by-value step to `t` exactly when the structural step function `l_step_fun` returns `Some t` on `s`.
- `star_is_l_base_run`: Every L reduction sequence from `s` to `t` is reached by running the L base machine some number of steps from `s`.
- `permanent_write_has_logical_payment`: On a finite state space, if instruction `i` keeps the record on wherever it is on, and some state goes from record off to record on under `i`, then `i` is not injective.
- `permanent_flip_merges_on_yes_side`: Under the same conditions, `i` sends every state that reads on, and the flipped state, to a state that reads on, and is not injective even on those states: the forgetting lands on the record's yes side.
- `record_pair_is_two_latches_holds`: Under the same conditions for two records, the pair evolves as two latches whose events may each read the other record.
- `toggle_not_latch`: A record on a counter base that flips at every step is driven by the computation and is not the latch of any event.
- `clock_record_not_driven`: The record switched on by a hidden clock at its fifth tick is not driven by the computation.
- `latch_core_honest`: For any base and any event it reaches from a starting state, the machine that latches that event and charges one unit per write is an honest extension of the base.
- `history_latch_injective`: If the base step is injective, the latch that also keeps every earlier record value has an injective step.
- `history_latch_honest`: That history-keeping latch is an honest extension of its base whenever the base reaches the event.
- `finite_reversible_cannot_write`: On a finite state space with a permanent reading, an injective step never switches the reading from false to true.
- `shadow_cannot_price_exactly`: If two steps share their observed before and after and only one switches certification on, no price computed from the observation both meets the floor and never overcharges.
- `shadow_floor_overcharges`: Under that collision, a window-computed price that meets the floor charges some non-certifying step at least one.
- `window_showing_reading_has_no_collision`: If certification is a function of the window, no such collision exists.
- `window_showing_reading_prices_exactly`: If certification is a function of the window, some window-computed price meets the floor and never overcharges.
- `step_entropy_invariant_if_injective`: An injective step leaves the Shannon entropy of any distribution unchanged.
- `entropy_le_log_support`: The Shannon entropy of a distribution is at most the base-2 logarithm of the size of any list that contains its support.
- `permanent_step_entropy_ceiling`: On a finite state space with permanent certification, after a step that switches states on, any distribution living on the certified and flipping states has entropy at most `log2(m)`.
- `permanent_step_entropy_drop`: Under the same premises, the step lowers entropy by at least `H(p) - log2(m)`.
- `permanent_flip_uniform_entropy_drop`: From the uniform distribution on the `m + k` states in play, the step removes at least `log2((m + k)/m)` bits.
- `merge_pair_removes_a_bit`: For any finite list of states without repeats covering every state, any map f and any two different states x and x' with f x = f x', the spread with chance one half on each of x and x' loses at least one bit of Shannon entropy when pushed through f.
- `permanent_flip_spread_loses_a_bit`: On a finite machine with a permanent reading, if a move turns some no-state yes, then it sends some two different states x and x' to the same state, and the spread with chance one half on each of them loses at least one bit when pushed through the move.
- `a2_from_entropy_price_and_permanence`: On a finite state space with permanent certification, a whole-unit cost that covers the bits each instruction removes meets A2.
- `entropy_drop_le_log_fibre`: On a finite state space with decidable equality, if no state has more than K >= 1 states that a move sends to it, then for every probability distribution the move lowers Shannon entropy by at most log2 K bits.
- `entropy_drop_of_fibre`: On a finite state space with decidable equality, the uniform distribution on the nonempty set of states a move sends to one state y is a distribution, and the move lowers its entropy by at least log2 of that set's size.
- `worst_case_entropy_drop`: On a finite state space with decidable equality, if no state has more than K >= 1 states that a move sends to it and some state y0 has exactly K, then every distribution loses at most log2 K bits through the move, and the uniform distribution on the states sent to y0 is a distribution that loses exactly log2 K bits.
- `entropy_priced_iff_compression_priced`: On a finite state space with decidable equality, a whole-number cost covers the entropy each move removes from every distribution exactly when it satisfies the halving price (`compression_priced`).
- `merging_priced_iff_pair_halving`: For any states with decidable equality, every non-injective move costs at least 1 exactly when every list of at most two distinct states has length at most 2^cost times the number of distinct states the move sends it to.
- `merging_priced_iff_pair_entropy`: On a finite state space with decidable equality, every non-injective move costs at least 1 exactly when the cost of each move is at least the entropy it removes from every distribution supported on at most two states.
- `one_premise_three_forms`: On a finite state space with decidable equality: entropy pricing holds exactly when the halving price holds; the halving price holds exactly when no state has more than 2^cost states sent to it by a move; and merge pricing holds exactly when the halving price holds for lists of at most two distinct states, and exactly when entropy pricing holds for distributions on at most two states.
- `entropy_priced_trace_floor`: Under the same premises, a trace from uncertified to certified costs at least one.
- `permanent_flip_heat_floor`: On a finite state space with a permanent reading, under the named premise `landauer_heat` and with `0 <= kT`, an instruction flipping k > 0 states beside m certified ones, on the uniform input distribution over those m + k states, has mean heat at least `kT ln((m + k)/m)`.
- `permanent_flip_heat_positive`: Under the same premise, with `k` at least one and positive temperature, that heat is positive.
- `entropy_drop_as_point_sum`: For nonnegative weights `p` on a repeat-free list of every state, the entropy a deterministic step removes equals a sum over states of positive probability of `p(x) (log2 q(f x) - log2 p(x))`.
- `entropy_drop_nonneg`: Under the same premises, that entropy drop is never negative.
- `entropy_drop_pos_of_support_merge`: Under the same premises, the drop is positive when two different states of positive probability land on the same state.
- `permanent_flip_full_support_entropy_drop_positive`: A permanent flip removes positive entropy from any distribution positive on the certified states and the flipping state.
- `permanent_flip_full_support_heat_positive`: Under `landauer_heat` with positive temperature, that flip forces positive heat.
- `known_state_step_removes_no_entropy`: A step from a point mass removes no entropy.
- `known_state_flip_forces_no_heat`: From a point mass, `landauer_heat` holds exactly when the heat is non-negative, so no positive heat is forced.
- `fiber_bound_compression`: If every image of a map has at most `K` preimages in a duplicate-free list, the list has at most `K` times as many members as distinct images.
- `fin_finite`: The eight states of the finite certification machine form a duplicate-free list of every state.
- `fin_permanent`: The finite machine never revokes its flag.
- `fin_merging_priced`: Every merging instruction of the finite machine costs at least one.
- `fin_compression_priced`: Every instruction of the finite machine meets the squeeze price.
- `fin_a2_from_merging_price`: A2 holds for the finite machine, derived from the merge price.
- `fin_a2_from_compression_price`: A2 holds for the finite machine, derived from the squeeze price.
- `fcertify_merges`: The finite machine's certify instruction is not injective.
- `fjump_merges`: Every finite-machine jump is not injective.
- `fnext_injective`: The finite machine's next-slot instruction is injective.
- `retained_history_step_injective`: For any step function, the history-keeping step, which moves to the next state and pushes the old state onto a history list, is injective for each instruction.
- `history_simulates_observed_step`: For any step function, the state part of the history-keeping step (the first component of the new pair) is the original step applied to the state part, for every state, history and instruction.
- `clock_record_permanent`: The record of the clock core, switched on when its hidden clock reads five, never switches off.
- `toggle_computation_driven`: The toggle core's next record value is a function of the counter base's state and its current record value.
- `toggle_not_permanent`: The toggle core's record switches off at some step.
- `growing_record_decomposes_holds`: Every honest growing extension (a record whose next value is a function of the base state and its current value, that only grows in a Boolean-decidable partial order, whose monotone ledger charges every strict change, and that changes at some reachable step) has, for every threshold `a`, a next value of "`a` is at most the record" equal to its current value or'd with an event of the base state and record, and keeps that pricing.
- `thresholds_determine_record_holds`: In a Boolean-decidable partial order, two values that every threshold `a` answers the same way ("`a` is at most it") are equal.
- `record_price_iff_threshold_price_holds`: For a record that only grows, a monotone ledger that charges every strict change of the record exactly matches a monotone ledger that charges every step at which some threshold switches on.
- `one_latch_refuted`: Not every honest growing extension can be carried by a single Boolean latch on base events together with a decoding from the base state and the latch.
- `chain_needs_bits_holds`: A list of distinct `k`-bit vectors in which each vector is pointwise at most the next has at most `k + 1` members.
- `deterministic_latch_handles_branching_refuted`: Not every honest probabilistic record (positive branch weights, a successor for every value, true staying true, and every false-to-true branch charged) has each successor equal to the current value or'd with a deterministic function of it.
- `schedule_determines_probabilities_refuted`: Two honest probabilistic records with the same branch supports and the same charges need not have the same weighted branches.
- `weak_base_equiv_refl_holds`: Every base machine with any observation is weakly equivalent to itself.
- `weak_base_equiv_sym_holds`: Weak base equivalence is symmetric.
- `weak_base_equiv_trans_holds`: Weak base equivalence is transitive.
- `weak_equiv_preserves_record_latch_holds`: If two base machines are weakly equivalent (a relation covering both sets of initial states, keeping observations and halting equal, and matching each step on either side by some number of steps on the other), the record axis is a latch on one exactly when it is a latch on the other.
- `weak_match_left_runs`: If every step of the first base machine from a related pair is matched by some number of steps of the second, then every `k`-step run of the first from a related pair is matched by some run of the second.
- `weak_match_right_runs`: The mirror statement, with every step of the second machine matched by some number of steps of the first.

### Merges, grades and the record ceiling on finite machines

- `nec_f_orbit_merges_visited`: For any type with decidable equality, any reading, any map f and any finite list of all states, if the reading is false at a start s0 and true at every point of f's orbit from some step N on, then f sends two different states of that orbit to the same state.
- `nec_f_repeat_merges_visited`: On a finite machine with decidable state equality, if one move repeated from a start whose reading is false leaves the reading true at every step from some point on, the move sends two different states of that run to the same state.
- `nec_f_closed_merges_visited`: On a finite machine with decidable state equality, for any rule picking the next move from the state, if the run from a start whose reading is false has the reading true at every step from some point on, two different states of that run, each taking its own picked move, land on the same state.
- `nec_f_word_merges_visited`: On a finite machine with decidable state equality, if a word of moves repeated from a start whose reading is false leaves the reading true after every repetition from some point on, then the word splits as u, a letter c, and the rest, and for two repetition counts m and n the states after m or n repetitions followed by u are different and c sends them to the same state.
- `nec_f_outside_moves_no_merge`: On the two-state machine where one move swaps the states and the other leaves them alone, the swap followed by any number of idle moves from the state reading false ends in the state reading true, and neither move sends two different states to the same state.
- `nec_f_same_rung_same_cups`: In any Boolean preorder, if x is at or below y and y is at or below x, then for every a the threshold a <= x has the same truth value as a <= y.
- `nec_f_non_partial_cups_fail`: In any Boolean preorder with two different places each at or below the other, there are two different places that leave every threshold with the same truth value.
- `nec_f_cups_iff_partial`: In any Boolean preorder, the thresholds determine the place (two places with the same threshold values are equal) if and only if the order is antisymmetric.
- `nec_f_record_ceiling_unique`: On any machine with a reading, a per-step charge that charges every raising step at least one and whose total over every run is at most the number of raising steps in it charges every step exactly one if it raises the reading and zero otherwise.
- `nec_f_three_automorphism_id`: On the three-state machine (blank, once, twice; flip and smooth), every injective map of the states that commutes with both moves is the identity.
- `nec_f_three_toll_meets`: On the three-state machine, the charge of one for the flip from blank and nothing else meets all six reading-free requirements: no charge on a step that changes nothing, none on a move that forgets nothing, invariance under every move-respecting renaming, a run total that adds over concatenation, a charge that depends only on the state before and after, and one unit on the flip from blank.
- `nec_f_three_merge_meets`: On the three-state machine, the charge of one for the flip from blank and one for the smooth from once, and nothing else, meets the same six reading-free requirements.
- `nec_f_three_bills_differ`: The toll and the price on merging charge the smooth from once differently, zero and one.
- `nec_f_three_ceiling_picks_toll`: On the three-state machine, any per-step charge that charges every raise at least one and whose total over every run is at most the number of raises equals the toll charge at every state and move.
- `nec_f_three_merge_fails_ceiling`: The price on merging does not satisfy the ceiling: some run on the three states costs more under it than the number of raises in that run.
- `nec_f_three_cs_floor`: The three-state machine with the flip costing one and the smooth costing nothing is a certification system, and every run from blank that ends in a yes-state costs at least one.
- `nec_f_board_raw_free`: On the board, every move other than VOUCH leaves the state where it was and costs nothing.
- `nec_f_board_floor`: On the board as a certification system, every run from NO that ends in YES costs at least one.
- `nec_f_board_floor_flat`: For any property of states that holds of YES, some run from NO ends in a state with that property, reading yes, at total cost exactly one.
- `nec_f_board_no_wait`: On the board, the run consisting of VOUCH alone takes NO to YES at cost one with no CHECK in it, and the run CHECK then VOUCH takes NO to YES at cost one.
- `nec_f_history_infinite`: No duplicate-free list of lists of Booleans contains every list of Booleans, so the history machine's state space has no finite enumeration.

### Narrowing: what is priced and what costs nothing

- `run_narrowing_priced_log`: For a finite deterministic machine whose costs meet the squeeze price, a program run from any duplicate-free set `D` of starting states satisfies `log2_up|D| <= cost(t) + log2_up|D'|`, where `D'` is the set of states the run can end in.
- `demon_machine_spread_kept`: In the two-bit measuring machine, the measuring step from the two blank-display states can still end in two different states.
- `wipe_costs_at_least_one`: In the two-bit measuring machine, every cost that meets the squeeze price charges the display wipe at least one.
- `observer_narrowing_can_be_free`: The cost of the two-bit measuring machine that charges 0 for the measuring step and 1 for the wipe meets the squeeze price, and observer-narrowing pricing fails for it: for some repeat-free candidate list, true start in it and trace, the rounded-up logarithm of the number of candidates the observer still considers possible drops by more than the trace's cost.
- `demon_refutes_incremental`: In the two-bit measuring machine (a hidden bit and a display, observed through the display), incremental observer-narrowing pricing fails: it is false that, for every repeat-free candidate list, every true start in it and every trace, the drop in the rounded-up logarithm of the observer's candidate list from the empty trace to that trace is at most the trace cost. The proof's witness is the one-step measuring trace, whose cost is zero.
- `free_incremental_narrowing_with_three`: A three-state cyclic machine with zero costs meets the squeeze price, and a zero-cost trace strictly shrinks the observer's candidate list relative to the empty trace.
- `no_free_incremental_narrowing_below_three`: For every n at most two, no finite machine with exactly n states, squeeze-priced and running a zero-cost trace, leaves the observer with strictly fewer candidates than after the empty trace; with two states or fewer the window is constant on every state once two starting states look alike.
- `demon_observer_learns`: In the two-bit measuring machine, starting from the prior list `[(false, false); (true, false)]` with actual state `(true, false)`, the observer's candidate list after one measuring step has one member, the prior has two, and the step costs zero.
- `measure_forgets_nothing`: The two-bit machine's measuring step, which adds the hidden bit into the display by exclusive-or, is injective.
- `wipe_merges`: The two-bit machine's wipe step, which blanks the display, is not injective.

### The ledger

- `run_writer_is_run_and_cost`: Running a trace in the writer monad over the natural numbers returns the state the trace reaches and the trace's total cost.
- `a2_iff_nonnegative_amortized_cost`: For any step function, cost, and yes/no reading, A2 holds exactly when every step's cost plus the change in the potential "one if uncertified, zero otherwise" is non-negative.
- `nfi_by_potential`: Under A2, a trace from an uncertified state to a certified one costs at least one, by the potential method's telescoping bound.
- `certification_system_is_potential_method`: Every `CertificationSystem` has non-negative amortized cost under the certification potential.
- `run_graded_is_run`: With costs indexed by instruction, running a trace as a computation graded by the trace's total cost gives the same final state as running it.
- `a2_and_aara_iff_exact`: For any step function, state-dependent cost, and yes/no reading, A2 together with the AARA inequality for the potential "one if uncertified, zero otherwise" holds exactly when certifying steps cost one, all other steps cost zero, and no step switches the reading off.
- `flips_le_cost`: Under A2, the number of false-to-true switches of the reading along any trace is at most the trace's total cost.

- `potential_telescoping`: In the section's generic step-and-cost setting, if a potential `Phi` has non-negative amortized cost on every step, then for every trace and start state the trace's total cost plus `Phi` of the final state is at least `Phi` of the start state.

## What stays

### Replicated-record examples

- `toggle_game_refutes_strong_pointer_necessity`: Consensus, authentic observer views, a positive observer count, and coordinator-free evolution do not imply event permanence, because the two-observer toggle game satisfies those premises and revokes its event.
- `durable_consensus_implies_permanence`: A positive observer count, authentic observer views, and durable true views imply event permanence; durability is the premise that supplies the conclusion.

- `toy_cert_unique_pointer`: In the chosen replicated-ledger toy, the certificate predicate proliferates and the single designated work predicate does not.
- `pointer_on_unique`: Two events that are each the pointer (the strongest event copied by every observer and relied on by every non-producing observer) on the same reachable states agree on every one of those states.
- `independent_copies_everywhere_are_constant`: If observers' carriers are independent (each view reads its own part, and any two parts can be set separately) and there are at least two observers, an event every observer decides exactly on every state is constant.
- `ledger_carriers_independent`: In the replicated-header toy, the three nodes' copies are independent carriers.
- `ledger_copying_alone_does_not_separate`: In the replicated-header toy, on synced states both "finalized" and "gas used is at least one" are decided by every node's copy.
- `ledger_finalized_is_pointer`: In the replicated-header toy, "finalized" is copied by every node, relied on by every non-producing node, and implies every other event copied and relied on in that sense on synced states.
- `ledger_gas_not_relied_on`: In the replicated-header toy, "gas used is at least one" is not relied on by the non-producing nodes.
- `PoS_model_unique_pointer`: In the synthetic PoS-labelled mirror model, every stipulated observer exposes the selected flag and omits the named rival.
- `Gas_model_unique_pointer`: In the synthetic gas-labelled mirror model, every stipulated observer exposes the selected flag and omits the named rival.
- `TEE_model_unique_pointer`: In the synthetic TEE-labelled mirror model, every stipulated observer exposes the selected flag and omits the named rival.
- `CT_model_unique_pointer`: In the synthetic transparency-labelled mirror model, every stipulated observer exposes the selected flag and omits the named rival.
- `PCC_model_unique_pointer`: In the synthetic PCC-labelled mirror model, every stipulated observer exposes the selected flag and omits the named rival.
- `deniable_authentication_model_not_proliferating`: The selected flag does not proliferate under the stipulated Boolean observer maps of the deniable-authentication-labelled model; no deniability or security property is formalized.
- `mac_model_not_proliferating`: The selected flag does not proliferate under the stipulated Boolean observer maps of the MAC-labelled model; no MAC security property is formalized.
- `capability_model_not_proliferating`: The selected flag does not proliferate under the stipulated Boolean observer maps of the capability-labelled model; no capability or memory-safety property is formalized.
- `public_log_model_proliferating`: The selected flag proliferates under the stipulated Boolean observer maps of the public-log-labelled model; no log protocol is formalized.
- `public_log_effort_not_proliferating`: In the same public-log-labelled model, the rival effort predicate does not proliferate, because no observer map reads the effort counter; this shows the control model discriminates between events.
- `twelve_candidate_measurements_checked`: The conjunction of twelve claims about named finite models: in each of the proof-of-stake, gas, TEE, certificate-transparency, and proof-carrying-certificate models the selected event is redundantly proliferating and the named rival event is not; the symmetric-MAC event is not redundantly proliferating; the digital-signature event is.
- `swapped_event_is_pointer_checked`: In `swap_ecosystem` (states with two booleans, three observers each reading `swap_second`), `second_event` (`swap_second` is true) is redundantly proliferating and `first_event` (`swap_first` is true) is not.
- `toy_work_not_proliferating`: In the replicated-ledger toy, the event "the work counter is at least one" is not recorded by every observer.
- `blind_observer_blocks_proliferation`: If some observer below the observer count reports false at a state where the event holds, the event is not redundantly proliferating.
- `labeled_model_verdicts`: In the stipulated labelled models, the deniable-authentication, MAC, and capability events are not redundantly proliferating, the public-log inclusion and digital-signature events are, and observer 0 of the deniable model records its event; no security property is formalized.

## What a window forgets

### What a window loses

- `thiele_simulates_turing`: Lifting a Turing configuration and running the file-local Thiele model for `n` steps gives the Turing machine's configuration after `n` steps.
- `thiele_simulates_turing_gen`: For every fuel, transition table `delta`, and Thiele configuration `tc`, the Turing configuration inside `thiele_run fuel delta tc` equals `tm_run fuel delta` applied to the Turing configuration inside `tc`, whatever the `th_mu` value of `tc`.
- `thiele_strictly_extends_turing`: Two conjuncts about the `ProperSubsumption.v` Turing and Thiele step functions: every Turing computation `TM_computes delta c_init c_final` has a Thiele computation from `lift_config c_init` with some cost whose final Turing configuration is `c_final`; and for every fuel, table, and configuration, the `cc_witness` of `thiele_cost_certificate` (the `th_mu` increase, by natural subtraction) is at most its `cc_bound`, which is `fuel * (step_cost + 1)`.
- `decoding_requires_fiber_constancy`: If some decoder of an observation returns a query on every state, the query is constant on each set of states with the same observation.

### Trace and projection contracts

- `selected_representatives_give_decoder`: Given a representative for every view whose observation is that view, a query is constant on observation fibers exactly when it factors through a decoder of the view.
- `independent_coordinates_joint_change_costs_one`: On pairs of Booleans, the two coordinates are independent observations, the step from (false, false) to (true, true) raises both, the least cost meeting both unit floors on that step is 1, and the constant cost 1 respects each floor.
- `nat_recursion_theorem`: For the candidate-decider-dependent nat substrate, every transformer selected by its representability predicate has a code whose total run equals the transformer's image on every input state.

### Information and witness contracts

- `compression_priced_trace_floor`: On an enumerated finite state space with permanent certification and compression pricing, an instruction-list run from uncertified to certified costs at least one.
- `priced_reset_satisfies_premises`: The two-state Blank/Stamped machine is finite, keeps its stamp permanently, and prices every merging step at one.
- `step_price_is_exact`: The defined full-state certification-flip indicator price meets the flip floor and never overcharges.
- `decision_tree_leaves_le_pow2_depth`: A decision tree has at most `2^depth` leaves.
- `decision_tree_log2_up_leaf_bound`: The rounded-up base-2 logarithm of a decision tree's leaf count is at most its depth.

### Adequacy, selection and finite validation

- `operational_adequacy_iff`: For a supplied successor relation, view and outputs, with explicit representatives and permitted successor choices, deterministic output and next-view maps exist exactly when outputs are constant on view fibres and all permitted successors of equal-view sources under a common instruction have equal views.
- `branching_answers_exclude_exact_deterministic_encoding`: If one state and instruction admit two successors with different required answers, no encoding into a deterministic host can commute with every permitted successor and preserve those answers.
- `hidden_bit_blocks_visible_only_dynamics`: Copying the hidden coordinate of a Boolean pair into its visible coordinate has no next-visible-state function depending only on the old visible coordinate.
- `toggle_symmetry_forces_constant_reading`: A Boolean reading on two states that is invariant under Boolean negation has the same value on all states.
- `no_nonconstant_renaming_invariant_toggle_reading`: No Boolean reading on the two-state toggle can both respect its state-exchange symmetry and distinguish any pair of states.
- `finite_observations_do_not_establish_permanence`: For every natural horizon, the specified delayed-reset clock agrees with the enduring reading through the next tick, starts false, raises at tick one and resets one tick after that comparison interval; the enduring reading is permanent, the delayed one is not, and both satisfy the actual unit-price toll.

## The room a kept distinction needs

### A distinction that stays

- `step_law`: For any step on any type with decidable equality and any start, every step of the run is fresh (its new state equals no earlier state), or a merge (it equals an earlier state reached from a different state, so two distinct states share an image), or a return to the start, or a revisit from the same state as before. The labels can overlap after the first revisit; the two lemmas below give the shape without double counting.
- `first_revisit_start_or_merge`: If the step from position n is the first that lands on an earlier state, position j, then j is the start or the state before position j differs from the state at n, so the two share a next state: the first return is to the start or a merge.
- `later_steps_repeat`: After any revisit, every later step is a step the run already took, from the same state to the same state, so nothing after the first return merges anew.
- `merge_is_collision`: A merge in the sense of the step law exhibits two distinct states with the same image under the step.
- `revisit_means_loop`: Once a run returns to a state it visited at position j, every later state of the run is one it visited at some position at most n, the position of the return.
- `partial_raises_without_merge`: On two states with a partial step, a steps to b, b has no successor, the reading is false on a and true on b, and no two states share a successor.
- `totalised_halt_is_merge`: Totalising that step with the halted state stepping to itself makes a and b, which differ, share the image b.
- `write_is_permanent`: On the states blank, zero and one, the write of a 0 keeps a definite cell definite.
- `write_raises`: The write of a 0 takes the blank cell, which reads not definite, to a cell that reads definite.
- `write_is_a_merge`: Blank and zero both step to zero under the write, and blank differs from zero.
- `four_state_escape_fails`: With a fourth state that remembers the cell was blank, the write still sends blank and that fourth state to the same state, and they differ.
- `tape_write_injective`: On an endless tape, writing one more cell sends different tapes to different tapes.
- `tape_write_never_returns`: On an endless tape, writing one more cell never returns to the empty tape.
- `shift_bijective`: Stepping one cell along the integers is one-to-one and onto.
- `shift_raises_and_keeps`: The reading "at least one" is false at 0, true after one step from 0, and stays true under the step.
- `shift_never_returns`: After any positive number of steps along the integers, the state differs from the start.
- `no_space_holds_its_own_readings`: For any type and any coding of its states as yes/no readings on it, some reading is coded by no state.
- `regress_price_unbounded`: For every m there is a count N whose rounded-up base-two logarithm is at least m.
- `nondet_merge`: With a step relation, a duplicate-free closed set of yes-states each having a chosen successor inside the set, and a no-state related to a yes-state, some yes-state has two distinct predecessors.
- `returns_to_start`: An injective step on a finite duplicate-free list containing every state brings the run from any start back to the start after a positive number of steps.
- `reversible_keeps_nothing`: Under such a step, a reading that is false at the start and never goes from true to false is false at every step of the run.
- `noisy_chairs`: For a nonnegative kernel whose rows and columns each sum to one, and a closed set of states, every entry from a state outside the set into a state inside it is zero.
- `raise_breaks_uniform`: If a nonnegative row-stochastic kernel with a closed set has a positive entry from outside the set into it, some column sum of the kernel differs from one.
- `colsums_total`: For a nonnegative row-stochastic kernel on n states, the column sums add to n.
- `raise_concentrates`: If a list of rationals sums to its own length and some member differs from one, the sum of the squares strictly exceeds the length.
- `uniform_floor`: If every member of a list of rationals equals one, the sum of the squares equals the length.
- `raise_concentrates_uniform`: A nonnegative row-stochastic kernel on n states with a closed set and a positive entry into it from outside has column sums whose squares add to strictly more than n.
- `no_merge_no_concentration`: For a nonnegative kernel whose rows and columns each sum to one, the sum of the squares of a spread after one step is at most the sum of the squares before.
- `gibbs_nonneg`: For a strictly positive spread on N states summing to one, the sum over states of the probability times the natural logarithm of N times the probability is nonnegative.
- `gibbs_strict`: That sum is strictly positive as soon as some probability differs from 1/N.
- `relent_is_entropy_gap`: That sum equals the natural logarithm of N minus the Shannon entropy of the spread.
- `quantum_chairs`: For an n by n matrix U over the algebraic numbers with conjugate transpose times U equal to the identity, and a Hermitian idempotent P with (1 minus P) U P equal to zero, P U (1 minus P) is zero.
- `heat_at_any_speed`: For a forward probability p strictly between 0 and 1 and not one half, the biased walk's entropy production per tick, (2p minus 1) times the natural logarithm of p over (1 minus p), is strictly positive.
- `no_heat_at_rest`: At p equal to one half that entropy production is zero.
- `heat_time_floor`: For a speed v strictly between 0 and 1 and a nonnegative distance N, N times the logarithm of (1 plus v) over (1 minus v), times N over v, is at least N squared.

## Records over any base and the diagonal

### Latching an event

- `latch_constant_up`: For any base machine and any event that holds at every base state, the record-carrying machine that latches the event has its record up after one step from every base state with the record down and any ledger.
- `latch_distinguishes`: For any base machine, event and two base states, if the event holds at one of the first n states of the first run and at none of the first n states of the second, the latch's record after n steps from the first state is up and from the second is down, both started with the record down and ledger 0.

### Clocks, reachable states and partitions

- `record_axis_is_latch_r1_r4`: Over any base, a record driven by the computation and permanent factors as the latch of some event; the ledger, toll and reachable-write clauses are not hypotheses.
- `record_axis_is_latch_reachable`: Over any base, a permanent record driven by the computation on every state a run reaches from a starting state factors as the latch of some event on those states.
- `clock_not_reachably_driven`: The record switched on at the fifth tick of a hidden clock, with every state a starting state, is not driven by the computation even on the states runs reach.
- `sync_clock_not_driven`: The same clock with starting states (b, b, off) is not driven by the computation when every state counts.
- `sync_clock_reachably_driven`: The clock with starting states (b, b, off) is driven by the computation on every state its runs reach.
- `sync_clock_reachable_latch`: The clock with starting states (b, b, off) is, on every state its runs reach, the latch of the event "the base state is 5".
- `sync_clock_record_permanent`: The record of the clock with starting states (b, b, off) never switches off.
- `grouping_partition`: For any pile of items and any grouping of them by bucket label, the classes of "same label" form a partition of the items.
- `grouping_sound_structural`: For any key and any two groupings with the same partition of the pile, one is sound for the key exactly when the other is.
- `sound_transfers_iff_refines`: For groupings g and h of a pile, soundness of g for a key gives soundness of h for that key, for every key, exactly when h refines g.
- `sound_only_for_refinements`: For groupings g and h of a pile where h does not refine g, there is a key for which g is sound and h is not.

### Diagonal and undecidability

- `structural_shortcut_undecidable`: For any substrate with a shortcut predicate, no decider whose diagonal flip is representable in the substrate decides the predicate.
- `nat_structural_shortcut_undecidable`: For each candidate `d`, the nat substrate built from `d` has no decider with a representable flip for its predicate.
- `nat_self_undecidable`: Each candidate `d` fails to decide the predicate of the substrate built from it.
- `mk_app_enc`: In the weak call-by-value calculus L, applying the application-code builder to the codes of terms s and t reduces in finitely many steps to the code of the application s t.
- `rec_spec`: For closed values F and v in L, applying rec F to v reduces in finitely many steps to F (rec F) v; the lemma does not assert termination of that resulting computation.
- `Qn_spec`: For every natural n, the numeral-quoting program Qn applied to the Scott numeral for n reduces in finitely many steps to the syntax code of that numeral.
- `Q_spec`: In the L lambda calculus, the quote combinator maps the code of any term to the code of its code.
- `second_recursion`: In L, every closed value `s` has a closed term `t` that reduces to `s` applied to the code of `t`.
- `L_recursion_theorem`: In L, every transformer that some closed L value computes on codes has a program equivalent to its image.
- `L_rice`: In L, no closed term decides, from programs' codes, a property that depends only on the values programs reach and that holds for one closed program and fails for another.
- `L_structural_shortcut_undecidable`: In L, no Boolean decider for such a property has an L-computable flip.
- `L_halting_undecidable`: No closed L term decides, from programs' codes, whether an L program reaches a value.
- `star_value_confluent`: In the calculus L of `LRecursion.v`, if `s` reduces to `t` and to `v` in zero or more steps and `v` is a value (a lambda), then `t` reduces to `v` in zero or more steps.

## The world

### Scalar physics and geometry contracts

- `canonical_reset_heat_exact`: In the frozen two-state reset protocol, the bath heat for an energy gap `Delta` is exactly `Delta / 2`.
- `selected_gap_gives_landauer_heat`: Choosing the two-state energy gap to be `2 * k_B * T * ln 2` makes the frozen reset protocol's bath heat exactly `k_B * T * ln 2`.
- `master_equation_does_not_fix_heat_scale`: Two distinct energy gaps obey the same frozen population master equation but transfer different heat, so those population dynamics alone do not determine an energy scale.
- `calibrated_mu_landauer_energy`: For all reals `k_B` and `T`, every state type `S`, every natural-number ledger `mu` on it and every state with `mu s = 1`, `mu_energy_at_scale mu (k_B * T * ln 2) s` equals `k_B * T * ln 2`; the scale is the supplied argument, so this is the arithmetic `mu s * scale`.
- `canonical_reset_satisfies_master_equation`: One step of the discrete two-state master equation, with the protocol's fixed time step and transition rates, carries the frozen initial populations exactly to the frozen final populations.
- `canonical_reset_heat_below_landauer_at_small_gap`: For positive `k_B` and `T`, the canonical reset (population one half to zero, up rate 0, down rate 1) with energy gap `k_B * T * ln 2` books bath heat strictly less than `k_B * T * ln 2`, so this bookkeeping toy obeys no Landauer floor.
- `canonical_rates_break_detailed_balance`: For every `kT` and gap `Delta`, the canonical reset's rates (up 0, down 1) do not satisfy detailed balance: 0 is not 1 times `exp (- Delta / kT)`.
- `detailed_balance_settles_at_gibbs`: For rates `k01`, `k10` in detailed balance at gap `Delta` (`k01 = k10 * exp (- Delta / kT)`), any time step `dt` and any population `p`, one master-equation step minus the equilibrium population `1 / (1 + exp (Delta / kT))` equals `(1 - dt (k01 + k10))` times `p` minus that population.
- `detailed_balance_thermalizing_step`: For rates in detailed balance at gap `Delta` and a time step with `dt (k01 + k10) = 1`, one master-equation step takes every population to the equilibrium population `1 / (1 + exp (Delta / kT))`.
- `detailed_balance_never_empties`: For rates in detailed balance at gap `Delta`, a time step with `1 - dt (k01 + k10)` at least 0, and a population at least the equilibrium population, the equilibrium population is positive and one master-equation step leaves the population at least that value.
- `landauer_gap_settles_at_one_fifth`: For `k_B * T` nonzero, the equilibrium excited population `1 / (1 + exp (Delta / (k_B T)))` at gap `Delta = 2 k_B T ln 2` is exactly `1/5`.
- `driven_first_law`: For every `kT`, gap schedule `g` and number of steps `n`, the driven reset's work equals its heat plus the register's mean energy at the end, `g n` times the equilibrium population at `g n`, minus the mean energy at the start.
- `driven_work_second_law`: For `kT` positive and a gap schedule that never falls over its first `n` steps, the driven reset's work over those `n` steps is at least the free energy `- kT ln (1 + exp (- Delta / kT))` at the final gap minus that at the first gap.
- `driven_work_near_free_energy`: For `kT` positive and a gap schedule each of whose first `n` steps rises by between 0 and `h`, the driven reset's work over those `n` steps is at most the free-energy change plus `h` times the fall in equilibrium population from the first gap to the last.
- `driven_reset_work_window`: For `k_B * T` positive, `D` at least 0 and `N` at least 1, the driven reset along `N` equal raises from gap 0 to `D` does work between `kT ln 2 - kT exp (- D / kT)` and `kT ln 2 + D / (2 N)`, with `kT = k_B * T`, and its final equilibrium population is at most `exp (- D / kT)`.

- `five_labeled_models_have_selected_pointer`: In the five synthetic labelled mirror models, each selected flag is returned by every stipulated observer and its named rival is not.

- `mu_has_no_intrinsic_joule_value`: For every state type and natural-number ledger `mu` on it, two real-valued functions on states exist that give 1 and 2 on every state with `mu` equal to 1, so the counter by itself fixes no energy value.

### Relaxation and entropy production

- `rc_contract`: On a finite chain with steady spread pi and detailed balance, if every listed row satisfies P x y >= delta * pi y with delta > 0, then for any vector p of total mass 1, one step shrinks sum_x |p x - pi x| by at least the factor 1 - delta.
- `rc_converges`: Under that condition, for every probability vector p and listed state x, the chain's spread at x after t steps converges to pi x as t grows.
- `rc_known_start_gap`: Under that condition, with m > 0 a lower bound on pi over the listed states, the entropy produced in the first T steps from the point mass at s falls short of - ln (pi s) by at most (4 / m) (1 - delta)^(2T).
- `rc_known_start_limit`: Under that condition, the entropy produced in the first T steps from the point mass at a listed state s converges to - ln (pi s) as T grows.
- `rcd_sigma_nonneg`: For rates q >= 0 and a positive steady spread pi with detailed balance pi x q x y = pi y q y x, the continuous-time entropy production rate of any positive vector is nonnegative.
- `rcd_D_derivative`: For any solution p t of the master equation that is positive after time 0, at every time t > 0 d/dt p t x = sum_y (p t y q y x - p t x q x y), the relative entropy of p t to pi has derivative minus the entropy production rate.
- `rcd_D_monotone`: For any solution of the master equation that is positive after time 0, and times 0 < t1 <= t2, the relative entropy to pi at t2 is at most its value at t1.
- `rs_split`: On a finite chain with a stationary spread pi and a reading splitting states into up and down, the steady mass that has stayed among the up-states for k steps equals the flow into the up-states times the spread of stretches still running after k steps, plus the mass that stays one step more.
- `rs_partial`: The flow into the up-states times the sum, over k < n, of the chances that a stretch entered through that flow lasts more than k steps equals the steady mass of the up-states minus the mass that has stayed n steps.
- `rs_mean_stretch`: Under Doeblin's condition (every listed row puts at least delta times pi everywhere) and with positive mass on the down-states, the mean length of a stretch with the flag up, counted in steps from entry through the flow, converges to the steady mass of the up-states divided by the flow into them.
- `rcd_produced_window`: For any solution of the master equation that is positive after time 0 and times 0 < a <= b, the Newton integral of the entropy production rate from a to b equals the relative entropy to pi at time a minus that at time b.
- `rcd_produced_bounds`: For any solution of the master equation that is positive after time 0 and times 0 < a <= b, if the relative entropy at time b is nonnegative then the entropy produced from a to b lies between 0 and the relative entropy at time a.
- `rcl_sigma_ge`: With rates satisfying q x y >= c pi y for all listed x, y (c > 0), detailed balance and pi of total mass 1, the continuous-time entropy production rate of any positive vector of total mass 1 is at least c times its relative entropy to pi.
- `rcl_D_decay`: Under that condition, for a solution of the master equation that is positive after time 0 and has total mass 1 at time 0, the relative entropy at time b is at most its value at time a times exp (- c (b - a)), for 0 < a <= b.
- `rcl_D_limit`: Under the same hypotheses, the relative entropy to pi tends to 0 as time grows.
- `rcl_produced_limit`: Under the same hypotheses, the entropy produced from time a > 0 to time b, the Newton integral of the production rate, tends to the relative entropy at time a as b grows.
- `rcl_D_at_zero`: Under the same hypotheses and with a nonnegative start, the relative entropy at time t tends to its value at time 0 as t decreases to 0, including where the start puts no weight.
- `rcl_known_start_total`: Under the same hypotheses, from the point mass at a listed state s, the entropy produced from a small time a out to a large time b comes within any given margin of - ln (pi s).
- `rsc_mass_over_flow`: For a finite chain in continuous time with rates q x y >= 0 and a spread pi that is stationary (the flow into each listed state equals the flow out of it), and a reading splitting states into up and down, any solution h of the leaving-time equations (out x times h x minus the sum over up-states y of q x y h y equals 1 at every listed up-state x) satisfies: the flow into the up-states times the mean of h over the entrance spread equals the steady mass of the up-states.
- `rsc_leave_exists`: With rates satisfying q x y >= c pi y for all listed x, y (c > 0) and a positive flow into the up-states, the leaving-time equations have a solution: the limit of the uniformized iteration, which grows and stays between 0 and 1 / (c pi(down)).
- `rsc_S_decay`: Under the same hypotheses, for any nonnegative solution of the master equation with the chain stopped on leaving the up-states, started from the entrance spread, the chance that the stretch is still running at time b >= 0 is at most exp (- c pi(down) b).
- `rsc_window_value`: For such a solution and any solution h of the leaving-time equations, the Newton integral from 0 to T of the chance that the stretch is still running equals the steady mass of the up-states over the flow into them, minus the h-weighted total of the stretches still running at time T.
- `rsc_mean_stretch_time`: Under the same hypotheses, the time a stretch spends with the flag up between 0 and T, the Newton integral of the chance it is still running, comes within any given margin of the steady mass of the up-states divided by the flow into them for all large T.
- `rsc_stretch_identity`: The same limit, with the leaving times the theorem rsc_leave_exists constructs: in continuous time, the mean length of a stretch with the flag up, in seconds, is mass over flow.
- `re_gibbs`: For two probability vectors on a finite list of states, where the second is positive wherever the first is, the relative entropy of the first against the second is nonnegative.
- `re_pi_stationary`: On a finite chain whose rows sum to one and whose positive distribution pi satisfies detailed balance, one step of the chain leaves pi unchanged at every state of the list.
- `re_sigma_is_drop`: On such a chain, for any nonnegative vector p, the entropy produced in one step (the relative entropy of the forward flow p x P x y against the backward flow (pP) y P y x) equals the relative entropy of p to pi minus that of pP to pi.
- `re_sigma_nonneg`: On such a chain, the entropy produced in one step from any probability vector is nonnegative.
- `re_relative_entropy_monotone`: On such a chain, one step never raises the relative entropy of a probability vector to pi.
- `re_known_start_total`: On such a chain with a list without repeats, from the point mass at a listed state s, the entropy produced in the first T steps equals -ln pi(s) minus the relative entropy to pi of the distribution after T steps.
- `re_known_start_bound`: On such a chain, from the point mass at a listed state s, the entropy produced in the first T steps lies between 0 and -ln pi(s).
- `re_known_start_vs_set`: For a list of states containing s, -ln pi(s) is at least -ln of the total pi-mass of the list.
- `re_flux_balance`: On such a chain, the pi-weighted flow from the states reading no to the states reading yes equals the flow from yes back to no.
- `re_stretch_ratio`: For any positive flow J and positive mass of the no-states, -ln of that mass equals ln (1 + (mass of yes-states / J) / (mass of no-states / J)).

### Models from other fields

- `quote_cannot_attest_unmeasured_state`: In the scoped TPM quote-field abstraction, whose quote authenticity is not modeled (it is assumed externally), no function of the selected-PCR digest and nonce returns the additional runtime Boolean for every platform.
- `quote_decides_measured_claims`: In the same model, every supplied Boolean function of the retained selected-PCR digest is computed by some Boolean function of the quote.
- `persistent_write_priced`: In the transcribed Prague `sstore` gas and refund arithmetic, for one storage slot that is empty at the start of a transaction, any sequence of stores that leaves it nonzero has gas charged minus refund counter of at least 20000; the EIP-3529 refund cap is outside the model.
- `revoked_write_nearly_free`: In the same model, setting a cold empty slot to one and clearing it again costs 2300 net, while setting it and leaving it set costs 22100.
- `accountable_safety` (`Kernel.CasperFFG.accountable_safety`): In the ported Casper FFG model, under the setting's quorum-intersection and single-parent premises, two finalized blocks on different branches imply that some set in the second quorum class consists of slashed validators.
- `conflicting_records_are_priced`: Reading finalization as the record, two finalized blocks on different branches imply a slashed set in the second quorum class; this restates accountable safety.
- `finalization_without_slashing`: In the one-validator chain setting, a single vote finalizes the genesis block and no validator is slashed.
- `ct_local_view_insufficient`: In the two-field certificate-transparency client model, no function of the local signed tree head number returns the world-consistency bit for every state.
- `tpm_selection_binding_is_necessary`: In the two-selection quote model, some input passes the check that inspects only the composite digest while its signed and supplied PCR selections differ.
- `weak_subjective_suffix_insufficient`: In the two-field weak-subjectivity model, no function of the local suffix returns the trusted-anchor bit for every state.
- `wal_ack_requires_durability`: In the two-bit write-ahead-log model, some state has the client acknowledgement set while crash recovery does not recover the commit.
- `audit_local_snapshot_insufficient`: In the two-bit audit model, no Boolean function of the current local log bit returns whether the event occurred for every state.
- `tpm_interface_authenticity_refuted`: Not every signature-scheme interface satisfies quote authenticity (every accepted signature is the signing of the message by some secret key); the interface alone does not provide it.
- `pcc_checker_accepts_iff_vc`: In the memory-access fragment of proof-carrying code, the checker accepts a program exactly when every instruction obeys the memory-limit policy.
- `pcc_certificate_implies_vc`: In that fragment, every certificate derivation for a program implies the program obeys the policy.
- `pcc_unsafe_program_rejected`: With memory limit 2, the checker rejects `[PRead 2; PHalt]`.
- `rfc9162_inclusion_boundary_safe`: For every hash algorithm, inclusion verification with leaf index equal to the tree size returns false.
- `rfc9162_consistency_boundary_safe`: For every hash algorithm, consistency verification between two trees of the same size with the same root returns false.
- `rfc9162_example_inclusion_d0`: With the symbolic hash on the seven-leaf example tree, the audit path `[b; h; l]` verifies leaf hash `a` at index 0 against the root.
- `rfc9162_example_inclusion_d3`: The audit path `[c; g; l]` verifies leaf hash `d` at index 3 against the example root.
- `rfc9162_example_inclusion_d4`: The audit path `[f; j; k]` verifies leaf hash `e` at index 4 against the example root.
- `rfc9162_example_inclusion_d6`: The audit path `[i; k]` verifies leaf hash `j` at index 6 against the example root.
- `rfc9162_example_consistency_4_7`: The consistency proof `[l]` verifies the size-4 root `k` against the size-7 example root.
- `ct_extension_preserves_entries`: Appending entries to a log keeps every old entry in it.
- `casper_fork_exists`: In the concrete three-validator Casper FFG setting with unit stakes, blocks `HA1` and `HB1` on different branches are each finalized at epoch 1 by the quorums `{VA, VB}` and `{VB, VC}`, neither is an ancestor of the other, the state has a finalization fork, and both are finalized records.
- `casper_fork_slashable`: In that setting some second-class quorum consists of slashed validators, the set `{VB}` is such a quorum and is slashed, and `VA` and `VC` are not slashed.
- `janus_like_unbounded_inverse`: For integer add and subtract instructions, applying the syntactic inverse after the instruction returns the original value.
- `janus_like_bounded_inverse`: For a positive modulus and a value in `[0, modulus)`, applying the inverse after the instruction, both reduced modulo the modulus, returns the original value.
- `concrete_ram_write_reads_back`: Writing a value at an address that holds some value and reading that address gives the written value.

## Verifiers and finite premises

### Verifiers

- `ver_collision_blocks`: If two states A and B, one satisfying a claim and one not, stand behind the same transcript, no verifier is both sound and complete for the claim.
- `ver_no_factor`: If two states of opposite claim have explanations whose projections agree, no sound and complete verifier reads its answer through that projection.
- `ver_full_state_escape`: A verifier that is given the full state is sound and complete for any claim about it.
- `ver_honest_meets_contract`: A commitment bit that is the honest reading of the explanation satisfies the binding-and-honesty contract.
- `ver_unchecked_breaks_contract`: If some state that does not satisfy the claim stands behind a transcript, a commitment bit taken without checking does not satisfy the contract.
- `ver_commitment_escape`: Under the binding-and-honesty contract, a verifier that reads the commitment bit is sound and complete for the claim.
- `ver_response_escape`: If a truthful response of the state decides the claim, a verifier that accepts the response is sound and complete for the claim.

### Which finite premises are needed

- `nec_f_a2_iff_flipping_merges_priced`: For any machine with move costs and a permanent reading whose yes-states are exactly the members of some list without repeats, A2 (every move that turns a no-state into a yes-state costs at least 1) holds exactly when every move that turns some no-state yes and sends two different states to one state costs at least 1.
- `nec_f_a2_without_entropy_pricing`: The eight-state machine (four slots and a certified bit) with CERTIFY costing 1 and every JUMP and NEXT costing 0 meets A2 but is not entropy priced: some move and some probability distribution on its eight states lose more bits of entropy than the move's price.
- `nec_f_a2_without_merge_pricing`: The eight-state machine with CERTIFY costing 1 and every JUMP and NEXT costing 0 is finite, has a permanent reading and meets A2, yet some move that sends two states to one costs 0, while every move that both turns some no-state yes and merges states is still priced.
- `nec_f_bit_price_iff_halving`: For any machine with decidable equality of states and move costs, the bit price (for every move and every list D without repeats, the rounded-up log2 of the length of D is at most the move's cost plus the rounded-up log2 of the number of distinct states the move sends D to) holds exactly when the halving price holds.
- `nec_f_bit_rises_exact`: For every k, on the one-bit machine where SET costs 1 and RESET costs 0, the run of k repetitions of SET then RESET started at no turns the reading from no to yes exactly k times and costs exactly k.
- `nec_f_collision_avoids_s`: The four-state chain c0 (reading no) and c1, c2, c3 (reading yes), whose one move sends c0 to c1, c1 to c2, and c2 and c3 to c3, is finite with a permanent reading, turns c0 from no to yes, has c0 as the only state landing on c1, and sends c2 and c3 to the same state.
- `nec_f_conservation`: On every counter machine (a counter that reads 0 at the start and grows by each move's price), the counter after any run t from any state s equals the counter at s plus the total price of t.
- `nec_f_conservation_iff_rule`: On every counter machine, a reading m of states into natural numbers ends every run at its starting value plus the run's total price exactly when every single move raises m by that move's price.
- `nec_f_cost_ge_rises`: For any system of states, moves, move costs and a yes-or-no reading that meets A2 (every move from a no-state to a yes-state costs at least 1), every run from every state costs at least the number of times the reading goes from no to yes along it.
- `nec_f_counter_monotone`: On every counter machine the counter never decreases along a run: its value at a state s is at most its value after any run from s.
- `nec_f_descent_fails_for_history`: The one-bit machine with SET costing 1 and RESET costing 0 meets A2, yet descent fails for the target that records every move: the runs SET and RESET, SET from off leave the bit in the same state but give different histories.
- `nec_f_descent_iff_functional`: For a source machine and a target fold over the same moves, descent (any two move lists that take the source from its start to the same state take the target from its start to the same state) holds exactly when each source state reached by some list is related to only one target state.
- `nec_f_drop_pos_iff_support_merge`: For a list of all states without repeats, any move f and any nonnegative weights p, the entropy of p minus the entropy of its image under f is positive exactly when f sends two different states of positive weight to the same state.
- `nec_f_drop_zero_of_support_injective`: For a list of all states without repeats, any move f and any nonnegative weights p, if f never sends two different states of positive weight to the same state, then the entropy of p minus the entropy of its image under f is exactly 0.
- `nec_f_entropy_bounds_attained`: For every m and n at least 1, the grid with m rows and n + 1 columns (reading yes exactly in column zero, the move sending each cell to column zero of its row) is finite with a permanent reading, flips its n times m other cells, has m yes-states, and on the even spread its entropy after the move is exactly log2 m and its drop is exactly log2 of (m + n m) over m.
- `nec_f_entropy_eq_log_support`: For a list without repeats, a probability distribution r on it and a nonempty list Sup containing every listed state of positive chance, if the entropy of r equals log2 of the length of Sup, then every listed state of positive chance has chance exactly one over that length.
- `nec_f_entropy_invariant_iff_injective`: For a list of all states without repeats and any move f, f is injective exactly when every probability distribution has the same entropy after f as before.
- `nec_f_entropy_toll_needs_finite`: The history machine (states are bit lists, the one move puts true in front, the reading is yes on every nonempty list), with an empty list of states and the move costing 0, is entropy priced and has a permanent reading, yet A2 fails.
- `nec_f_entropy_toll_needs_permanent`: Negation on one bit at cost 0, with states false and true and the bit as the reading, is finite and entropy priced, yet A2 fails.
- `nec_f_factor_gives_descent`: For a source machine and a target fold over the same moves, if some map from source states sends the source state reached by every move list to the target value of that list, then any two move lists that take the source to the same state take the target to the same value.
- `nec_f_finite_counter_charges_nothing`: On every counter machine whose states are all listed in a finite list without repeats, every move has price 0.
- `nec_f_flip_collision_in_yes_and_s`: For any machine with decidable equality of states whose yes-states are exactly the members of a list Y without repeats, if move i never turns a yes-state into a no-state and turns the no-state s into a yes-state, then two different states among s and the members of Y land on the same state under i.
- `nec_f_floor_at_iff_free_reach`: For any system and any start s0 reading no, every run from s0 that ends reading yes costs at least 1 exactly when every move that turns a no-state into a yes-state, at a state s0 reaches by moves of cost 0, costs at least 1.
- `nec_f_floor_iff_a2`: For any system of states, moves, costs and a yes-or-no reading, A2 (every move from a no-state to a yes-state costs at least 1) holds exactly when every run from a no-state to a yes-state costs at least 1.
- `nec_f_floor_one_attained`: On the one-bit certification system with SET costing 1 and RESET costing 0, the start no reads no, the single move SET reaches yes, and that run costs exactly 1.
- `nec_f_fold_unique`: For any step function on targets with start t0, every map g from move lists to targets that sends the empty list to t0 and sends a list l followed by a move i to the step of g(l) by i equals the left fold of the moves from t0.
- `nec_f_forced_iff_merges_isolated`: For any machine and any move i that can be decided equal or not to every move, i is forced to be priced (every cost assignment charging each merging move at least 1 charges i at least 1) exactly when i sends two different states to the same state.
- `nec_f_forced_without_merge_under_continuity`: If every function from bit sequences to numbers depends only on a finite prefix of its input, then on the machine whose states are numbers and whose moves are bit sequences (a move sends m to 0 when it has a true bit at or below m, otherwise leaves m), the all-false move is forced to be priced yet is injective.
- `nec_f_free_stamp_floor_fails`: On the one-bit system where SET and RESET both cost 0 and the bit is the reading, some run from a no-state to a yes-state costs less than 1.
- `nec_f_full_support_needs_s`: For every kT, the point mass on the stamped sheet gives the blank sheet chance 0 and the stamped sheet positive chance, and zero heat meets Landauer's bound (heat at least kT ln 2 times the entropy drop) for that distribution under the stamp move.
- `nec_f_full_support_needs_yes`: For every kT, the point mass on the blank sheet gives the blank sheet positive chance and the stamped sheet chance 0, and zero heat meets Landauer's bound for the entropy drop of that distribution under the stamp move, which sends both sheets to stamped.
- `nec_f_grid_cost_least`: For every m at least 1 and every c, on the grid with m rows and 2 to the c columns whose one move sends every state to column zero of its row, every cost meeting the halving price charges that move at least c.
- `nec_f_heat_determines_gap`: Two energy gaps that give the same bath heat in the canonical reset (excited-state probability one half before and zero after, under a fixed two-level Hamiltonian) are equal.
- `nec_f_heat_floor_attained`: For every m and n at least 1 and every real kT, on the grid with m rows and n + 1 columns under the even spread, the heat kT ln 2 times the entropy drop meets Landauer's bound and equals kT ln of (m + n m) over m.
- `nec_f_heat_floor_needs_nonneg_kT`: The three-state machine with yes-states Y1 and Y2 and no-state S0, whose move sends every state to Y1, is finite with a permanent reading and flips S0, and with kT = -1 and the even spread on its three states the heat -ln 2 times the entropy drop meets Landauer's bound yet is below the floor -ln (3/2).
- `nec_f_heat_positive_needs_kT`: For every entropy drop dH, zero heat meets Landauer's bound (heat at least kT ln 2 times dH) when kT is 0, and 0 is not positive.
- `nec_f_initiality`: On every counter machine, books that read 0 at the start and grow by each move's price at every state agree with the counter on every state reachable from the start.
- `nec_f_initiality_iff`: On every counter machine, books that read 0 at the start agree with the counter on every reachable state exactly when they grow by each move's price at every reachable state.
- `nec_f_initiality_needs_reachable`: On the idle counter machine (states the two bits, start false, one move that changes nothing and costs 0, counter 5 on true and 0 on false), the books reading 7 on true and 0 on false start at 0 and follow the price list, but true is unreachable and the books disagree with the counter there.
- `nec_f_initiality_needs_zero_start`: On every counter machine, the books that read the counter plus 1 grow by each move's price at every state yet disagree with the counter on every state.
- `nec_f_initiality_reachable_rule`: On every counter machine, books that read 0 at the start and grow by each move's price at every reachable state agree with the counter on every reachable state.
- `nec_f_invariance_needs_complete_list`: Over the list holding only true, which has no repeats but omits false, with weight 1/2 on true and 0 on false, negation is injective yet changes the listed entropy.
- `nec_f_invariance_needs_nodup`: Over the list true, true, false, which names every bit but repeats true, with weight 1/2 on true and 0 on false, the identity move changes the listed entropy.
- `nec_f_jump_merges_never_flips`: On the eight-state machine, every JUMP move sends two different states to the same state and never turns a no-state into a yes-state.
- `nec_f_landauer_gap_unique`: For all real kB, T and gap D, the bath heat of the canonical reset with gap D equals kB T ln 2 exactly when D equals 2 kB T ln 2.
- `nec_f_least_cost_exists`: For every m at least 1 and every k there is a whole cost c with m + k at most 2 to the c times m such that c is 0 or c - 1 does not meet that bound.
- `nec_f_least_cost_is_ceiling`: For m at least 1, if a whole cost c meets m + k at most 2 to the c times m and either c is 0 or c - 1 does not meet it, then c - 1 is below log2 of (m + k) over m and that logarithm is at most c.
- `nec_f_ln_strict`: For every positive real y other than 1, ln y is strictly less than y - 1.
- `nec_f_machine_narrowing_iff_halving`: For any machine with decidable equality of states and move costs, the narrowing bound (for every run t and every list D without repeats, the rounded-up log2 of the length of D is at most the cost of t plus the rounded-up log2 of the number of distinct states t reaches from D) holds exactly when the halving price holds.
- `nec_f_merging_priced_weakens`: For any machine with move costs and a yes-or-no reading, if every move that sends two different states to one costs at least 1, then every move that sends two different states to one and turns some no-state yes costs at least 1.
- `nec_f_narrowing_equality`: For every m at least 1 and every c, on the grid with m rows and 2 to the c columns whose one move costs c, the move run from all cells meets the narrowing bound with equality: the rounded-up log2 of the number of cells equals c plus the rounded-up log2 of the number of distinct cells reached.
- `nec_f_narrowing_needs_nodup`: The demon machine (a hidden bit and a display; Measure adds the bit into the display at cost 0, Wipe blanks it for 1) meets the halving price, yet for the list naming the state (false, false) twice and the empty run the narrowing bound fails.
- `nec_f_one_state_observer_priced`: Every machine with at most one state, listed without repeats, satisfies observer narrowing pricing for any moves, costs and observation (the drop in the rounded-up log2 of the candidates consistent with what the observer saw is at most the run's cost).
- `nec_f_paid_door_floor`: In the three-room system (rooms A and B read no, C reads yes; PAY costs 1 and moves A to B, FREE costs 0 and moves B to C, every other move stays put), every run from A that ends reading yes costs at least 1.
- `nec_f_paid_door_not_a2`: In the same three-room system, room B is reachable from A and A2 fails, since the move FREE turns B, a no-state, into C, a yes-state.
- `nec_f_potential_bound_exact`: For any machine, move costs and potential Phi, along a run t from s whose every step has zero amortized cost (cost plus potential after equal to potential before), the total cost of t plus the final potential equals the potential at s.
- `nec_f_potential_bound_iff`: For any machine with move costs and any natural-number potential Phi, every step has nonnegative amortized cost (cost plus potential after at least potential before) exactly when every run from every state s has total cost plus final potential at least Phi at s.
- `nec_f_qfloor_from_any_witness`: For any system with a natural-number witness and a threshold N meeting A3 (a move raises the witness by at most its cost) and A5 (every yes-state has witness at least N), every run from a state s that ends reading yes costs at least N minus the witness at s.
- `nec_f_qfloor_raw`: For any system with a witness and a threshold N meeting A3 and A5, every run from a state of witness 0 that ends reading yes costs at least N, with no use of A2 or of a start reading no.
- `nec_f_quant_needs_a3`: On the natural numbers with one move that jumps every state to 2 at cost 1, reading yes from 2 on and witness equal to the state, A2 and A5 with threshold 2 hold and A3 fails, and the one-move run from 0 reaches 2 at cost 1, below the threshold 2.
- `nec_f_quant_needs_a5`: On the natural numbers with one move adding 1 at cost 1, reading yes from 1 on and witness equal to the state, A2 and A3 hold, A5 with threshold 2 fails, and the one-move run from 0 reads yes at cost 1, below 2.
- `nec_f_quant_needs_a6`: In the quantitative counter system with threshold 2 (one move adding 1 at cost 1, reading yes from 2 on, witness equal to the state), the state 1 has witness 1 and reads no, and one move reaches yes at cost 1, below the threshold 2.
- `nec_f_quant_tight`: For every N, the quantitative counter system with threshold N has witness 0 at state 0, and N moves from 0 reach yes at total cost exactly N, which is the threshold.
- `nec_f_repo_quantitative_from_raw`: In every quantitative certification system (a certification system with a witness meeting A3 and A5 for its threshold), every run from a state of witness 0 that ends reading yes costs at least the threshold.
- `nec_f_rises_iff_a2`: For any system of states, moves, costs and a yes-or-no reading, A2 holds exactly when every run from every state costs at least the number of times the reading goes from no to yes along it.
- `nec_f_rounded_log_form_weaker`: With m = 3 and k = 1, the rounded-logarithm bound (rounded-up log2 of 3 + 1 at most 0 plus rounded-up log2 of 3) holds while the integer bound 3 + 1 at most 2 to the 0 times 3 fails.
- `nec_f_scales_always_disagree`: For any states, any ledger reading mu, two different real scales a and b, and any state s whose reading is nonzero, the energy mu(s) times a differs from the energy mu(s) times b.
- `nec_f_smaller_gap_iff`: For all real kB and T, the bath heat of the canonical reset with gap kB T ln 2 is strictly below kB T ln 2 exactly when kB times T is positive.
- `nec_f_smaller_gap_negative_pair`: With kB = -1 and T = -1, the bath heat of the canonical reset with gap (-1)(-1) ln 2 is strictly below (-1)(-1) ln 2.
- `nec_f_squeeze_needs_finite`: The history machine at cost 0 has a permanent reading and meets the halving price, and the empty history is a no-state its move turns yes, yet with the empty list taken as all states the squeeze bound 1 + 0 at most 2 to the 0 times 0 fails.
- `nec_f_squeeze_needs_halving`: The stamp machine on the blank and stamped sheets at cost 0 is finite with a permanent reading but does not meet the halving price, and the squeeze bound fails: one flipped blank sheet plus one stamped sheet exceed 2 to the 0 times 1.
- `nec_f_squeeze_needs_permanent`: Negation on one bit at cost 0 is finite and meets the halving price and turns false into true, yet the squeeze bound 1 + 1 at most 2 to the 0 times 1 fails.
- `nec_f_squeeze_real_iff`: For natural numbers m at least 1, k and c, the bound m + k at most 2 to the c times m holds exactly when log2 of (m + k) over m is at most c.
- `nec_f_squeeze_tight`: For every m and c, the grid with m rows and 2 to the c columns (reading yes exactly in column zero, one move of cost c sending each cell to column zero of its row) is finite, has a permanent reading, meets the halving price, has m yes-states, and turns a list without repeats of no-states yes whose length plus m is exactly 2 to the c times m.
- `nec_f_squeeze_tight_every_k`: For every m, k and c with m + k at most 2 to the c times m, the grid with m rows and 2 to the c columns (finite, permanent, halving priced, its move costing exactly c, with m yes-states) has a list without repeats of exactly k no-states that its move turns yes.
- `nec_f_perm_flip_merges_yes_finite`: For any machine whose yes-states are exactly the members of a list without repeats, a move that never turns a yes-state to no and turns some no-state to yes is not injective: it sends two different states to one.
- `nec_f_toll_from_merges_yes_finite`: For any machine whose yes-states are exactly the members of a list without repeats, whose reading is permanent and in which every move that sends two different states to one costs at least 1, every move from a no-state to a yes-state costs at least 1.
- `nec_f_two_state_observer_free`: The machine on one bit whose single move changes nothing and costs 0, observed through the bit itself, is finite and meets the halving price, yet fails observer narrowing pricing.
- `nec_f_two_states_never_teach`: On any machine with at most two states, listed without repeats, for every candidate list, run and true start, the candidates consistent with what the observer sees along the run are exactly those consistent with the first look alone.
- `nec_f_uniform_drop_exact_only_if_divides`: For a finite machine with a permanent reading, m yes-states and a nonempty list without repeats of k no-states that move i turns yes, if the even spread on those m + k states loses exactly log2 of (m + k) over m bits under i, then k is a multiple of m.
- `nec_f_uniform_drop_strict_unless_divides`: For a finite machine with a permanent reading, m yes-states and a nonempty list without repeats of k no-states that move i turns yes, if k is not a multiple of m, then the even spread on those m + k states loses strictly more than log2 of (m + k) over m bits under i.
- `nec_f_wipe_under_merge_pricing`: On the demon machine, every cost assignment that charges each move sending two states to one at least 1 charges Wipe at least 1.
- `nec_f_zero_drop_every_move_iff_one_state`: For a list of all states without repeats and nonnegative weights p, every move whatever leaves the entropy of p unchanged exactly when no two different states both have positive weight.
- `nec_t_blocks_of_equiv_partition`: For every type, the classes of any equivalence relation form a partition: every block has a member, every element lies in a block, blocks sharing a member have the same members, and the collection is closed under sets with the same members.
- `nec_t_blocks_round_trip`: For every partition P of a type, a set is a class of the relation "lie in a common block of P" exactly when it is a block of P.
- `nec_t_cover_needed`: There is a type with a collection of sets whose blocks all have members, whose blocks sharing a member have the same members, and which is closed under sets with the same members, but in which some element lies in no block, and its relation "lie in a common block" is not an equivalence relation.
- `nec_t_disjoint_needed`: There is a type with a collection of sets whose blocks all have members, which covers every element and is closed under sets with the same members, but whose relation "lie in a common block" is not an equivalence relation.
- `nec_t_nonempty_needed`: There is a type with a collection of sets that covers every element, whose blocks sharing a member have the same members, and which is closed under sets with the same members, but for which the classes of the relation "lie in a common block" are not exactly its blocks.
- `nec_t_rel_of_partition_equiv`: For every partition of a type, the relation "x and y lie in a common block" is reflexive, symmetric and transitive.
- `nec_t_rel_round_trip`: For every equivalence relation R on a type, two elements lie in a common class of R exactly when R relates them.
- `nec_w_accountable_safety_repo`: For every Casper setting and vote state, a finalization fork (two finalized blocks, neither an ancestor of the other) implies a second-class quorum, about one third of the validators, all of whose members are slashed for a double vote or a surrounding vote.
- `nec_w_billed_honest`: For every machine M that is an honest extension of a base through a cover, and every surcharge on M's states, the billed machine (M with a second ledger component that grows by the surcharge of the current state at each step) is an honest extension of the same base through the billed cover.
- `nec_w_billed_same_latch`: If the record of M factors through a latch h on the base, the record of the billed machine factors through the same latch h.
- `nec_w_billed_same_up_to_schedule`: The billed machine matches M through the relation "the first component is M's state": every start of either has a matched start of the other, matched states read the same record, halt together and step to matched states, and a matched billed state shows the same base state as M's.
- `nec_w_billed_step_cost`: If the ledger of M never decreases along a step, every step of the billed machine costs exactly M's step cost plus the surcharge at the current state.
- `nec_w_event_free_choice`: For any base machine and any two event tests h1 and h2 whose latch machines each reach, from some initial base state, a state where the event holds with the record still down, both latch machines are honest extensions of the base, and at every base state where h1 holds and h2 does not, one step from that state with the record down and ledger 0 raises the record of the first latch machine and leaves the record of the second down.
- `nec_w_forget_needs_settable`: With natural-number states and a "set" that returns the state unchanged, the identity window does not change when set is applied, and some rule on the window returns the counter at every state.
- `nec_w_forgetful_window_no_counter`: For any nonempty type of states with a counter, an operation set such that set s n has counter n, and a window that set does not change, no rule on the window returns the counter at every state.
- `nec_w_forgetful_window_no_flag`: For any nonempty type of states with a flag, an operation set such that set s b has flag b, and a window that set does not change, no rule on the window returns the flag at every state.
- `nec_w_fork_of_repo`: For every Casper setting and vote state, a finalization fork in the repository's sense is a fork in the stripped setting with the same validators, blocks, quorum classes, parent relation and genesis but without the quorum-intersection and single-parent premises, under the same votes.
- `nec_w_outside_decider`: For every d, the decider that answers yes on program 0, the negation of d(2) on program 2 and no on every other program answers yes on exactly the programs the nat substrate built from d admits, and its 0-or-1 indicator is not representable in that substrate.
- `ax_a2_from_compression`: An axis system with finitely many states, a growing record and the halving price (every repeat-free list of states has length at most 2 to the cost of an instruction times the number of its distinct images) obeys the toll.
- `ax_a2_from_merge_price`: An axis system with finitely many states whose record grows and in which every instruction that merges two states costs at least 1 obeys the toll.
- `ax_a2_iff_flipping_merges_priced`: In an axis system with finitely many states whose record grows, the toll holds exactly when every instruction that leaves the down-set of the record from some state and merges two states costs at least 1.
- `ax_a2_iff_views`: An axis system over any preorder obeys the toll exactly when, for every point a, its two-point view (the bit "a is below the record") obeys the one-bit toll.
- `ax_a2_threshold_form`: An axis system over any preorder obeys the toll exactly when every step that carries some point a from not below the record to below the record costs at least 1.
- `ax_block_loss_unbounded`: For every real number B there is an m such that, under the block prior (block k has 2^(2^k) states each weighted 1/((k+1)(k+2)) divided by 2^(2^k)), the sum of p ln(1/p) over the states of the first m blocks exceeds B.
- `ax_block_mass_n`: For every m, the block prior (block k has 2^(2^k) states, each weighted 1/((k+1)(k+2)) divided by 2^(2^k)) gives the first m blocks a total weight of exactly 1 - 1/(m+1).
- `ax_block_no_toll`: For every cost c there is an m such that c times ln 2 (the loss a toll of c bits covers on weight 1) is strictly below the sum of p ln(1/p) over the states of the first m blocks of the block prior.
- `ax_chain_rule`: For any weights p that are nonnegative on the states of a finite list of spots, the conditional entropy (the sum over spots of each spot's loss, p ln(W/p) summed with W the spot's weight) equals the sum over spots of W ln W minus the sum over all their states of p ln p.
- `ax_collapse_unpriceable`: For any type T with a state t0 and an injective map from the natural numbers into T, for every c there is a repeat-free list of more than 2^c states of T, and the collapse machine (every move, whose cost is its own number, sends every state to t0) fails the halving price for every equality test on T.
- `ax_compression_iff_fibres`: In an axis system with finitely many states listed without repeats, the halving price holds exactly when, for every move i and every state y, the number of listed states that i sends to y is at most 2 to the cost of i.
- `ax_cost_ge_exits`: In an axis system that obeys the toll, every run from every starting state costs at least the number of its steps whose new record is not below the record just before the step.
- `ax_decompose`: For a machine with a covering classical machine and a record in any preorder, if the record never drops (each next record is at or above the current one) and the next record is a function of the classical state and the current record, then there is an event h (reading a point, the classical state and the record) such that, for every state and point a, a is below the next record exactly when a is below the current record or h fires.
- `ax_entropy_split`: For any weights p that are nonnegative on the states of a finite list of spots, the entropy of the states (minus the sum of p ln p) equals the entropy of the spots (minus the sum of W ln W over the spot weights W) plus the conditional entropy.
- `ax_exact_without_position`: For the counter on the natural numbers with two moves, one adding 1 (cost 1) and one leaving it alone (cost 0), the record the counter itself, watched through its parity: the adding move always raises the record and the other never does; the parity changes on a step exactly when the step raises the record; no collision exists; some window price is exact (charging 1 exactly when the parity changed); no constant price is exact; and no function reads the counter off its parity.
- `ax_exit_collision`: In an axis system with finitely many states and a growing record, if a move i from some state leaves the down-set of the record, then two different states are sent by i to the same state.
- `ax_exit_is_strict_rise`: In an axis system whose record grows (every step ends at or above the record it started from), a step leaves the down-set of the current record (its new record is not below the old one) exactly when it rises strictly (the new record is above the old one and not below it).
- `ax_exit_merges_or_revokes`: In an axis system with finitely many states (listed without repeats), every step from s by instruction i that leaves the down-set of the record either is not injective (two different states go to the same state under i) or takes some state t whose record is at or above the new record of s to a state whose record is not.
- `ax_factor_determined`: Over an antisymmetric order, if a record of a machine with a covering classical machine admits a threshold factorization with some event h, then any two states with the same classical state and the same record have the same next record.
- `ax_factor_grows`: If a record of a machine with a covering classical machine admits a threshold factorization (some event h with a below the next record exactly when a is below the current record or h fires), then the record grows: every next record is at or above the current one.
- `ax_fibre_collapse_exit`: In an axis system with finitely many states and a growing record, with a projection to classical states that commutes with a classical step, if a move i leaves the down-set of the record from some state and the classical step for i is injective, then two different states with the same projection are sent by i to the same state.
- `ax_fibre_gibbs`: For weights p nonnegative on a nonempty list F, the loss of F (the sum of p ln(W/p) with W the weight of F) is at most W times the natural log of the length of F.
- `ax_flips_compression_bound`: In an axis system with finitely many states, a growing record, and the halving price (every repeat-free list of states has length at most 2 to the cost of i times the number of distinct images under i), every repeat-free list F of states that instruction i carries from not at or above a point a to at or above a satisfies: the length of F plus the number m of states at or above a is at most 2 to the cost of i times m.
- `ax_floor_iff_a2`: For every axis system (states, instructions, a step, a cost per instruction and a record that is a point of a preorder given by a Boolean test), the floor (every run whose final record is not below its starting record costs at least 1) holds exactly when the toll holds (every single step whose new record is not below the old one costs at least 1).
- `ax_geometric_loss`: For every n, under the geometric prior (state j has weight 1/2^(j+1)) the sum of p ln(1/p) over states 0 to n-1 equals ln 2 times (2 - (n+2)/2^n), and so is at most 2 ln 2.
- `ax_geometric_mass`: The partial sums of the geometric prior (state j has weight 1/2^(j+1)) over states 0 to n-1 converge to 1 as n grows.
- `ax_gibbs_code`: For weights p nonnegative on a finite list F, code lengths l whose Kraft sum (the sum of 1/2^l over F) is at most 1, and any real W at least the weight of F, the sum of p ln(W/p) over F is at most ln 2 times the sum of p times l plus W minus the weight of F.
- `ax_gibbs_code_uniform`: For weights p nonnegative on a list F of exactly 2^c states, the loss of F (the sum of p ln(W/p) with W the weight of F) is at most c times ln 2 times the weight of F.
- `ax_growth_exit_merges`: In an axis system with finitely many states whose record grows, every instruction i that leaves the down-set of the record from some state s is not injective: two different states go to the same state under i.
- `ax_inf_loss_bits`: In an axis system of any size with the halving price, for every move i, every nonnegative weighting p of the states and every finite list of landing spots y, each with a repeat-free list of exactly the states that i sends to y, the conditional entropy over those lists is at most their total weight times the cost of i times ln 2.
- `ax_inf_loss_series`: For nonnegative weights on the states and a sequence of spots each holding at most N states (N at least 1), if the total weight of the first n spots is at most M for every n, then the partial sums of the spots' losses converge to a limit L that is at most M times ln N.
- `ax_infinite_entropy_survives`: In an axis system of any size with the halving price, for every move i, nonnegative weighting and finite list of landing spots with exact repeat-free lists of the states landing on each, the entropy of those states is at most the entropy of the spots plus their total weight times the cost of i times ln 2.
- `ax_ln_pow2`: For every natural number c, the natural log of 2^c equals c times ln 2.
- `ax_loss_le`: For weights nonnegative on the states of a finite list of spots, if every spot has at most N states and N is at least 1, then the conditional entropy (the sum of the spots' losses) is at most the total weight times ln N.
- `ax_overcharge_lower`: For an axis system watched through a window, any price of observed transitions that meets the floor charges, along any run, at least the number of the run's steps that do not leave the down-set of the record but are shadowed (look the same as some step that does).
- `ax_overcharge_tight`: For an axis system watched through a window, if it is decidable for each pair of observations whether some step that leaves the down-set of the record shows them, then some price of observed transitions charges at least 1 on every step that leaves the down-set and, on every step that does not, charges exactly 1 exactly when the step is shadowed (some down-set-leaving step looks the same) and 0 when it is not.
- `ax_priced_loss_bits`: In an axis system with finitely many states (listed without repeats) and the halving price, for every move i, every nonnegative weighting and every list of target states, the conditional entropy over the fibres of i above those targets (the listed states i sends to each) is at most their total weight times the cost of i times ln 2.
- `ax_priced_loss_tight`: For every list F of exactly 2^c states, the uniform weighting 1/2^c gives F a loss of exactly c times ln 2.
- `ax_priced_spots`: In an axis system with an equality test on states, the halving price implies that no landing spot receives more than 2^cost states: every repeat-free list of states that move i sends to one state y has length at most 2 to the cost of i.
- `ax_spots_priced`: In an axis system with an equality test on states, if every repeat-free list of states that a move i sends to one state has length at most 2 to the cost of i, then the halving price holds (every repeat-free list of states has length at most 2 to the cost of i times the number of its distinct images).
- `ax_step_fibre_in_fibre`: For an axis system with a projection to classical states that commutes with a classical step, if the classical step for a move i is injective, then any two states that i sends to the same state have the same projection.
- `ax_threshold_view_separates`: In an axis system over any preorder, any two states whose records are not equivalent are told apart by some threshold a: the bit "a is below the record" differs between them.
- `ax_threshold_window_blind`: There is an axis system on the natural numbers (one move adds 1, the other stays, each at cost 1, the record the counter) with a window that shows only whether the record is at least 1, and that window has a collision: two steps look the same, one leaving the down-set of the record and the other not.
- `ax_thresholds_separate`: In any preorder given by a Boolean test, if two points x and y are not equivalent (not both x below y and y below x), then some point a is below one of them and not the other.
- `ax_toll_covers_landauer_minimum`: In an axis system with the halving price, for every move i, nonnegative kT, nonnegative weighting and finite list of landing spots with exact repeat-free lists of the states landing on each, the sum over those lists of kT times their loss is at most kT times ln 2 times the cost of i times their total weight.
- `ax_uniform_loss_exact`: For every list F of exactly n states with n at least 1, the uniform weighting 1/n gives F a loss (the sum of p ln(W/p) with W the weight of F) of exactly ln n.
- `ax_view_a2`: If an axis system over any preorder obeys the toll, then for every point a the two-point system that reads the same machine's record only as the bit "a is below the record" also obeys the toll.
- `ax_window_collision_overcharges`: For an axis system watched through a window, if there is a collision (two steps with equal observations before and after, one leaving the down-set of the record and the other not), then every price of observed transitions that charges at least 1 on each down-set-leaving step charges at least 1 on some step that does not leave it.
- `ax_window_exact_iff_no_collision`: For an axis system with finitely many states and moves, watched through a window whose observations have decidable equality, some price of observed transitions is exact (at least 1 on each step that leaves the down-set of the record and 0 on every other step) exactly when there is no window collision.
- `ax_window_no_exact_price`: For an axis system watched through a window with a collision (two steps with equal observations before and after, one leaving the down-set of the record and the other not), no price of observed transitions both charges at least 1 on every down-set-leaving step and charges 0 on every other step.
- `ax_window_sees_record_exact`: For an axis system watched through a window, if the record of every state is a fixed function of its observation, then some price of observed transitions is exact (at least 1 on each step that leaves the down-set of the record and 0 on every other step) and the window has no collision.
- `bp_thresholds_determine`: In a preorder given by a Boolean test that is antisymmetric, two points x and y with the same thresholds (every point a is below x exactly when a is below y) are equal.
- `two_point_is_join_latch`: For any machine with a covering classical machine and a one-bit record, if the record never goes from true to false and the next record is a function of the classical state and the current record, then there is an event g of the classical state alone such that the next record is the current record or g of the classical state.
- `two_point_nfi`: In every certification system, every run that starts in a state whose certificate bit is false and ends in a state whose certificate bit is true has total cost at least 1.
- `thresholds_fail_on_preorder`: In the preorder on the Booleans where each value is below the other, the order is not antisymmetric, and true and false get the same answer from every threshold although they are different.
- `indiscrete_loses_record`: There is a one-state classical machine with a Boolean record that switches value on every step, which grows and is driven by the computation in the preorder where each Boolean is below the other, and factors as a threshold latch whose event never fires, while every threshold gives the same answer at true and at false.
- `chain_bits_exact`: For every k, every repeat-free chain of k-bit words (each word's set bits among the next word's) has at most k + 1 members, and some such chain has exactly k + 1.
- `chain3_not_join_latch`: Over a one-state classical machine, the record on the three-point chain 0 < 1 < 2 whose next value is 2 from 0, 1 from 1 and 2 from 2 grows and is driven by the computation, and there is no fixed point g such that every next record is the least upper bound of the current record and g.
- `history_escape`: The axis system on the natural numbers whose record is the state, whose one instruction adds 1 and costs 0, grows, prices every non-injective instruction (it has none), has an injective step, leaves the down-set from every state, and does not obey the toll. It pays in fresh states instead, a new one at every step, which a price list that charges only merges doesn't see.
- `toggle_escape`: The two-state axis system on the Booleans whose one instruction negates the state at cost 0, with the two-point order, has the full list of states, prices every non-injective instruction, leaves the down-set from false, does not grow, and does not obey the toll.
- `free_merge_escape`: The two-state axis system on the Booleans whose one instruction sends every state to true at cost 0, with the two-point order, has the full list of states and a growing record, does not price its non-injective instruction, and does not obey the toll.
- `shadow_merge_escape`: The two-state Boolean axis system whose one instruction sends every state to true at cost 0 has the full list of states, a growing record, leaves the down-set from false and is not injective, while its projection (the identity) puts the two states in different fibres and its classical step (always true) is not injective.

