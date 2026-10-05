# What each cited theorem says

Coq checks that a proof matches its statement. It does not check that the
name or the prose around a theorem means what the statement says. This file
closes that gap for every theorem the README, the monograph, the
mathematical specification, the technical disclosure, and
`THIELE_MACHINE.txt` cite. Each entry is one plain sentence saying what the
Coq statement asserts, premises included.

`tests/test_theorem_meanings.py` fails when a document cites a theorem that
has no entry here, or when an entry names a theorem that does not exist.
The entries describe the current statements. Their accuracy requires reading
the quantified premises and conclusion; the gate checks coverage and names.
Where several modules use the same short name, the parenthesized qualified
name identifies the theorem meant by unqualified citations in these documents.
An explicitly qualified citation keeps its own module identity.

## Certification cost

- `universal_nfi_any_substrate`: In any `CertificationSystem`, whose record includes the rule that a step switching certification on costs at least one, a trace from an uncertified state to a certified one has total cost at least one.
- `universal_nfi_quantitative`: For every `QuantitativeCertificationSystem` QCS, trace, and start state whose witness value `qcs_witness` is zero, if the state reached by running the trace in the underlying certification system is certified, then the trace's total cost is at least `qcs_threshold QCS`.
- `honest_cost_tracking_strict_restriction`: Some cost-bearing system certifies at total cost zero, while every `CertificationSystem` needs cost at least one; the cost rule is what separates them.
- `free_forgery_violates_A2`: In any cost-bearing system, if some step switches certification from false to true at cost zero, the system fails the rule that every such step costs at least one.
- `commitment_cost_not_reducible_to_erasure_cost`: Some trusted erasure-accounting system certifies at total cost zero with no erasure reported, while every `CertificationSystem` needs cost at least one.
- `scs_run_embed`: For a `SimulatingCertificationSystem` over a host certification system, embedding the state its base system reaches on a trace equals the host's run of the concatenated decoded trace from the embedded start state.
- `host_represents_simulating_cert_system`: For a `SimulatingCertificationSystem` over a host certification system, a trace that goes from uncertified to certified in the base system has total cost at least one there, the host run of its decoded trace from the embedded start ends certified, and that host run has total cost at least one.

## Pricing the event

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

## Why A2 on finite hardware

- `permanent_flip_is_not_injective`: On a finite state space where certification is never revoked, a step that switches certification on is not injective.
- `permanent_at_flip_is_not_injective`: The same, needing permanence only for the one instruction that flips.
- `a2_from_merging_price_and_permanence`: On a finite state space with permanent certification, if every non-injective instruction costs at least one, then every certifying step costs at least one.
- `permanent_certification_trace_floor`: Under the same premises, a trace from uncertified to certified costs at least one.
- `permanent_flips_collapse_at_least`: A step that switches `k` distinct uncertified states on, beside the certified states, has at least `k` fewer distinct images than inputs.
- `honest_erasure_accounting_implies_a2`: In a trusted erasure-accounting system on a finite state space with permanent certification, if the erasure flag reports every merge, every certifying step costs at least one.
- `commit_without_erasure_system_is_not_honest`: The zero-cost commit-without-erasure system does not report its own merge.
- `unbounded_history_escapes`: Keeping the full history makes a step injective while it still switches certification on, using unbounded memory.
- `revocable_certificate_escapes`: Flipping a bit is injective and switches the reading on, because it also switches it off.
- `free_merge_escapes`: With merges unpriced, a stamping machine on a finite, permanent state space certifies at cost zero.
- `permanent_flips_compression_bound`: On a finite state space with permanent certification and costs where cost `c` allows at most a `2^c`-fold squeeze, switching `k` states on beside `m` certified ones satisfies `m + k <= 2^cost * m`.
- `permanent_flips_log_bound`: The same bound in rounded base-2 logarithms: `log2_up(m + k) <= cost + log2_up(m)`.
- `a2_from_compression_price_and_permanence`: Under finiteness, permanence, and the squeeze price, every certifying step costs at least one.
- `quad_stamp_cost_two_is_priced`: The four-state stamp priced at two meets the squeeze price.
- `quad_stamp_needs_two`: Every squeeze-priced cost for the four-state stamp is at least two.
- `forced_priced_iff_merges`: With decidable equality on instructions, an instruction is charged by every merge-pricing cost exactly when its step is not injective.
- `flip_merges_or_revokes`: On a finite state space, an instruction that switches a reading on somewhere either is not injective or switches the reading off somewhere.
- `injective_flip_revokes`: On a finite state space, an injective instruction that switches a reading on somewhere also switches it off somewhere.
- `permanent_record_write_is_forced_priced`: An instruction that never switches the reading off and switches it on somewhere is charged by every merge-pricing cost.
- `forced_price_without_permanent_record`: A three-state instruction is charged by every merge-pricing cost and still revokes the reading, so forced pricing does not imply a permanent record.
- `record_axis_is_latch_holds`: For any base machine and any record-carrying machine that covers it step for step, whose record never switches off, satisfies A2 with a monotone ledger, is written by some reachable step, and has its next value determined by the base state and its current value, there is a base event h such that the base state and record evolve exactly as the latch "switch on where h holds, never switch off."
- `record_axis_is_latch_on_tm_holds`: The record axis is a latch on the executable toy Turing-machine base for every program.
- `record_axis_is_latch_on_ram_holds`: The record axis is a latch on the Cook-Reckhow RAM base (unbounded natural-number registers, indirect load and store, conditional jumps) for every program.
- `record_axis_is_latch_on_l_holds`: The record axis is a latch on the L base, whose next function is L's weak call-by-value step on reducible terms and stutters on irreducible ones.
- `l_step_fun_correct`: For all L terms `s` and `t`, `s` takes one weak call-by-value step to `t` exactly when the structural step function `l_step_fun` returns `Some t` on `s`.
- `star_is_l_base_run`: Every L reduction sequence from `s` to `t` is reached by running the L base machine some number of steps from `s`.
- `permanent_write_has_logical_payment`: On a finite state space, if instruction `i` keeps the record on wherever it is on, and some state goes from record off to record on under `i`, then `i` is not injective.
- `record_pair_is_two_latches_holds`: Under the same conditions for two records, the pair evolves as two latches whose events may each read the other record.
- `toggle_not_latch`: A record on a counter base that flips at every step is driven by the computation and is not the latch of any event.
- `clock_record_not_driven`: A record switched on by a hidden clock at its fifth tick never switches off and is not driven by the computation.
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
- `a2_from_entropy_price_and_permanence`: On a finite state space with permanent certification, a whole-unit cost that covers the bits each instruction removes meets A2.
- `entropy_priced_trace_floor`: Under the same premises, a trace from uncertified to certified costs at least one.
- `permanent_flip_heat_floor`: Under the named premise `landauer_heat`, the uniform permanent flip dissipates at least `kT ln((m + k)/m)`.
- `permanent_flip_heat_positive`: Under the same premise, with `k` at least one and positive temperature, that heat is positive.
- `entropy_drop_as_point_sum`: The entropy a deterministic step removes equals a sum over states of positive probability of `p(x) (log2 q(f x) - log2 p(x))`.
- `entropy_drop_nonneg`: That entropy drop is never negative.
- `entropy_drop_pos_of_support_merge`: The drop is positive when two different states of positive probability land on the same state.
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

## Narrowing: what is priced and what is free

- `run_narrowing_priced_log`: For a finite deterministic machine whose costs meet the squeeze price, a program run from any duplicate-free set `D` of starting states satisfies `log2_up|D| <= cost(t) + log2_up|D'|`, where `D'` is the set of states the run can end in.
- `demon_machine_spread_kept`: In the two-bit measuring machine, the measuring step from the two blank-display states can still end in two different states.
- `wipe_costs_at_least_one`: In the two-bit measuring machine, every cost that meets the squeeze price charges the display wipe at least one.
- `observer_narrowing_can_be_free`: A particular squeeze-priced cost assigns zero to the injective measuring step of a two-bit machine even though an observer's candidates shrink; the lower-bound pricing rule does not prevent another admissible cost from overcharging that step.
- `demon_refutes_incremental`: In the two-bit measuring machine, the drop in the rounded logarithm of the observer's candidate list from the empty trace to the one-step measuring trace exceeds the trace cost, which is zero.
- `free_incremental_narrowing_with_three`: A three-state cyclic machine with zero costs meets the squeeze price, and a zero-cost trace strictly shrinks the observer's candidate list relative to the empty trace.
- `no_free_incremental_narrowing_below_three`: For every n at most two, no finite machine with exactly n states, squeeze-priced and running a zero-cost trace, leaves the observer with strictly fewer candidates than after the empty trace; with two states or fewer the window is constant on every state once two starting states look alike.
- `demon_observer_learns`: In the two-bit measuring machine, starting from the prior list `[(false, false); (true, false)]` with actual state `(true, false)`, the observer's candidate list after one measuring step has one member, the prior has two, and the step costs zero.
- `measure_forgets_nothing`: The two-bit machine's measuring step, which adds the hidden bit into the display by exclusive-or, is injective.
- `wipe_merges`: The two-bit machine's wipe step, which blanks the display, is not injective.

## The ledger

- `run_writer_is_run_and_cost`: Running a trace in the writer monad over the natural numbers returns the state the trace reaches and the trace's total cost.
- `a2_iff_nonnegative_amortized_cost`: For any step function, cost, and yes/no reading, A2 holds exactly when every step's cost plus the change in the potential "one if uncertified, zero otherwise" is non-negative.
- `nfi_by_potential`: Under A2, a trace from an uncertified state to a certified one costs at least one, by the potential method's telescoping bound.
- `certification_system_is_potential_method`: Every `CertificationSystem` has non-negative amortized cost under the certification potential.
- `run_graded_is_run`: With costs indexed by instruction, running a trace as a computation graded by the trace's total cost gives the same final state as running it.
- `a2_and_aara_iff_exact`: For any step function, state-dependent cost, and yes/no reading, A2 together with the AARA inequality for the potential "one if uncertified, zero otherwise" holds exactly when certifying steps cost one, all other steps cost zero, and no step switches the reading off.
- `flips_le_cost`: Under A2, the number of false-to-true switches of the reading along any trace is at most the trace's total cost.

- `potential_telescoping`: In the section's generic step-and-cost setting, if a potential `Phi` has non-negative amortized cost on every step, then for every trace and start state the trace's total cost plus `Phi` of the final state is at least `Phi` of the start state.

## What a window loses

- `no_mu_oracle` (`Minimal.EarnedCore.no_mu_oracle`): In minimal/EarnedCore.v, no function of the window (program counter and the two counters) returns mu for every trace run from `start 0 0`; minimal/MuCore.v proves the same for its strict shadow and `st_mu` over every state.
- `thiele_simulates_turing`: Lifting a Turing configuration and running the file-local Thiele model for `n` steps gives the Turing machine's configuration after `n` steps.
- `thiele_simulates_turing_gen`: For every fuel, transition table `delta`, and Thiele configuration `tc`, the Turing configuration inside `thiele_run fuel delta tc` equals `tm_run fuel delta` applied to the Turing configuration inside `tc`, whatever the `th_mu` value of `tc`.
- `thiele_strictly_extends_turing`: Two conjuncts about the `ProperSubsumption.v` Turing and Thiele step functions: every Turing computation `TM_computes delta c_init c_final` has a Thiele computation from `lift_config c_init` with some cost whose final Turing configuration is `c_final`; and for every fuel, table, and configuration, the `cc_witness` of `thiele_cost_certificate` (the `th_mu` increase, by natural subtraction) is at most its `cc_bound`, which is `fuel * (step_cost + 1)`.
- `decoding_requires_fiber_constancy`: If some decoder of an observation returns a query on every state, the query is constant on each set of states with the same observation.

## Diagonal and undecidability

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
- `MM2_HALTING_compl_undec`: The complement of two-counter machine halting, as the vendored library defines it, is undecidable in the library's synthetic sense.
- `star_value_confluent`: In the calculus L of `LRecursion.v`, if `s` reduces to `t` and to `v` in zero or more steps and `v` is a value (a lambda), then `t` reduces to `v` in zero or more steps.

## CHSH and NPA

- `local_box_CHSH_bound`: A factorizable box has absolute CHSH value at most 2.
- `chsh_stat_violation_not_local`: A tally with CHSH above 2 is inconsistent with any single four-bit strategy repeated at every trial.
- `chsh_violation_rules_out_locally_factorizable_coupling`: The same statement in coupling vocabulary.
- `locally_consistent_classical_bound`: A tally consistent with one four-bit strategy has absolute CHSH value at most 2.
- `cauchy_schwarz_chsh` (`Kernel.TsirelsonGeneral.cauchy_schwarz_chsh`): For any reals, `(a + b + c - d)^2 <= 4(a^2 + b^2 + c^2 + d^2)`.
- `tsirelson_from_row_bounds` (`Kernel.TsirelsonGeneral.tsirelson_from_row_bounds`): If `E00^2 + E01^2 <= 1` and `E10^2 + E11^2 <= 1`, the CHSH value squared is at most 8.
- `algebraically_coherent_tsirelson_general`: Algebraically coherent rational correlators have CHSH value squared at most 8.
- `quadratic_nonneg_discriminant`: If `a + 2bt + ct^2 >= 0` for every real `t`, then `b^2 <= ac`.
- `column_contractive_iff_npa_psd`: Four correlators are column-contractive exactly when their zero-marginal NPA moment matrix is symmetric and PSD. PSD of this matrix is NPA's level-1 test, not quantum realizability.
- `zero_marginal_npa_column_contractive_implies_psd`: The three column-contractivity inequalities imply the zero-marginal NPA matrix is PSD.
- `npa_psd_implies_column_contractive`: PSD of the zero-marginal NPA matrix implies column contractivity.
- `column_contractive_iff_general_realizable`: Column contractivity is equivalent to the dimension-generic PSD predicate at size five.
- `npa_psd_implies_tsirelson_bound`: If the zero-marginal NPA matrix is symmetric and PSD, the CHSH value squared is at most 8.
- `npa_psd_implies_tsirelson_bound_abs`: For any four reals `E00 E01 E10 E11`, if `zero_marginal_npa E00 E01 E10 E11` is positive semidefinite, then the absolute value of `CHSH E00 E01 E10 E11` is at most `sqrt8`.
- `npa_psd_zero_marginal_implies_row_bounds`: For any four reals, if `zero_marginal_npa E00 E01 E10 E11` is positive semidefinite, then `1 - E00^2 - E01^2 >= 0` and `1 - E10^2 - E11^2 >= 0` (the row minor constraints).
- `tsirelson_from_minors`: For four reals, if `1 - e00^2 - e01^2 >= 0` and `1 - e10^2 - e11^2 >= 0`, then the square of `CHSH e00 e01 e10 e11` is at most 8.
- `tsirelson_squared`: For four reals with `e00^2 + e01^2 <= 1` and `e10^2 + e11^2 <= 1`, `CHSH_value e00 e01 e10 e11` multiplied by itself is at most 8.
- `fine_theorem`: For any correlator table `E` that is factorizable (two `+1`/`-1` response functions, a probability distribution on finitely many hidden states, and `E a b x y` equal to the distribution-weighted sum of the products of the two responses), `E 0 0 0 0 + E 0 0 0 1 + E 0 0 1 0 - E 0 0 1 1` lies between -2 and 2.
- `column_contractive_check_witness_sound`: If the integer witness check passes, the witness-derived correlators are column-contractive.
- `sym4_qf_nonneg_from_pd`: If the four leading minors of a symmetric 4 by 4 matrix are positive, its quadratic form is non-negative.
- `psd_cauchy_schwarz`: For a symmetric PSD 5 by 5 matrix, the square of the bilinear form is at most the product of the two quadratic forms.
- `deterministic_strategy_elliptope`: Correlators from four signs have a PSD completion.
- `classical_tightness_witness_elliptope`: The all-ones correlators have a PSD completion.
- `turing_point_elliptope`: The correlators (1, 0, 1, 0) have a PSD completion.
- `elliptope_zero`: The zero correlators have a PSD completion.
- `elliptope_convex`: A convex combination of two completable correlator tuples is completable.
- `elliptope_finite_mixture`: A sub-convex finite mixture of completable tuples is completable.
- `lhv_mixture_elliptope`: A finite mixture of deterministic sign strategies with weights summing to one is completable.
- `elliptope_tsirelson`: A completable correlator tuple has CHSH value squared at most 8.
- `pr_box_not_elliptope`: The PR box correlators have no PSD completion.
- `beyond_classical_elliptope`: The tuple (3/5, 3/5, 3/5, -3/5) is completable and has CHSH value above 2.
- `elliptope_check_full_sound`: If the two-branch integer elliptope check passes, the witness-derived correlators are completable.
- `elliptope_ldl_check_sound`: If the LDL certificate check passes, the witness-derived correlators are completable.
- `elliptope_full_gate_never_accepts_pr_box`: The full elliptope check rejects the PR box tally for every completion and certificate input.
- `gate_accepts_all_ones`: The full check accepts the all-ones tally with its certificate.
- `gate_accepts_beyond_classical`: The full check accepts the interior tally.
- `gate_accepts_pythagorean_boundary`: The LDL check accepts the Pythagorean boundary tally with its certificate.
- `gate_accepts_turing_point`: The full check accepts the (1, 0, 1, 0) tally with its certificate.
- `local_S_2_deterministic`: For rational response functions with values 1 or -1, the CHSH combination of the products has absolute value at most 2.
- `deterministic_strategy_chsh_bounded`: For real response functions `A` and `B` with values 1 or -1, `A0 B0 + A0 B1 + A1 B0 - A1 B1` lies between -2 and 2.
- `factorizable_CHSH_classical_bound`: For any factorizable correlator table, `CHSH_from_correlations` lies between -2 and 2.
- `chsh_gap_is_sum_of_squares` (`Kernel.TsirelsonFromAlgebra.chsh_gap_is_sum_of_squares`): For all reals, `4(a^2 + b^2 + c^2 + d^2) - (a + b + c - d)^2` equals the sum of the six squares `(a - b)^2`, `(a - c)^2`, `(a + d)^2`, `(b - c)^2`, `(b + d)^2`, and `(c + d)^2`.
- `tsirelson_bound_abs` (`Kernel.TsirelsonGeneral.tsirelson_bound_abs`): For four reals with `e00^2 + e01^2 <= 1` and `e10^2 + e11^2 <= 1`, the absolute value of `CHSH e00 e01 e10 e11` is at most `sqrt8`.
- `tsirelson_achievable` (`Kernel.TsirelsonGeneral.tsirelson_achievable`): Some four reals meet both row bounds and have `CHSH` exactly `sqrt8`.
- `tsirelson_tight`: Some four reals meet both row bounds and have `CHSH_value` exactly `sqrt 8`.
- `rational_tsirelson_bound` (`Kernel.TsirelsonFromAlgebra.rational_tsirelson_bound`): `sqrt 8 < 5657 / 2000`.
- `psd2_quadratic_form_nonneg`: For reals with `a >= 0`, `d >= 0`, and `a d - b^2 >= 0`, `a u^2 + 2 b u v + d v^2 >= 0` for all `u` and `v`.
- `npa_psd_iff_column_contractive`: For four reals, the zero-marginal NPA 5 by 5 matrix is PSD exactly when the three column-contractivity inequalities hold; symmetry is not part of either side.
- `npa_quad5_test_col0`: The quadratic form of the zero-marginal NPA matrix at the vector with entries `-e00`, `-e10`, and 1 in positions 1, 2, and 3 (0 elsewhere) equals `1 - e00^2 - e10^2`.
- `npa_quad5_test_col1`: The quadratic form at the vector with entries `-e01`, `-e11`, and 1 in positions 1, 2, and 4 equals `1 - e01^2 - e11^2`.
- `npa_quad5_test_schur`: For every real `t`, the quadratic form at the vector with entries `-(e00 t + e01)`, `-(e10 t + e11)`, `t`, and 1 in positions 1 to 4 equals `(1 - e00^2 - e10^2) t^2 - 2 (e00 e01 + e10 e11) t + (1 - e01^2 - e11^2)`.
- `psd_3x3_determinant_nonneg`: For a symmetric PSD 5 by 5 matrix with diagonal entries 1 at indices `i`, `j`, `k`, the correlation determinant `1 - x^2 - y^2 - z^2 + 2xyz` of its `(i, j)`, `(i, k)`, `(j, k)` entries is non-negative.
- `zero_marginal_implies_elliptope`: If the zero-marginal NPA matrix of four correlators is symmetric and PSD, the correlators have a PSD completion.
- `completed_quad_expand`: The quadratic form of the completed NPA matrix with completion entries `x` and `y` expands to the sum of the five squared coordinates plus twice `x`, `y`, and the four correlators times the corresponding coordinate products.
- `elliptope_pd_check_sound`: If the positive-definiteness integer check passes on the witness counts and completion operands, the witness-derived correlators have a PSD completion.
- `q1ab_moment_matrix_symmetric`: The 9 by 9 level-1+AB moment matrix is symmetric for every choice of the four correlators and five higher moments.
- `quad9_q1ab_sos_decomposition`: The quadratic form of the level-1+AB matrix equals three explicit squares plus the defined residual in the six remaining coordinates.
- `q1ab_psd_iff_column_contractive`: The level-1+AB matrix is PSD exactly when its residual is non-negative for all six remaining coordinates (`column_contractive_q1ab`).
- `column_contractive_q1ab_implies_psd9`: Non-negativity of that residual implies the level-1+AB matrix is PSD.
- `psd9_implies_column_contractive_q1ab`: PSD of the level-1+AB matrix implies non-negativity of the residual.
- `column_contractive_q1ab_iff_general_realizable`: Non-negativity of the residual is equivalent to the dimension-generic symmetric-and-PSD predicate for the level-1+AB matrix at size nine.
- `q1ab_residual_g_zero_decomp`: With all five higher moments zero, the residual splits into a two-coordinate part and a four-coordinate part, each a sum of squares minus the squares of the correlator-weighted combinations.
- `column_contractive_check_q1ab_sound_at_g_zero`: If the integer level-1+AB check on witness counts passes, the witness-derived correlators with all five higher moments zero satisfy `column_contractive_q1ab`.
- `q1ab_check_at_gzero_forces_unit_ball`: If that check passes, the squares of the four witness-derived correlators sum to at most 1.
- `q1ab_check_at_gzero_implies_classical_bound`: If that check passes, the absolute CHSH value of the witness-derived correlators is at most 2, so the check with all higher moments zero accepts nothing above the classical bound.
- `q1ab_certifies_a_superclassical_chsh_point`: The correlators (3/5, 3/5, 3/5, -3/5) have CHSH value above 2, and the level-1+AB matrix at those correlators with four higher moments zero and the fifth equal to -1/2 is PSD.
- `q1ab_g5_kernel_check_accepts_superclassical`: The integer check with the fifth moment supplied accepts the witness counts (4, 1), (4, 1), (4, 1), (1, 4) with fifth-moment counts 1 and 3.
- `q1ab_four_body_cells_are_conjugate`: For every choice of parameters, the level-1+AB matrix entry at rows 6 and 7 (counting from 0) is the negative of the entry at rows 5 and 8.
- `q1ab_g12345_minors_witness_implies_psd9`: If the six-variable residual matrix with entries `q12345_H11` to `q12345_H66` meets the positive-pivot predicate `sym6_pd_interior`, the level-1+AB matrix is PSD.
- `q1ab_g12345_caller_witness_z_abs_sound`: For integer correlation and residual numerators and positive denominators, if the integer kernel `q1ab_g12345_check_z_kernel` returns true, the real-valued ratios satisfy `q1ab_g12345_minors_witness`.
- `column_contractive_check_witness_npa_psd`: For any witness tally, if the integer column-contractive check accepts it, the zero-marginal NPA moment matrix built from its four bucket correlations is positive semidefinite.
- `q12345_sym6_qf_equals_residual`: The six-variable quadratic form with entries `q12345_H11` to `q12345_H66` equals the level-1+AB residual.
- `cleared_g12345_H11_Z_bridge`: For integer numerators and positive integer denominators, the integer-cleared `H11` entry, read as a real, equals the integer `g12345_COMMON_Z` of those denominators times `q12345_H11` at the corresponding rational correlators and moments.
- `sym4_LDLT_identity`: For a symmetric 4 by 4 quadratic form, the defined pivots `d1` to `d4` and partial forms `P1`, `Q1`, `Q2` satisfy `d1^2 d2 d3 q = d1 d2 d3 P1^2 + d1 d3 Q1^2 + Q2^2 + d1^2 d2 d4 v4^2`.
- `sym5_Schur_identity`: For a symmetric 5 by 5 quadratic form, `h11` times the form equals the square of the defined first partial form plus the 4 by 4 form of the scaled Schur complement in the last four coordinates.
- `sym5_qf_nonneg_from_pd`: If `h11 > 0` and the four defined pivots of the scaled Schur complement are positive, the symmetric 5 by 5 quadratic form is non-negative.
- `sym6_Schur_identity`: For a symmetric 6 by 6 quadratic form, `h11` times the form equals the square of the defined first partial form plus the 5 by 5 form of the scaled Schur complement in the last five coordinates.
- `sym6_qf_nonneg_from_pd`: If `h11 > 0` and the scaled Schur complement meets the 5 by 5 positive-pivot predicate, the symmetric 6 by 6 quadratic form is non-negative.

## Models from other fields

- `quote_cannot_attest_unmeasured_state`: In the scoped TPM quote-field abstraction, whose quote authenticity is assumed externally rather than modeled, no function of the selected-PCR digest and nonce returns the additional runtime Boolean for every platform.
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

## Trace and projection contracts

- `selected_representatives_give_decoder`: Given a representative for every view whose observation is that view, a query is constant on observation fibers exactly when it factors through a decoder of the view.
- `independent_coordinates_joint_change_costs_one`: On pairs of Booleans, the two coordinates are independent observations, the step from (false, false) to (true, true) raises both, the least cost meeting both unit floors on that step is 1, and the constant cost 1 respects each floor.
- `nat_recursion_theorem`: For the candidate-decider-dependent nat substrate, every transformer selected by its representability predicate has a code whose total run equals the transformer's image on every input state.

## Information and witness contracts

- `compression_priced_trace_floor`: On an enumerated finite state space with permanent certification and compression pricing, an instruction-list run from uncertified to certified costs at least one.
- `priced_reset_satisfies_premises`: The two-state Blank/Stamped machine is finite, keeps its stamp permanently, and prices every merging step at one.
- `step_price_is_exact`: The defined full-state certification-flip indicator price meets the flip floor and never overcharges.
- `locally_consistent_gives_separable_coupling`: A witness tally consistent with the supplied four local deterministic outputs induces a separable setting-outcome coupling.
- `decision_tree_leaves_le_pow2_depth`: A decision tree has at most `2^depth` leaves.
- `decision_tree_log2_up_leaf_bound`: The rounded-up base-2 logarithm of a decision tree's leaf count is at most its depth.

## Replicated-record examples

- `toggle_game_refutes_strong_pointer_necessity`: Consensus, authentic observer views, a positive observer count, and coordinator-free evolution do not imply event permanence, because the two-observer toggle game satisfies those premises and revokes its event.
- `durable_consensus_implies_permanence`: A positive observer count, authentic observer views, and durable true views imply event permanence; durability is the premise that supplies the conclusion.

- `toy_cert_unique_pointer`: In the chosen replicated-ledger toy, the certificate predicate proliferates and the single designated work predicate does not.
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

## Scalar physics and geometry contracts

- `canonical_reset_heat_exact`: In the frozen two-state reset protocol, the bath heat for an energy gap `Delta` is exactly `Delta / 2`.
- `selected_gap_gives_landauer_heat`: Choosing the two-state energy gap to be `2 * k_B * T * ln 2` makes the frozen reset protocol's bath heat exactly `k_B * T * ln 2`.
- `master_equation_does_not_fix_heat_scale`: Two distinct energy gaps obey the same frozen population master equation but transfer different heat, so those population dynamics alone do not determine an energy scale.
- `calibrated_mu_landauer_energy`: For all reals `k_B` and `T`, every state type `S`, every natural-number ledger `mu` on it and every state with `mu s = 1`, `mu_energy_at_scale mu (k_B * T * ln 2) s` equals `k_B * T * ln 2`; the scale is the supplied argument, so this is the arithmetic `mu s * scale`.
- `canonical_reset_satisfies_master_equation`: One step of the discrete two-state master equation, with the protocol's fixed time step and transition rates, carries the frozen initial populations exactly to the frozen final populations.
- `smaller_gap_refutes_unconditional_landauer_floor`: For positive `k_B` and `T`, the frozen reset protocol with energy gap `k_B * T * ln 2` transfers bath heat strictly less than `k_B * T * ln 2`, so the protocol by itself does not enforce a Landauer floor.

- `tsirelson_rational_lower_witness`: Some correlator satisfying the selected rational coherence predicate has CHSH at least 28284/10000.
- `five_labeled_models_have_selected_pointer`: In the five synthetic labelled mirror models, each selected flag is returned by every stipulated observer and its named rival is not.

- `mu_has_no_intrinsic_joule_value`: For every state type and natural-number ledger `mu` on it, two real-valued functions on states exist that give 1 and 2 on every state with `mu` equal to 1, so the counter by itself fixes no energy value.

## Earned commitments in the minimal machine

- `checker_soundness`: From a clean start, every stored fact whose version equals its counter's current version states a true property of that counter's current value.
- `earned_certification_provenance`: Every trace from a clean start ending certified contains a passing CHECK, then a passing COMMIT of the same property and counter at the same version with that counter untouched between them, then a passing CERTIFY.
- `no_forging`: Every trace from a clean start satisfies no_forgery: each stored fact has a passing CHECK as its origin, with the stated untouched-counter condition when its version is current.
- `certified_run_min_cost`: A trace from a clean start ending certified has total cost at least three and raises the ledger by at least three.
- `min_cost_tight`: From every initial counter pair, four execution steps of CHECK at-least-zero, COMMIT of that claim, and CERTIFY halt with certification true and ledger three.
- `run_prog_trapped`: A machine whose trap latch is set takes no further step: any number of program steps leaves its state unchanged.
- `earned_run_check_can_fail`: The program CHECK is-zero on counter A, COMMIT of that claim, CERTIFY, run four steps from (a, b), certifies with ledger exactly three when a is 0, and traps with the flag down when a is not 0.
- `earned_run_refused_forever`: From any start whose counter A is not 0, no number of steps of that program raises the flag.
- `certified_channel_earned`: From a clean start, a trace ending certified leaves the channel naming a fact f, and the trace contains an earlier passing COMMIT whose claim is exactly f.
- `channel_names_last_commit`: The run CHECK and COMMIT of is-zero on A, CERTIFY, then CHECK and COMMIT of is-zero on B, from (0, 0), ends certified with the channel naming the claim about B, not the one the flag rose on.
- `generic_earned_certification_provenance`: For any property language with a Boolean checker proved equivalent to its meaning, every trace from a clean start ending certified contains a passing CHECK, then a passing COMMIT of the same property and counter at the same version with that counter untouched between them, then a passing CERTIFY.
- `generic_checker_soundness`: For any such property language, from a clean start every stored fact whose version equals its counter's current version states a true property of that counter's current value.
- `generic_no_forging`: For any such property language, every trace from a clean start satisfies no_forgery: each stored fact has a passing CHECK as its origin, with the untouched-counter condition when its version is current.
- `generic_certified_run_min_cost`: For any such property language, a trace from a clean start ending certified has total cost at least three.
- `sorted_run_certifies_iff`: With a counter value decoded to a list of naturals, the program CHECK sorted on counter A, COMMIT, CERTIFY, run four steps from (a, b), certifies if and only if the list decoded from a is sorted.
- `sorted_run_certifies`: When the list decoded from a is sorted, that program certifies from (a, b) with ledger exactly three.
- `sorted_run_refused_forever`: When the list decoded from a is not sorted, no number of steps of that program from (a, b) raises the flag.
- `simulation_run`: Starting with the error flag false, any number of steps of a compiled two-counter program projects to the same number of two-counter steps and keeps the error flag false.
- `earned_core_halting_undecidable`: Halting for the minimal earned-commitment machine is undecidable, by reduction from the vendored two-counter halting problem.

- `a2`: Any minimal-machine step turning certification from false to true costs at least one.
- `base_blind`: Projecting an executed step to its core gives exactly the core transition, independently of the ledger and certification flag.
- `cert_latch`: After an instruction, certification is the old flag OR the event fired by that instruction on the core.
- `cert_permanent`: A true certification flag stays true under every instruction.
- `committed_claim_holds` (`Minimal.EarnedCore.committed_claim_holds`): From a clean start, a COMMIT guard that passes names a property true of the selected counter at that moment.
- `earned_commitment_provenance`: A COMMIT guard that passes after a clean-start trace has a prior passing CHECK of the same property and counter version, with that counter untouched between the CHECK and COMMIT.
- `earned_core_floor`: A trace taking the minimal machine from uncertified to certified has total cost at least one, by the abstract certification-system floor.
- `earned_core_honest`: The minimal machine with its program has a certification reading driven by, and permanent over, its projected core base.
- `earned_core_is_latch`: There exists an event on the minimal machine core base whose latch reproduces its certification reading.
- `universal_simulation`: A host that is not trapped, after n guest-step moves with budget 1, holds the guest state that n steps of the guest program reach, with the guest program unchanged and the host still not trapped.
- `universal_program_simulation`: From line 1 and not trapped, 3n steps of the stored host program U leave the guest where n steps of its own program put it.
- `host_thiele_complete`: A two-counter program halts from (1, (a, b)) exactly when the host program made of OWN moves of its compilation halts from a host whose core starts at (a, b), whatever guest the host carries.
- `record_agreement_step`: Every host move keeps the host's mirror equal to the guest's certified flag.
- `record_agreement`: Every host trace keeps the host's mirror equal to the guest's certified flag.
- `record_agreement_program`: Every run of a stored host program keeps the host's mirror equal to the guest's certified flag.
- `hload_agrees`: A freshly loaded host's mirror equals its guest's certified flag.
- `simulated_record`: After n guest steps under the host, the mirror is the guest's certified flag after n steps of its own program.
- `toll_enforced_by_host_step`: When a guest step with budget b takes the guest's flag from down to up, the host's mirror goes from down to up in that same host step, the host's ledger rises by exactly b, and b is at least 1.
- `every_guest_crossing_is_a_host_crossing`: A guest crossing between its steps n and n+1 is the mirror's crossing between host moves n and n+1, which costs 1.
- `host_pays_for_guest`: One host move raises the guest's ledger by no more than it raises the host's.
- `host_cost_covers_guest`: Over every host trace, the host's ledger grows at least as much as the guest's.
- `simulated_cost`: The guest's total cost over n steps is at most the host's total cost over the matching n guest-step moves.
- `no_free_host_certification_step`: If one host move raises the mirror, it is a guest step with budget at least 1 on an untrapped host whose guest's next instruction is CERTIFY, and the guest's flag crossed in that step.
- `no_free_host_certification`: Any host trace that raises the mirror contains a guest step with budget at least 1 in which the guest's flag crossed.
- `no_free_host_certification_program`: Any run of a stored host program that raises the mirror contains such a guest step.
- `guestless_runs_leave_mirror`: A host trace made only of OWN moves leaves the mirror and the guest state unchanged.
- `own_record_only_by_certify`: The host's own flag rises only by an OWN CERTIFY that passes on the host's core.
- `host_own_toll`: A host move that raises the host's own flag costs at least 1.
- `host_mirror_toll`: A host move that raises the mirror costs at least 1.
- `host_toll`: A host move that raises the host's reading, its own flag or the mirror, costs at least 1.
- `host_nfi`: Any host trace that raises the host's reading has total cost at least 1, by the abstract certification-system floor.
- `demo_certifies`: The guest CHECK, COMMIT, CERTIFY, HALT loaded at (0, 0) raises the mirror on the third guest step, with the host's own flag down and 3 paid.
- `demo_program_certifies`: Under the stored host program U the same guest raises the mirror at host step 7, with 3 paid.
- `demo_forgery_fails`: The guest CERTIFY, CERTIFY traps, the mirror stays down after five guest steps, and the host pays 5.
- `hexec_gprog`: No host move changes the stored guest program.
- `host_mirror_earned`: Load the host with guest program P and guest start (x, y) and run any host trace; if the mirror is up, the guest state is the guest program's own run of some number of steps from (x, y), and the instructions it executed contain a passing CHECK, then a passing COMMIT of the same claim at the same version with the counter untouched between, then a passing CERTIFY.
- `eval_iff`: For each property and number, the Boolean checker is true if and only if the arithmetic meaning of the property holds.
- `facts_bounded_step`: A core whose fact list has at most fact_cap entries still meets that bound after any instruction.
- `facts_keep`: Every fact already in the core table remains there after any instruction.
- `facts_step`: Every fact present after a core step was present before, or is exactly the fact written by a passing CHECK in that step.
- `full_table_traps`: If the fact table is full, CHECK sets the error flag and leaves the fact list unchanged.
- `halting_correspondence`: A two-counter program halts from counters a and b if and only if its compiled minimal-machine program halts from the corresponding start.
- `mm2_halting_iff`: The vendored two-counter halting predicate holds exactly when the translated and compiled minimal-machine halting predicate holds.
- `mm2_step_iff`: A vendored two-counter step is equivalent to the translated executable two-counter step returning the same successor.
- `mm2_stop_iff`: The vendored two-counter stopping predicate is equivalent to the translated executable step returning None.
- `mm2_terminates_iff`: Vendored two-counter termination is equivalent to reaching an executable stopping configuration after finitely many translated steps.
- `mu_conservation_trace`: The minimal-machine ledger after a trace equals its initial value plus the sum of instruction costs.
- `nfi_floor`: Any trace taking the minimal-machine flag from false to true has total cost at least one.
- `no_cert_oracle`: No function of the two-counter window recovers the certification flag on every trace from start 0 0.
- `no_commit_oracle`: No function of the two-counter window decides whether COMMIT of counter A being zero would pass on every trace from start 0 0.
- `no_forging_step`: Appending any instruction to a trace preserves its no-forgery property.
- `only_certify_certifies`: A step changing certification from false to true must be CERTIFY with its guard satisfied.
- `program_certified_min_cost`: A program run from a standard start that ends certified has ledger at least three.
- `receipt_separation`: Two concrete traces have the same two-counter window and versions but different ledgers, certification flags, fact tables, and permission to commit counter A being zero.
- `simulation_step`: From an error-free core, translated two-counter stopping agrees with minimal-machine halting, and each two-counter successor is the projected core successor with error still false.
- `sound_step`: Every core instruction preserves the invariant that fact versions do not exceed current versions and current-version facts hold of their counters.
- `uncommitted_certify_traps`: If the certification guard fails, CERTIFY raises the core error flag and leaves the certification flag unchanged.
- `unearned_commit_traps`: If the commitment guard fails, COMMIT raises the error flag and leaves both the channel and fact table unchanged.
- `mu_conservation` (`Minimal.EarnedCore.mu_conservation`): Executing an instruction raises the minimal-machine ledger by exactly that instruction's cost.

## Thiele-complete

- `thiele_complete_is_weak`: Every Thiele-complete machine obeys the toll (a step raising its record costs at least one) and has a universal base, so it is weakly Thiele-complete.
- `base_runs_every_program`: For every machine with a universal base, every two-counter program and every live state, running the program's compiled moves for n steps from that state shows, in the base's window, exactly the configuration the program reaches in n steps, and the state stays live.
- `base_halting_correspondence`: For every machine with a universal base, a two-counter program halts from (1, (a, b)) exactly when running its compiled moves from the loaded state for (a, b) reaches a state whose window line holds no instruction.
- `ledger_counts_record_moves`: Through any interface meeting the exact toll clause, the ledger after a run equals the ledger before it plus the number of CHECK, COMMIT and CERTIFY moves in the run.
- `certificate_costs_three`: Through any interface making a machine Thiele-complete, a run from a clean state that ends with the record up contains at least three record moves and raises the ledger by at least three.
- `check_can_fail`: Through any interface making a machine Thiele-complete, some CHECK of some claim fails at some loaded state, where the claim's meaning is false.
- `some_run_certifies`: Through any interface making a machine Thiele-complete, some run from some loaded clean state ends with the record up.
- `only_certify_raises`: Through any interface making a machine Thiele-complete, on a run from a clean state, a move that takes the record from down to up is a CERTIFY.
- `complete_costs_at_most_one`: Every move of a Thiele-complete machine costs 0 or 1.
- `complete_has_free_move`: Every Thiele-complete machine has a move that costs 0.
- `one_move_record_excluded`: No machine with a move that raises the record from every state is Thiele-complete.
- `never_certifies_excluded`: No machine whose record is down at every state is Thiele-complete.
- `clock_weakly_thiele_complete`: The two-counter machine with every move costing 1 and any reading of its configuration as the record obeys the toll and has a universal base.
- `clock_not_thiele_complete`: The two-counter machine with every move costing 1 and any reading of its configuration as the record is not Thiele-complete.
- `latch_clock_weakly_thiele_complete`: The two-counter machine with every move costing 1 and a flag that latches once any chosen test of the configuration says yes obeys the toll and has a universal base.
- `latch_clock_not_thiele_complete`: The two-counter machine with every move costing 1 and a flag that latches once any chosen test of the configuration says yes is not Thiele-complete.
- `paid_latch_weakly_thiele_complete`: A free two-counter base with a ledger and one move TICK that costs 1 and raises a flag obeys the toll and has a universal base.
- `paid_latch_meets_base_and_toll`: Read with TICK as CERTIFY, that paid latch meets the universal base clause and the exact toll clause.
- `paid_latch_not_thiele_complete`: That paid latch is not Thiele-complete.
- `silent_weakly_thiele_complete`: A free two-counter base whose record never rises obeys the toll and has a universal base.
- `silent_meets_base_record_toll`: That silent machine, with one interface, meets the universal base clause, the earned record clause and the exact toll clause.
- `silent_not_thiele_complete`: That silent machine is not Thiele-complete.
- `earned_core_thiele_complete`: The small machine of EarnedCore.v, read with INC and DEC as base moves, CHECK and COMMIT of a property on a counter as record moves on that claim, CERTIFY as CERTIFY, clean starts as clean states and mu as the ledger, is Thiele-complete.
- `earned_generic_thiele_complete`: The small machine over any property language with an exact claim equality and a checker equivalent to its meaning, in which some property is true of one number and false of another, is Thiele-complete.
- `sorted_machine_thiele_complete`: The small machine whose property says a counter, decoded as a list, is sorted is Thiele-complete.
- `sorted_cs_sound`: For the sorted-list machine read as a certification system, on any run from a clean start, if the table holds the fact that a counter is sorted at that counter's current version, the list decoded from the counter's value is sorted.
- `thiele_complete_floor`: For every Thiele-complete machine, read as the certification system `complete_cs`, a trace from a state with the record down to a state with it up has total cost at least one.
- `earned_complete_agrees`: The certification system built from the small machine's Thiele-completeness reaches the same state and charges the same total cost as `earned_cs` on every trace from every state.
- `generic_complete_agrees`: For every property language, any certification system built from a proof that the generic small machine is Thiele-complete reaches the same state and charges the same total cost as `generic_cs` on every trace from every state.
- `thiele_complete_hides`: Every Thiele-complete machine has an interface making it Thiele-complete through which no function of the base window gives the ledger, and none gives the record, at the end of every run from every loaded state.

## The window of a Thiele-complete machine

- `complete_every_window_printed`: For every machine and every interface making it Thiele-complete, and every state s, there is a loaded clean start and one base move of cost 0 from it that ends in a state with the same base window (pc, (A, B)) as s, the record down, and the ledger unchanged from the start.
- `complete_hides_ledger`: For every machine and every interface making it Thiele-complete, there is a loaded clean start and two runs from it that end with the same base window, with different ledgers, the first at least 3 above the second.
- `complete_two_runs`: For every machine and every interface making it Thiele-complete, there is a loaded clean start and two runs from it, the second made of base moves only, that end with the same base window; the first ends certified with its ledger at least 3 above the start, and the second ends uncertified with its ledger unchanged.
- `complete_hides_record`: For every machine and every interface making it Thiele-complete, there is a loaded clean start and two runs from it that end with the same base window, the record up after the first and down after the second.
- `complete_no_ledger_oracle`: For every machine and every interface making it Thiele-complete, no function from base windows to numbers gives the interface's ledger at the end of every run from every loaded start.
- `complete_no_record_oracle`: For every machine and every interface making it Thiele-complete, no function from base windows to Booleans gives the record at the end of every run from every loaded start.
- `complete_cs_window_blind`: For every Thiele-complete machine and every interface making it Thiele-complete, on the CertificationSystem `complete_cs` built from the machine, no function of the base window of the state a trace reaches from a loaded start gives that state's reading, and none gives the interface's ledger there.

## The universal interpreter

- `U_simulation`: For every small-machine program P, start (x, y) and guest step count m, there is a host step count n such that, after m guest steps from (x, y) and n steps of the fixed host program U from the loaded host `hload P x y`, either the simulation relation `rel` holds with m at most n (the host is at U's head with its registers A and B, the guest program counter, the trap latch, the ledger, the flag, the fact table and the channel matching the guest's) or both machines have stopped and the halting relation `rel_halt` holds.
- `hload_rel`: For every small-machine program P and start (x, y), the loaded host `hload P x y` stands in the simulation relation to the guest start (x, y), with no slot records and an empty channel.
- `U_paid_sites`: The instructions of the fixed host program U that cost 1 are exactly the listed paid sites: one CHECK on each slot and one on the dead register for each guest counter, one COMMIT on each slot and one on the dead register for each guest counter, and one CERTIFY, 69 in all.
- `U_step`: If `rel` holds between a guest state and a host state, then either the guest has halted and some host state reachable from the host stands in `rel_halt` with it, or the guest has not halted and some positive number of steps of U reach a host state that stands in `rel` with the guest's next state or, when that guest step traps, in `rel_halt` with it.
- `universal_halting`: For every small-machine program P and start (x, y), the guest's run of P from (x, y) halts at some step if and only if the fixed program U run from `hload P x y` halts at some step.
- `universal_output`: If the guest's run of P from (x, y) has halted at step m and U's run from `hload P x y` has halted at step n, the host's registers A and B hold the guest's counters A and B, and the host's trap latch, ledger and certified flag equal the guest's.
- `universal_flag_iff`: For every P and (x, y), the guest's certified flag is up at some step of its run if and only if the host's certified flag is up at some step of U's run from `hload P x y`.
- `universal_ledger_exact`: For every P and (x, y), each guest step count m has a host step count n at which `rel` (with m at most n) or `rel_halt` holds and the host ledger equals the guest ledger, and each host step count n has a guest step count m such that the host ledger at n lies between the guest ledger at m and the guest ledger at m + 1.
- `universal_earned`: If the host flag is up after n steps of U from `hload P x y`, the instructions U executed contain a passing CHECK PSlot on a slot register SLOT c k with k below 16, then, with that slot untouched and its version unchanged, a passing COMMIT PSlot on the same slot, then the passing CERTIFY; the slot held `pair (pcode p) v` at the CHECK with the guest property p true of v; and the guest's own run from (x, y) contains a passing CHECK p c, then, with counter c untouched, a passing COMMIT p c, then a passing CERTIFY, with counter c holding v at its CHECK.
- `U_run_on_host_machine`: For every P, (x, y) and n, running `host_machine` (the machine of EarnedMulti.v with the property PSlot, one move per instruction) on the instructions U executes in n steps from `hload P x y` gives exactly U's state after n steps.
- `universal_thiele_complete`: The machine of EarnedMulti.v with the single property PSlot, read as a machine of ThieleComplete.v with one move per instruction, satisfies `thiele_complete`.
- `pigeonhole_not_injective`: For any type, any finite list Q of its elements and any function f from the naturals whose every value lies in Q, f is not injective.
- `pigeonhole_collision`: For any type with decidable equality, any finite list Q and any function f from the naturals whose every value lies in Q, there are two different naturals n and m with f n = f m.
- `no_exact_copy_host`: For any host property language with an exact claim equality and any host checker, and any translation of guest properties into a finite list of host properties whose host check passes whenever the guest check passes on the same number, there are n different from m with `PGe n` different from `PGe m` and the same translation, such that the guest program CHECK (PGe n) A; COMMIT (PGe m) A traps within two steps from every start, and for every a at least n, every untrapped host state with fewer than 16 facts whose register R holds a, and every b, the guest's first step from (a, b) passes, its second traps, and the host's translated CHECK, COMMIT on R ends untrapped with the channel naming the committed claim at R's version.
- `multi_cs_floor`: For any property language, claim equality and checker, a trace of the machine of EarnedMulti.v from a state with the flag down to a state with the flag up has total cost at least one, by `universal_nfi_any_substrate` on the record `multi_cs`.
- `interp_cs_runs_U`: For every P, (x, y) and n, running the record `interp_cs` (the machine of EarnedMulti.v with PSlot) on the instructions U executes in n steps from `hload P x y` gives U's state after n steps.
- `interp_U_certified_floor`: If the host flag is up after n steps of U from `hload P x y`, the instructions U executed have total cost at least three on `interp_cs`.
- `interp_halting_iff`: For every P and (x, y), the small machine's halting predicate `EARNED_HALTING` holds of (P, x, y) exactly when U halts at some step from `hload P x y`.
- `interp_halting_undecidable`: The halting predicate of the one fixed program U on loaded triples (P, x, y) is undecidable in the vendored library's synthetic sense, by reduction from the small machine's halting problem of `earned_core_halting_undecidable`.
- `interp_complete_agrees`: For every host trace and host state, the record `complete_cs` built from `universal_thiele_complete` reaches the same state and charges the same total cost as `interp_cs`.
- `interp_U_complete_floor`: If the host flag is up after n steps of U from `hload P x y`, the instructions U executed have total cost at least one on the record `complete_cs` built from `universal_thiele_complete`, by `thiele_complete_floor`.
- `multi_cs_no_exact_copy`: For any host property language with an exact claim equality and any checker, and any translation of guest properties into a finite list of host properties whose host check passes whenever the guest check passes on the same number, there are n different from m with the same translation of `PGe n` and `PGe m` such that the guest program CHECK (PGe n) A; COMMIT (PGe m) A traps within two steps from every start, while on the record `multi_cs` the translated CHECK, COMMIT on a register holding a value a at least n, from any untrapped state with fewer than 16 facts, ends untrapped with the channel naming the committed claim at that register's version.

