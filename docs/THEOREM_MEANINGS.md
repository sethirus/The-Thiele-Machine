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
- `abstract_nfi`: In an `AbstractCertMachine`, a trace that starts uncertified and ends certified contains an instruction in the cert-setter class.
- `cert_addr_setter_cost_pos`: Every VM instruction in the cert-setter class costs at least one.
- `no_free_certification`: A single VM step that moves `csr_cert_addr` from zero to nonzero has instruction cost at least one.
- `no_free_certification_certified`: A single VM step that switches `vm_certified` from false to true has instruction cost at least one.
- `certification_requires_positive_mu`: A single VM step that switches on either certification channel raises `vm_mu` by at least one.
- `F3_plus_one_renaming_unification`: For every `cost`, `instruction_cost (instr_certify cost)` equals `S cost`, that is, `cost + 1`; the statement is this equation for `instr_certify` and says nothing about deriving the `+1`.
- `thiele_represents_simulating_cert_system`: For a certification system supplied together with an embedding and decoding into the VM, a trace that certifies in the source costs at least one there, and its decoded VM run ends with `vm_certified` true.
- `honest_cost_tracking_strict_restriction`: Some cost-bearing system certifies at total cost zero, while every `CertificationSystem` needs cost at least one; the cost rule is what separates them.
- `commitment_cost_not_reducible_to_erasure_cost`: Some trusted erasure-accounting system certifies at total cost zero with no erasure reported, while every `CertificationSystem` needs cost at least one.
- `level_k_certification_cost_floor`: A trace from the initial state that executes a `CERTIFY` whose charge is at least `k` has total mu cost at least `k`.
- `mu_hierarchy_theorem`: For every `k` at least one, some trace certified at level `k` costs exactly `k`, and every trace certified at level `k` costs at least `k`.
- `mu_hierarchy_no_upper_bound`: For every budget, some certification level cannot be reached within it.
- `level_k_verification_floor`: A proof script that certifies `k` claims costs at least `k` mu (the level-k floor restated for the proof-carrying model).
- `level_k_verification_floor_tight`: For every `k` at least one, some proof script certifies `k` claims at cost exactly `k`.

## Pricing the event

- `exact_commitment_pricing_characterization`: In a `LocalPredicatePricedSystem`, a charge meets the certification floor and never overcharges exactly when it charges on the certification flips and nowhere else, one unit each.
- `substitution_test_rejects_non_a2_exact_substitute`: A charging predicate that differs from the certification-flip predicate cannot both meet the floor and never overcharge.
- `a2_equal_trust_substitution_payoff`: A conjunction of the pricing characterizations: floors hold exactly when the charge covers the flips, exact pricing holds exactly when the charge is the flip predicate at unit price, total cost splits as base plus flip count exactly when the charge is the flip predicate, and the VM's certified channel has that split.
- `joint_floor_is_least`: A cost meets every event floor in a finite family exactly when it is at least the joint floor, which is one when any event fires and zero otherwise.
- `calibrated_model_exists_iff_positive_cost`: A calibrated positive model exists exactly when every eligible operation costs at least one.
- `gas_schedule_exactness`: A gas schedule meets the commitment floor and never overcharges exactly when it charges the commitment predicate at unit price.
- `thiele_vm_commit_pricing_is_exact`: The VM's commitment-pricing schedule meets the floor and never overcharges.
- `thiele_unit_price_lower_bounds_mu`: Where the VM's commitment pricer charges, its unit charge is at most the instruction's full cost.
- `overcharge_breaks_exactness`: A gas schedule that charges a step that does not flip certification violates no-overcharge.
- `undercharged_opcode_admits_free_commitment`: A gas schedule that does not charge a certifying step lets that one-step trace certify at cost zero.
- `nothing_at_stake_is_free_forgery`: The finality gadget whose finalize step carries zero stake cannot satisfy the certification cost rule.
- `slashing_finality_floor`: In the slashing gadget, where finalizing carries at least one unit of stake, a run from unfinalized to finalized carries total stake at least one.

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
- `history_core_equiv_thiele`: Under `core_equiv`, the history-carrying core and the Thiele core cover each other's initial states and agree after every related step on certification, next-step cost, and the relation obtained by forgetting retained history.
- `billed_core_adequate`: The CPU-billed Thiele core, whose ledger is the VM ledger plus a step counter so every step costs one more, meets all four conditions of `Adequate`.
- `billed_core_honest_extension`: The same billed core meets the conditions of `HonestVMExtension`, with dropping the counter as the computational cover.
- `adequate_core_uniqueness_refuted`: The conjecture `adequate_core_uniqueness` is false: the billed core is adequate but its core is not `core_equiv` to the Thiele core, because a Thiele state with an empty program prices every step at zero and every billed step costs at least one.
- `honest_vm_extension_uniqueness_refuted`: The conjecture `honest_vm_extension_uniqueness` is false for the same reason: the billed core is an honest VM extension whose core is not `observed_core_equiv` to the Thiele core.
- `cert_record_schedule_uniqueness_holds`: Every machine with a cover onto the Thiele core, whose record is the Thiele certification reading through that cover and whose ledger is monotone and satisfies A2, is related to the Thiele core, through that cover, by a relation that preserves the record light and halting and steps to related states; charges are not compared.
- `billed_core_equiv_mod_schedule`: The CPU-billed Thiele core is the same machine as the Thiele core modulo its price schedule, through the cover that drops its step counter.
- `surcharged_core_equiv_mod_schedule`: For every surcharge function on Thiele states, the Thiele core that adds that surcharge to its ledger at each step is the same machine as the Thiele core modulo its price schedule.
- `tied_record_schedule_uniqueness_refuted`: Requiring only that the record be some reading of the computation is not enough: the Thiele core whose record is "the meter has passed one" meets that condition and disagrees with the certification light at a starting state with a positive meter and no certificate.
- `record_axis_is_latch_holds`: For any base machine and any record-carrying machine that covers it step for step, whose record never switches off, satisfies A2 with a monotone ledger, is written by some reachable step, and has its next value determined by the base state and its current value, there is a base event h such that the base state and record evolve exactly as the latch "switch on where h holds, never switch off."
- `record_axis_is_latch_on_tm_holds`: The record axis is a latch on the executable toy Turing-machine base for every program.
- `record_axis_is_latch_on_vm_holds`: The record axis is a latch on the unbounded VM base for every program.
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
- `vm_bare_observable_collision`: The VM has a certifying and a non-certifying step that look the same through `bare_observable`.
- `vm_bare_shadow_cannot_price_exactly`: No price computed from `bare_observable` prices VM certification exactly.
- `vm_forget_collision`: The VM has such a pair through the four-field `forget` window.
- `vm_forget_shadow_cannot_price_exactly`: No price computed from `forget` prices VM certification exactly.
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
- `vm_runs_finite_machine`: Read through program counter modulo four and the certification flag, one VM step of `CERTIFY 0`, `JUMP a 2`, or `CHECKPOINT "" 0` equals the finite machine's step.
- `vm_pays_finite_price`: Each of those VM steps raises `vm_mu` by exactly the finite machine's price.
- `vm_runs_finite_trace`: For a whole run of those instructions, the window follows the finite machine and `vm_mu` rises by the summed price.
- `vm_fragment_certification_paid`: A run of those instructions from an uncertified state to a certified one raises `vm_mu` by at least one.
- `vm_certify_merges`: `CERTIFY d` is not injective on VM states.
- `vm_certifying_step_is_priced_merge`: Every VM step that switches `vm_certified` on is not injective and costs at least one.
- `vm_jump_is_free_merge`: `JUMP 0 0` is not injective and costs zero.
- `vm_prices_certifying_merge_leaves_others_free`: Certifying VM steps are priced merges, some merge costs zero, and so the VM does not price every merge.

## Narrowing: what is priced and what is free

- `run_narrowing_priced_log`: For a finite deterministic machine whose costs meet the squeeze price, a program run from any duplicate-free set `D` of starting states satisfies `log2_up|D| <= cost(t) + log2_up|D'|`, where `D'` is the set of states the run can end in.
- `demon_machine_spread_kept`: In the two-bit measuring machine, the measuring step from the two blank-display states can still end in two different states.
- `wipe_costs_at_least_one`: In the two-bit measuring machine, every cost that meets the squeeze price charges the display wipe at least one.
- `vm_observer_narrowing_at_zero_cost`: Two reachable VM states that differ only in register 1 show the same register 2; after `XOR_ADD 2 1 0` at cost zero they show different register 2 values, and mu stays zero.
- `observer_narrowing_can_be_free`: A particular squeeze-priced cost assigns zero to the injective measuring step of a two-bit machine even though an observer's candidates shrink; the lower-bound pricing rule does not prevent another admissible cost from overcharging that step.
- `demon_refutes_incremental`: In the two-bit measuring machine, the drop in the rounded logarithm of the observer's candidate list from the empty trace to the one-step measuring trace exceeds the trace cost, which is zero.
- `free_incremental_narrowing_with_three`: A three-state cyclic machine with zero costs meets the squeeze price, and a zero-cost trace strictly shrinks the observer's candidate list relative to the empty trace.
- `no_free_incremental_narrowing_below_three`: For every n at most two, no finite machine with exactly n states, squeeze-priced and running a zero-cost trace, leaves the observer with strictly fewer candidates than after the empty trace; with two states or fewer the window is constant on every state once two starting states look alike.
- `structural_entitlement_representation`: Given a strict narrowing of a finite prior list, a distinguishing observation, an uncertified start, a certified posterior, a decision tree whose depth the trace's cert-setter count bounds, a nonempty posterior, and a representative reduction, the posterior predicate is strictly stronger, the trace contains a structure-addition event, and the drop in rounded list size is at most the trace's mu increase.
- `every_sound_structural_shortcut_lands_here`: Every `SoundStructuralShortcut` record yields those three conclusions.
- `sound_shortcut_from_components`: The same premises assemble a `SoundStructuralShortcut` record.
- `factored_n1_shortcut_lands_in_representation`: The concrete n = 1 factored-search shortcut yields those three conclusions.
- `fibered_reduction_implies_tree_cover`: A fibered feasible-set reduction for a tree implies the tree covers the reduction.
- `lassert_cost_from_component_floors`: A cost at least the state term and at least the description term is at least the LASSERT cost formula, which is their sum.
- `lassert_cost_is_its_formula`: The LASSERT cost formula equals its two terms added, and any total at least that sum is at least the formula; both halves hold by unfolding.
- `lassert_honest_cost`: A non-trapping LASSERT step declared a formula length equal to the length in the formula's memory header.
- `lassert_honest_mu_cost`: A non-trapping LASSERT step raises `vm_mu` by eight times the header length plus the successor of its declared cost.
- `non_adaptive_sat_lower_bound`: A correct non-adaptive decider for the stated n-variable family probes at least `2^n` distinct positions.
- `free_world_honesty_verifier_must_inspect_every_cert_position`: A positional verifier that is correct on the supplied length-`n` trace family and decides from inspected positions only must inspect every position below `n`.
- `advantage_factor_unbounded`: For every natural `k` at least 1, some `N` at least 2 has `N * N >= k * (2 * N)`.
- `iteration_savings_dwarfs_mu_cost`: For every natural `N` at least 6, `N * N > 2 * N + 18`.
- `time_tax_theorem_conditional`: For naturals `N` at least 2 and `lambda`, given a state whose register 15 holds `N * N` with `vm_mu` 0, a state whose register 15 holds `2 * N` with `vm_mu` 18, and `2 * N + 2 * lambda < N * N`, the conclusion is `2 * N + 2 * lambda < N * N + 0 * lambda`, the fourth premise with `N * N + 0 * lambda` in place of `N * N`.
- `sighted_program_total_cost_is_eighteen`: For any two target values, summing `instruction_cost` over the instruction list `sighted_program left_target right_target` gives 18; this is a static sum over the listed instructions, not a run.
- `sighted_halts_in_two_n`: Running `sighted_program 0 0` from `init_state` with fuel 20 leaves register 15 equal to 2, `vm_mu` equal to 18, and the program counter at or past the program length; this is one fixed run.
- `receipt_list_eqb_spec`: For two instruction lists, `receipt_list_eqb` returns true exactly when the lists are equal.
- `sighted_n1_supra_posterior_nonempty`: The fixed posterior `sighted_n1_supra_posterior` (a one-state list) has `feasible_size` greater than 0.
- `sighted_n1_supra_representatives`: For the fixed instance (observation function constantly the empty trace, decision tree `dt_branch dt_leaf dt_leaf`, prior `[init_state; sighted_n1_supra_final]`, posterior `[sighted_n1_supra_final]`), `PosteriorRepresentativeReduction` holds: some fiber assignment gives each prior state an observation-equivalent posterior state whose fiber contains it, the prior size is at most the sum of the fiber sizes, and each fiber is at most the tree's leaf count.

## The ledger

- `run_writer_is_run_and_cost`: Running a trace in the writer monad over the natural numbers returns the state the trace reaches and the trace's total cost.
- `a2_iff_nonnegative_amortized_cost`: For any step function, cost, and yes/no reading, A2 holds exactly when every step's cost plus the change in the potential "one if uncertified, zero otherwise" is non-negative.
- `nfi_by_potential`: Under A2, a trace from an uncertified state to a certified one costs at least one, by the potential method's telescoping bound.
- `certification_system_is_potential_method`: Every `CertificationSystem` has non-negative amortized cost under the certification potential.
- `run_graded_is_run`: With costs indexed by instruction, running a trace as a computation graded by the trace's total cost gives the same final state as running it.
- `a2_and_aara_iff_exact`: For any step function, state-dependent cost, and yes/no reading, A2 together with the AARA inequality for the potential "one if uncertified, zero otherwise" holds exactly when certifying steps cost one, all other steps cost zero, and no step switches the reading off.
- `flips_le_cost`: Under A2, the number of false-to-true switches of the reading along any trace is at most the trace's total cost.

- `vm_apply_mu` (`Kernel.MuLedgerConservation.vm_apply_mu`): One VM step raises `vm_mu` by exactly the instruction's cost.
- `mu_is_initial_monotone` (`Kernel.MuInitiality.mu_is_initial_monotone`): A measure that is zero at the initial state and rises by the kernel's instruction cost on every step equals `vm_mu` on every reachable state.
- `instruction_consistent_measure_equals_mu` (`Kernel.MuInitiality.instruction_consistent_measure_equals_mu`): A measure that is zero at the initial state and rises by the instruction cost on every step equals `vm_mu` on every reachable state.
- `mu_is_universal` (`Kernel.MuInitiality.mu_is_universal`): Every `CostFunctional` record equals `vm_mu` on every reachable state.
- `bounded_run_mu_decomposition`: For any two functions `mu_blind_component` and `mu_sighted_component` from instructions to naturals whose sum equals `instruction_cost` on every instruction (the premise `mu_component_split`), and any fuel, trace, and state, `vm_mu` after `run_vm fuel trace s` equals `vm_mu s` plus the sum of the first component over the executed instructions plus the sum of the second.
- `total_irreversible_bits_le_cost`: The number of positively charged instructions in a list is at most the list's total cost.
- `zero_cost_vm_jump_has_injective_history_lift`: `JUMP 1 0` costs zero, moves the program counter to one, and becomes injective once each state carries its history.
- `F1_physical_premises_incompatible`: No dissipation function both charges every step that collapses a Boolean macro-property and matches the VM cost schedule.
- `full_vm_f1_premises_incompatible`: The same statement, kept as a regression check.

## What a window loses

- `shadow_proj_kernel_is_eq_on_classical_shadow`: Two VM states have the same six-field shadow exactly when they agree on those six fields.
- `shadow_strictly_lossy`: Two VM states share a six-field shadow, differ in their morphism lists, and still differ after some probe instruction.
- `probe_preserves_graph_A`: The graph-preserving probe leaves the first separation witness's graph unchanged.
- `probe_preserves_graph_B`: The same for the second witness.
- `categorical_separation` (`Kernel.PartitionSeparation.PartitionSeparation.categorical_separation`): Two VM states agree on registers, memory, mu, program counter, error flag, and certification, and have different morphism lists.
- `degenerate_projection_theorem`: The Turing lift runs a Turing machine exactly; shadow equality is agreement on the six fields; classical programs from states agreeing on the shadow, graph, and CSRs end with equal shadows; and some distinct states share a shadow.
- `D2_classical_shadow_preserved`: A classical program run from two states that agree on the shadow, graph, and CSRs ends with equal shadows.
- `D5_thiele_strictly_extends_classical`: Classical programs leave the graph, `csr_cert_addr`, and certification unchanged, both as instruction lists and under the program-counter runner `run_vm` for any fuel; and from every state a classical run reaches from `init_state`, PNEW of address 0 is a step to a state whose graph differs from the graph of every state a classical run reaches from `init_state`.
- `thiele_simulates_turing`: Lifting a Turing configuration and running the file-local Thiele model for `n` steps gives the Turing machine's configuration after `n` steps.
- `thiele_simulates_turing_gen`: For every fuel, transition table `delta`, and Thiele configuration `tc`, the Turing configuration inside `thiele_run fuel delta tc` equals `tm_run fuel delta` applied to the Turing configuration inside `tc`, whatever the `th_mu` value of `tc`.
- `thiele_strictly_extends_turing`: Two conjuncts about the `ProperSubsumption.v` Turing and Thiele step functions: every Turing computation `TM_computes delta c_init c_final` has a Thiele computation from `lift_config c_init` with some cost whose final Turing configuration is `c_final`; and for every fuel, table, and configuration, the `cc_witness` of `thiele_cost_certificate` (the `th_mu` increase, by natural subtraction) is at most its `cc_bound`, which is `fuel * (step_cost + 1)`.
- `cert_not_function_of_forget`: No function of the four-field `forget` window returns `vm_certified` on every VM state.
- `mu_not_function_of_bare_observable`: No function of `bare_observable` returns `vm_mu` on every VM state.
- `cert_addr_not_function_of_forget`: No function of `forget` returns `csr_cert_addr` on every VM state.
- `no_classical_a2_cert_predicate`: Every Boolean function of `forget` disagrees with `vm_certified` on some VM state.
- `no_classical_mu_separation_predicate`: Every function of `bare_observable` disagrees with `vm_mu` on some VM state.
- `no_classical_cert_addr_predicate`: Every function of `forget` disagrees with `csr_cert_addr` on some VM state.
- `fiber_has_two_preimages`: Every four-field snapshot is the `forget` image of two different VM states.
- `decoding_requires_fiber_constancy`: If some decoder of an observation returns a query on every state, the query is constant on each set of states with the same observation.
- `mu_ledger_mutual_independence` (`Kernel.NecessityAbstract.mu_ledger_mutual_independence`): Neither mu nor certification is a function of the strict classical shadow, certification is not a function of the cost-annotated shadow, and mu is not a function of the certification-annotated shadow.
- `P_full_complete_neither_mu_nor_cert_droppable` (`Kernel.NecessityAbstract.P_full_complete_neither_mu_nor_cert_droppable`): The full projection determines mu and certification, and any projection that forgets one of them cannot determine it.
- `mu_ledger_full_pairwise_independence`: Four non-existence results: no function of `P_full_strict` (memory, registers, program counter, graph) returns `vm_mu`; none returns `vm_certified`; no function of `P_full_cost` (which adds `vm_mu`) returns `vm_certified`; and no function of `P_full_cert` (which adds `vm_certified`) returns `vm_mu`.
- `structural_shortcut_not_function_of_classical`: No function of `forget` returns whether `csr_cert_addr` is nonzero on every VM state.
- `structural_axis_invisible_to_classical`: The same statement, quantified over every decoder.
- `structural_axis_survives_any_classical_oracle`: No decoder reading `forget` and any oracle answer computed from `forget` returns that bit on every VM state.
- `structural_axis_survives_halting_oracle`: The same, with the oracle a Boolean function of `forget` such as a halting bit.
- `axes_mutually_independent`: The structural bit is not a function of `forget`, and the program counter is not a function of the structural-only projection.
- `structural_membership_decidable`: Whether `csr_cert_addr` is nonzero is decidable from the full VM state.
- `bare_setting_no_sound_complete_verifier`: No verifier reading bare classical transcripts is both sound and complete for the claim `vm_mu = 1`.
- `V_does_not_factor_through_classical`: For any transcript type whose two transcripts explain the collision witnesses and share a bare projection, no verifier that is sound and complete for `vm_mu = 1` factors through that projection.
- `substrate_escape_succeeds`: A unit-cost verifier that reads the full state is sound and complete for `vm_mu = 1`.
- `ReceiptTheorem`: No function of the strict classical shadow recovers `vm_mu` for every VM state.
- `commitment_contract_verifier`: Given a contract that the commitment bit exactly reports whether each explaining state has `vm_mu = 1`, reading that bit gives a sound and complete verifier with abstract unit cost; no cryptographic security or runtime bound is proved.
- `honest_commitments_satisfy_contract`: The commitment-bit contract holds when the bit equals whether `vm_mu = 1`.
- `unchecked_bit_violates_contract`: The exact commitment-bit contract fails when the bit can be set independently of the claim.
- `interactive_escape_succeeds`: A unit-cost verifier that reads the prover's reported mu is sound and complete for `vm_mu = 1` under the interactive explanation relation.
- `attestation_cannot_factor_through_bare_transcript`: A sound and complete attestation verifier cannot factor through the report's bare transcript.
- `replay_is_a_two_preimage_witness`: Two attestation reports have the same bare projection, different measurements, and explain the two collision witnesses.
- `measurement_enriched_attestation_succeeds`: A unit-cost verifier reading the measurement is a sound and complete attestation verifier.
- `abstract_log_bit_verifier`: Under an exact disclosure contract, reading the abstract inclusion-verdict bit gives a sound and complete unit-cost verifier for `vm_mu = 1`.
- `abstract_bare_verifier_impossible`: No bare verifier is both sound and complete for `vm_mu = 1` over the named collision relation.
- `abstract_mu_collision_witness`: Two VM states share a strict shadow and a transcript, and one satisfies `vm_mu = 1` while the other does not; this is not an RFC split view.
- `proof_rounds_escape`: A unit-cost check of the proof-carrying transcript is sound and complete for `vm_mu = 1`.
- `bare_pcc_impossible`: No check of bare transcripts is sound and complete for `vm_mu = 1` over the collision relation.

## Traces, states, and uniqueness

- `thiele_trace_fold_initial`: For any `CertCostMachine` and start state, folding its step over instruction lists is the only map from lists that sends the empty list to the start and extends one step per instruction.
- `thiele_morphism_unique_on_reachable`: Two certification-cost morphisms out of the VM that agree at the initial state agree on every state reached by a trace.
- `trace_descent_unique_value_iff`: Instruction lists with the same VM outcome always reach the same target state exactly when each VM outcome has a unique descended target value.
- `reachable_simulation_exists_iff`: Given a representative trace for each reachable state, a certification-preserving reachable simulation exists exactly when traces are fiber-compatible and certification-compatible.
- `certification_agreement_does_not_imply_descent`: The history-keeping target agrees with the VM on certification and still maps two traces with the same VM outcome to different states.

## Diagonal and undecidability

- `g_decode_guest_code_roundtrip`: Encoding a guest-fragment program as a natural number and decoding that number returns the original guest program.
- `g_eval_is_actual_vm_execution`: For a well-formed guest-fragment program, the fuel-bounded evaluator on its numeric code and input equals the state produced by the actual unbounded-VM runner, for every ambient state and tail.
- `g_smn`: Prefixing a guest-fragment program with a constant-input load and relocating its body preserves its terminal guest behavior at that fixed input, independently of the specialized program's external input.

- `structural_shortcut_undecidable`: For any substrate with a shortcut predicate, no decider whose diagonal flip is representable in the substrate decides the predicate.
- `nat_structural_shortcut_undecidable`: For each candidate `d`, the nat substrate built from `d` has no decider with a representable flip for its predicate.
- `nat_self_undecidable`: Each candidate `d` fails to decide the predicate of the substrate built from it.
- `vm_structural_shortcut_undecidable`: Given a round-trip code, a representability class, and a fixed-point premise for bounded `vm_run`, no decider whose flip is in the class decides the bounded shortcut predicate.
- `vm_structural_shortcut_undecidable_encoded`: The same with the round-trip code proved rather than assumed.
- `Q_spec`: In the L lambda calculus, the quote combinator maps the code of any term to the code of its code.
- `second_recursion`: In L, every closed value `s` has a closed term `t` that reduces to `s` applied to the code of `t`.
- `L_recursion_theorem`: In L, every transformer that some closed L value computes on codes has a program equivalent to its image.
- `L_rice`: In L, no closed term decides, from programs' codes, a property that depends only on the values programs reach and that holds for one closed program and fails for another.
- `L_structural_shortcut_undecidable`: In L, no Boolean decider for such a property has an L-computable flip.
- `L_halting_undecidable`: No closed L term decides, from programs' codes, whether an L program reaches a value.
- `star_value_confluent`: In the calculus L of `LRecursion.v`, if `s` reduces to `t` and to `v` in zero or more steps and `v` is a value (a lambda), then `t` reduces to `v` in zero or more steps.
- `vm_bounded_shortcut_decide_correct`: A computable Boolean function decides the bounded shortcut predicate.
- `vm_bounded_decider_flip_not_representable`: That decider's flip lies outside every class that satisfies the bounded fixed-point premise.
- `nat_to_program_program_to_nat`: Decoding the natural-number code of an instruction list returns the list.
- `vm_apply_logic_acc_commutes`: Every VM step commutes with replacing `vm_logic_acc`.
- `run_vm_logic_acc_commutes`: Every fuel-bounded VM run commutes with replacing `vm_logic_acc`.
- `no_logic_acc_encoded_interpreter`: No fixed VM program, observed through an output that ignores `vm_logic_acc`, reproduces every program's final certification bit from the program's code stored in `vm_logic_acc`.
- `vm_halts_at_deterministic`: The unbounded halting relation has at most one final state.
- `cm2_uniform_interpreter_simulation_total`: Each successful two-counter guest step is matched by a positive number of host steps that preserve the representation.
- `cm2_uniform_interpreter_raw_correct_total`: A two-counter guest halts with a final configuration exactly when the host run produces it.
- `cm2_uniform_interpreter_raw_never_malformed`: The host never reports malformed input on a canonical encoding.
- `cm2_uniform_interpreter_divergence_total`: The guest diverges exactly when the host never reaches its end.
- `mm2_termination_guest_iff`: An MM2 program terminates exactly when its translated guest halts.
- `mm2_halting_host_iff`: MM2 halting is equivalent to the fixed host halting on the encoded input.
- `actual_unbounded_host_synthetic_undecidability`: For any ambient state, host halting is undecidable in the Undecidability Library's synthetic sense.
- `g_step_is_vm_apply_u`: A well-formed guest instruction's step equals the unbounded VM step on its denotation.
- `g_width_fits`: The chosen width represents every instruction of the guest program.
- `self_interpreter_complete`: If the well-formed guest reaches a terminal configuration, the fixed host reaches its end with that configuration represented.
- `self_interpreter_sound`: If the host reaches its end, the guest reached a terminal configuration and the host represents it.
- `self_interpreter_correct`: Guest termination at a configuration is equivalent to the host reaching its end with that configuration represented.
- `self_interpreter_divergence`: The guest never terminates exactly when the host never reaches its end.
- `self_interpreter_malformed`: On a fetched word in the malformed range, the host reaches its end with status 2 and the guest registers unchanged.
- `self_rice`: An extensional guest-program property that holds of some well-formed program and fails for the divergent program is undecidable when restricted to well-formed programs.
- `self_rice_representable`: A guest program deciding such a property would make the complement of single-tape Turing halting enumerable.
- `g_decides_decidable`: A guest program that decides a property through its register 0 yields a Boolean decider for the property on well-formed programs.
- `vm_guest_recursion_theorem_closed`: For any transformer `F` on guest programs that sends well-formed guest programs to well-formed guest programs, and any well-formed guest program `D` that represents `F` (on the code of each well-formed program `p`, `D` terminates with register 0 holding the code of `F p`), some well-formed guest program `p` has the same terminating behaviours as `F p`, meaning the same final registers and the same `mu` for every input.
- `g_pair_smn`: For every guest program `p`, constant `x`, and input `y`, the specialized program `g_pair_specialize p x` run on `y` halts with registers `g` and ledger `mu` exactly when `p` run on the pair `g_pair x y` halts with `g` and `mu`.
- `hfun_sem`: If the guest program `D` represents the transformer `F` and `e` is well formed, the fuel function returns `m` for some fuel on the pair of `e`'s code and `y` exactly when `m` packs registers `g` and ledger `mu` with which `F` applied to `e` specialized by its own code halts on `y`.
- `RD_MMA`: For every guest program `D`, the relation "some fuel makes the tuple-form evaluator return `m` on input `z`" is computed by an alternate Minsky machine.
- `g_pipeline_beh_pack`: If every output of the Minsky program `P` on input `z` packs some registers and ledger, then the guest pipeline for `P` halts on `z` with registers `g` and ledger `mu` exactly when `P` halts on `z` with output `g_out_pack g mu`.

## Categories

- `relational_compose_assoc` (`Kernel.CategoryLaws.relational_compose_assoc`): Relational composition of coupling relations is associative up to membership.
- `morph_graph_compose_assoc`: For three stored morphisms whose ends match, the two groupings of their coupling compositions agree up to membership.
- `graph_compose_morphisms_coupling`: A successful `COMPOSE` stores a morphism whose coupling is the other input's coupling when one input is an identity, and their relational composition otherwise.
- `morph_compose_assoc_coupling`: For three lists of pairs of naturals, `relational_compose` of the composite of the first two with the third equals `relational_compose` of the first with the composite of the other two, up to `coupling_equiv` (the same pairs).
- `morph_id_left_coupling`: For a region list and a pair list `pairs_f` in which every pair's first component lies in the region, composing the diagonal pairs `(x, x)` over the region with `pairs_f` gives `pairs_f` up to `coupling_equiv`.
- `morph_id_right_coupling`: For a region list and a pair list `pairs_f` in which every pair's second component lies in the region, composing `pairs_f` with the diagonal pairs `(x, x)` over the region gives `pairs_f` up to `coupling_equiv`.
- `monoidal_coherence` (`Kernel.CategoryMonoidal.monoidal_coherence`): For three lists of pairs, `coupling_tensor` (list append) is associative and has the empty list as a left and right unit, as equalities of lists.
- `tensor_bifunctor` (`Kernel.CategoryMonoidal.tensor_bifunctor`): For four lists of pairs `pf`, `pg`, `pf'`, `pg'`, if the composite of `pf` with `pg'` and the composite of `pg` with `pf'` are both coupling-equivalent to the empty list, then composing `pf ++ pg` with `pf' ++ pg'` is coupling-equivalent to the append of the composite of `pf` with `pf'` and the composite of `pg` with `pg'`.

## CHSH and NPA

- `local_strategy_chsh_between_neg2_2`: Four local response bits give an integer CHSH value between -2 and 2.
- `local_box_CHSH_bound`: A factorizable box has absolute CHSH value at most 2.
- `classical_bound_achieved` (`Kernel.ClassicalBound.classical_bound_achieved`): A zero-cost six-instruction VM trace, run from its starting state, records a tally whose CHSH value is exactly 2.
- `chsh_stat_violation_not_local`: A tally with CHSH above 2 is inconsistent with any single four-bit strategy repeated at every trial.
- `chsh_violation_rules_out_locally_factorizable_coupling`: The same statement in coupling vocabulary.
- `locally_consistent_classical_bound`: A tally consistent with one four-bit strategy has absolute CHSH value at most 2.
- `chsh_trial_is_tier0`: `CHSH_TRIAL` is never a certification-insight event.
- `nonlocal_correlation_requires_revelation`: A trace that starts with `csr_cert_addr` zero and ends with it set contains a `REVEAL`, `EMIT`, `LJOIN`, `LASSERT`, or `MORPH_ASSERT`.
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
- `c4_direct_tsirelson_abs_from_npa_psd`: For any fuel, trace, and initial state, if the zero-marginal NPA matrix built from the trace's four correlator values `trace_e00` through `trace_e11` is positive semidefinite, then the absolute value of `CHSH` of those four values is at most `sqrt8`.
- `trace_column_contractive_iff_trace_npa_model`: For any fuel, trace, and initial state, `trace_column_contractive` holds exactly when the trace's zero-marginal NPA matrix is positive semidefinite.
- `tsirelson_from_minors`: For four reals, if `1 - e00^2 - e01^2 >= 0` and `1 - e10^2 - e11^2 >= 0`, then the square of `CHSH e00 e01 e10 e11` is at most 8.
- `tsirelson_squared`: For four reals with `e00^2 + e01^2 <= 1` and `e10^2 + e11^2 <= 1`, `CHSH_value e00 e01 e10 e11` multiplied by itself is at most 8.
- `fine_theorem`: For any correlator table `E` that is factorizable (two `+1`/`-1` response functions, a probability distribution on finitely many hidden states, and `E a b x y` equal to the distribution-weighted sum of the products of the two responses), `E 0 0 0 0 + E 0 0 0 1 + E 0 0 1 0 - E 0 0 1 1` lies between -2 and 2.
- `column_contractive_check_witness_sound`: If the integer witness check passes, the witness-derived correlators are column-contractive.
- `chsh_lassert_no_trap_implies_npa_psd`: A `CHSH_LASSERT` step that advances without setting the error flag implies the witness-derived zero-marginal NPA matrix is symmetric and PSD.
- `chsh_lassert_1ab_no_trap_implies_npa_psd_q1ab`: A `CHSH_LASSERT_1AB` step that advances without error implies the 9 by 9 level-1+AB matrix at the witness correlators and zero higher moments is symmetric and PSD.
- `state_column_contractive_implies_npa_gram`: A state whose correlators are column-contractive has a symmetric PSD zero-marginal NPA matrix.
- `state_column_contractive_implies_tsirelson`: A state whose correlators are column-contractive has CHSH value squared at most 8.
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

## Geometry

- `discrete_gauss_bonnet`: For a partition graph meeting `well_formed_triangulated`, which includes the extra condition `B = 3 chi`, the defined angle-defect sum equals `5 pi chi`.
- `boundary_4simplex_nonuniform_diagonal_refuted_at_1`: For any state `s`, if the full metric at vertex 1 equals 2 on the diagonal and 0 off it for indices below 4, and the full metric at vertex 0 equals 1 on the diagonal and 0 off it for indices below 4, then `combinatorially_orthogonal boundary_4simplex s 1` fails, that is, some off-diagonal `curved_ricci` entry (indices below 4) at vertex 1 is nonzero.
- `curvature_from_mu_gradients`: For any state `s`, complex `sc`, indices, and vertex, if every module carries the same tensor (`uniform_module_tensor s`), then `RiemannTensor4D.einstein_tensor s sc mu nu v` equals 0.
- `einstein_equation_vacuum`: For any state, complex, indices, and vertex, if every module has structural mass 0 and `uniform_module_tensor s` holds, then `einstein_tensor s sc mu nu v` equals `8 * PI * gravitational_constant` times `stress_energy_tensor s sc mu nu v`.
- `flat_spacetime_christoffel_zero_general`: If `uniform_module_tensor s` holds, `RiemannTensor4D.christoffel s sc rho mu nu v` equals 0 for every complex, index triple, and vertex.
- `flat_spacetime_riemann_zero_general`: If `uniform_module_tensor s` holds, `RiemannTensor4D.riemann_tensor s sc rho sigma mu nu v` equals 0 for every complex, index quadruple, and vertex.
- `flat_spacetime_einstein_zero_general`: If `uniform_module_tensor s` holds, `RiemannTensor4D.einstein_tensor s sc mu nu v` equals 0 for every complex, index pair, and vertex.
- `full_metric_compat_diagonal`: For a state, a vertex, and indices below 4, if the module tensor entries at that vertex equal the structural mass on the diagonal and 0 off it for all index pairs below 4, then `full_metric_at_vertex s v mu nu` equals `metric_at_vertex s v mu nu`.
- `non_uniform_mass_produces_curvature` (`Kernel.EinsteinEquations4D.non_uniform_mass_produces_curvature`): If two vertices `v` and `w` have different `module_structural_mass`, then it is not the case that `metric_at_vertex s u1 mu mu` and `metric_at_vertex s u2 mu mu` agree for all vertices `u1` and `u2`; the statement concludes position dependence of one diagonal metric component and does not mention curvature tensors.
- `stress_off_diagonal_zero_isotropic`: If the metric components at vertex `v` are 0 off the diagonal (`diagonal_metric_at s v`) and `i` differs from `j`, then `stress_component s sc v i j` (the energy density times the metric component) equals 0.
- `triangle_angle_plus_one_correction_decays`: For `d` at least 1, with the two denominators `3d` and `3d + 1` positive as premises, `PI * d / (3d + 1) - PI * d / (3d)` equals `-PI / (3 * (3d + 1))` as reals.

## Hardware and extraction

- `driven_step_wf`: One Kami model step, read through the abstraction, equals `vm_apply` on the abstracted state whenever `WFDrivenPrecondition` holds.
- `driven_trace_commutes`: A fuel-bounded driven Kami run, read through the abstraction, equals the VM run whenever `WFDrivenRun` holds at every visited state.
- `driven_step_compose`: Under the extended hardware invariant, one Kami `COMPOSE` step equals the VM's `COMPOSE` step through the abstraction.
- `kami_register_write_matches_vm`: Writing a register in a Kami snapshot gives the same register list as `write_reg` on the abstracted state. This is one register-write lemma, not step refinement.
- `morph_table_wf_kami_step_preserved`: Every Kami step preserves morph-table well-formedness.
- `coupling_desc_safe_kami_step_preserved`: Every Kami step preserves coupling-descriptor safety.
- `coupling_zero_empty_kami_step_preserved`: For any `KamiSnapshot` `ks` and instruction `i`, if `coupling_desc_safe ks` holds (the next coupling descriptor id is positive) and `coupling_zero_empty` holds on its rich state (coupling descriptor table entry 0 is empty), then `coupling_zero_empty` holds on the rich state of `kami_step ks i`.
- `coupling_wf_kami_step_preserved`: Every Kami step preserves coupling well-formedness, given coupling-descriptor safety.
- `start_from_reset`: Every execution of the CPU's `start` method from `hardware_reset_state` calls no other method and writes exactly the halted flag (false) and the program counter (zero); the reset state with those writes applied is `dispatch_reset_state`.
- `one_frame`: For every byte `s` held from before, every byte `v`, and all program registers `p`, running the loader's `rxSample` method once per cycle over the waveform of one serial frame of `v` (start bit, eight data bits least significant first, stop bit, 174 cycles each) from the idle receiver holding `s` ends at the idle receiver holding `v`, with the program registers changed exactly by `byte_step p v`.
- `serial_program_load`: For every list `ws` of 1 to 128 instruction words and every index `k` with `ws[k] = w`, running `rxSample` from the loader's reset registers over the frames of the count bytes and of the sixteen little-endian bytes of instructions 0 to `k` leaves `load_addr = k`, `load_data = w`, `load_req` equal to the parity flag `Nat.even k`, and `start_req` true exactly when `k` is the last index.
- `load_rule_hands_off`: When the loader's `load` rule executes on registers holding `load_req`, `load_ack`, `load_addr = a`, and `load_data = d`, the request and acknowledgement differ, the rule's only method call is `loadInstr` with the port value built from `a` and `d`, and its only register update sets `load_ack` to `load_req`.
- `load_instr_writes`: When the CPU's `loadInstr` method executes on the port value built from `a` and `d`, it calls no method and its only update sets `imem` to the old instruction memory with address `a` mapped to `d`.
- `fsm_retirement_refinement`: From a reset boundary state, every admitted run keeps the table invariants, ends at the snapshot the Kami run list computes, and is an actual multistep execution of the CPU core.
- `admitted_run_progress`: An admitted run from a boundary state reaches its end boundary in some number of rule runs, matches the Kami run list, and is an actual multistep execution.
- `rtl_inventory_arithmetic`: `37 + 10 + 0 = 47`. It records the synthesized-opcode count and checks no opcode.
- `rtl_gap_registry_empty`: The hand-written RTL gap list is empty.
- `ocaml_observable_nofi_and_monotone`: On the Coq-side observable the OCaml runner is tested against, certification costs at least one and mu never decreases.
- `ocaml_runner_observable_defined`: For every state and instruction, the Coq-side observable is defined. This is true of any Coq function; the binary's agreement is tested, not proved.
- `receipt_encoding_roundtrip`: Unpacking a packed receipt returns its mu, certification bit, and memory.
- `coq_kami_model_satisfies_rtl_step_correct`: For any `KamiSnapshot` `ks` and any instruction `i` outside the sixteen opcodes excluded by `SupportedOpcode` (PNEW, PSPLIT, PMERGE, LASSERT, CALL, RET, CHSH_TRIAL, tensor set and get, and the morphism instructions MORPH, COMPOSE, MORPH_ID, MORPH_DELETE, MORPH_ASSERT, MORPH_TENSOR, MORPH_GET), the full snapshot abstracted from `kami_step ks i` equals `vm_apply` applied to the full snapshot abstracted from `ks`.
- `three_layer_bisimulation`: For two `WireSpec` records (each with a step function, `mu` and `pc` projections, `mu` rising by exactly `instruction_cost`, `pc` rising by one, and determinism) and states with equal `mu` and equal `pc`, running the same instruction list in each gives equal `mu` and equal `pc`.
- `full_state_single_step_bisimulation`: For two `FullWireSpec` records (each satisfying its `fws_step_correct` field) and states that agree on all twelve projections (graph, CSRs, registers, memory, program counter, `mu`, `mu` tensor, error flag, logic accumulator, `mstatus`, witness counts, certified flag), one step on the same instruction yields states that agree on all twelve.
- `full_state_trace_bisimulation`: For two `FullWireSpec` records and states that agree on the same twelve projections, running the same instruction list with `run_fws` in each yields states that agree on all twelve.

## Physics files

- `full_efe_uniform_two_vertex`: For a uniform diagonal two-vertex metric, the computed curved Einstein tensor equals zero times the stress-energy, that is, zero. Both sides vanish; this does not derive general relativity.

## Models from other fields

- `quote_cannot_attest_unmeasured_state`: In the scoped TPM quote-field abstraction, whose quote authenticity is assumed externally rather than modeled, no function of the selected-PCR digest and nonce returns the additional runtime Boolean for every platform.
- `quote_decides_measured_claims`: In the same model, every supplied Boolean function of the retained selected-PCR digest is computed by some Boolean function of the quote.
- `quote_projection_faithful`: Two modeled quotes have equal classical-transcript encodings exactly when their nonce and retained selected-PCR digest agree.
- `quote_runtime_verifier_separation`: Any Boolean verifier that returns the modeled runtime claim on every full platform state fails to factor through the lossless encoding of its quote, by the named verifier corollary and an explicit truth-label adapter.
- `persistent_write_priced`: In the transcribed Prague `sstore` gas and refund arithmetic, for one storage slot that is empty at the start of a transaction, any sequence of stores that leaves it nonzero has gas charged minus refund counter of at least 20000; the EIP-3529 refund cap is outside the model.
- `revoked_write_nearly_free`: In the same model, setting a cold empty slot to one and clearing it again costs 2300 net, while setting it and leaving it set costs 22100.
- `accountable_safety` (`Kernel.CasperFFG.accountable_safety`): In the ported Casper FFG model, under the setting's quorum-intersection and single-parent premises, two finalized blocks on different branches imply that some set in the second quorum class consists of slashed validators.
- `conflicting_records_are_priced`: Reading finalization as the record, two finalized blocks on different branches imply a slashed set in the second quorum class; this restates accountable safety.
- `finalization_without_slashing`: In the one-validator chain setting, a single vote finalizes the genesis block and no validator is slashed.

## Trace and projection contracts

- `no_free_certification_mu`: A VM step that changes the certificate address from zero to nonzero raises mu by at least one.
- `no_free_certification_trace_mu`: An instruction-list run that changes the certificate address from zero to nonzero raises mu by at least one.
- `thiele_nfi_pc_indexed`: A successful PC-indexed trace run that changes the certificate address from zero to nonzero contains an instruction in the certificate-address setter class.
- `thiele_universal_nfi_cert_addr`: In the VM certificate-address system, an instruction-list run from uncertified to certified has total instruction cost at least one.
- `thiele_universal_nfi_certified`: In the VM certification-flag system, an instruction-list run from uncertified to certified has total instruction cost at least one.
- `kernel_certified_implies_positive_mu` (`Kernel.PrimeAxiom.kernel_certified_implies_positive_mu`): A bounded VM run from an uncertified state with mu zero that ends certified has positive final mu.
- `run_vm_mu_conservation` (`Kernel.MuLedgerConservation.run_vm_mu_conservation`): A bounded VM run's final mu equals its initial mu plus the sum of the ledger entries recorded by that run.
- `executed_instruction_cost_recorded`: Every instruction occurring in the bounded run's executed-instruction list has its cost in the corresponding ledger-entry list.
- `ledger_sum_contains_lower_bound`: The sum of a natural-number ledger-entry list is at least any entry in the list.
- `forged_receipt_fails_validation`: For a receipt `r` and a claimed `mu` delta that differs from `instruction_mu_delta` of the receipt's instruction, if `receipt_post_mu` equals `receipt_pre_mu` plus the claimed delta, then `receipt_mu_consistent r` fails.
- `valid_chain_mu_equals_computation`: For a receipt list `rs` and start value `initial_mu` with `receipt_chain_valid rs initial_mu`, any claimed final `mu` that equals `initial_mu` (for the empty list) or the last receipt's `receipt_post_mu` (otherwise) equals `chain_final_mu rs initial_mu`, which is `initial_mu` plus the chain's total cost.
- `structural_trace_preserves_cert_addr`: An instruction-list run containing no certificate-address setter preserves the certificate address.
- `graph_certify_morphism_lookup`: If a morphism lookup succeeds, certifying that morphism makes the same lookup return the same fields with its certification cost replaced by the supplied cost.
- `forget_kernel_is_eq_on_classical`: Two VM states have equal `forget` projections exactly when they agree on the fields in `eq_on_classical`.
- `blindness_non_injective`: Two distinct VM states have the same `forget` projection.
- `certification_is_lost`: Two VM states have the same `forget` projection and different certification flags.
- `mu_ledger_necessity` (`NecessityOfMuLedger.mu_ledger_necessity`): No function of the strict memory-register-PC projection recovers both mu and certification on every VM state.
- `vm_mu_not_classically_determined` (`NecessityOfMuLedger.vm_mu_not_classically_determined`): No function of the strict memory-register-PC projection recovers mu on every VM state.
- `vm_certified_not_classically_determined` (`NecessityOfMuLedger.vm_certified_not_classically_determined`): No function of the strict memory-register-PC projection recovers certification on every VM state.
- `vm_apply_certify_strict_shadow` (`NecessityOfMuLedger.vm_apply_certify_strict_shadow`): CERTIFY preserves memory and registers and increments PC in the strict projection.
- `vm_apply_pnew_strict_shadow` (`NecessityOfMuLedger.vm_apply_pnew_strict_shadow`): A PNEW that succeeds (`pnew_ok`) preserves memory and registers and increments PC in the strict projection.
- `mu_ledger_necessity_universal`: From every VM state with a free module number (`module_room s.(vm_graph) 1`), CERTIFY 0 and PNEW [] 0 produce the same strict projection, while CERTIFY adds one to mu and sets certification and PNEW preserves mu.
- `po1_trace_necessity`: Appending CERTIFY 0 or PNEW [] 0 to any instruction-list prefix from `po1_init` that leaves a free module number gives equal strict projections and strictly greater mu in the CERTIFY case.
- `shadow_mu_is_computation_intrinsic`: For a fixed instruction list, final mu equals initial mu plus the list's summed instruction cost.
- `shadow_mu_delta_universal`: Running the same instruction list from any two states produces equal mu increments.
- `shadow_mu_unique_accounting`: Any measure with the canonical per-instruction increments and value zero at the supplied start equals the summed instruction cost after that list run.
- `shadow_mu_inevitable`: An instruction list containing an instruction of positive cost strictly raises mu under instruction-list execution.
- `turing_ram_mu_necessity` (`Kernel.NecessityAbstract.turing_ram_mu_necessity`): No function of `P_strict` recovers mu on every VM state.
- `turing_ram_cert_necessity` (`Kernel.NecessityAbstract.turing_ram_cert_necessity`): No function of `P_strict` recovers certification on every VM state.
- `cost_model_cert_necessity` (`Kernel.NecessityAbstract.cost_model_cert_necessity`): No function of `P_cost`, which includes mu, recovers certification on every VM state.
- `cert_model_mu_necessity` (`Kernel.NecessityAbstract.cert_model_mu_necessity`): No function of `P_cert`, which includes certification, recovers mu on every VM state.
- `mu_ledger_minimality` (`Kernel.NecessityAbstract.mu_ledger_minimality`): `P_full` recovers mu and certification, `P_strict` recovers neither, `P_cost` recovers only mu, and `P_cert` recovers only certification.
- `graph_not_recoverable_from_P_full`: No function of the full mu-ledger projection recovers the partition graph on every VM state.
- `thiele_state_three_component_independence`: The stated strict, cost, certificate, and full-ledger projections fail to recover the omitted mu, certification, and graph fields in the five displayed combinations.
- `classical_observer_cannot_separate` (`Kernel.PartitionSeparation.PartitionSeparation.classical_observer_cannot_separate`): Every function satisfying `is_classical_observer` gives the same answer on some computationally equivalent states with different morphism structure.
- `shadow_separation_theorem`: Two states agree under `shadow_equal`, have different morphism lists, and still have different morphism lists after one common probe instruction.
- `no_classical_certification_decider`: No Boolean function of projected classical traces agrees with the defined certification decider on every Thiele trace.
- `selected_representatives_give_decoder`: Given a representative for every view whose observation is that view, a query is constant on observation fibers exactly when it factors through a decoder of the view.
- `reachable_simulation_unique`: Two `ReachableCertSimulation` records into the same target with the same base map every VM trace endpoint to equal target states.
- `D2_faithfulness`: A classical instruction-list run has its defined six-field projection and preserves its initial partition graph, certificate address, and certification flag.
- `D3_conservativity`: A list of classical opcodes preserves the partition graph, certificate address, and certification flag under instruction-list execution.
- `D3_conservativity_pc`: For any fuel, `run_vm` on a program whose instructions are all classical, which follows jumps through the program counter, leaves the partition graph, certificate address, and certification flag unchanged.
- `classical_reachable_preserves_structure`: Every state reached by a sequence of steps that each execute a classical instruction has the partition graph, certificate address, and certification flag of the starting state.
- `D4_strictness`: Some state reachable from `init_state` (it is `init_state`) and some VM instruction change the graph's next-module identifier where every classical instruction-list run from that state preserves it.
- `D4_strictness_reachable`: For every state `s` a classical run reaches from `init_state`: `s` is reachable; PNEW of address 0 is a step from `s` that raises `pg_next_id` by one and leaves the error latch as it was; every classical step sequence from `s` and every `run_vm` of a classical program from `s` keep `pg_next_id`; and the graph PNEW produces differs from the graph of every state a classical run reaches from `init_state`.
- `D4_strictness_from_init`: From `init_state`, PNEW of address 0 is a step to a state with `pg_next_id = 1`, and `run_vm` of every classical program from `init_state`, for any fuel, ends with `pg_next_id = 0`.
- `nat_recursion_theorem`: For the candidate-decider-dependent nat substrate, every transformer selected by its representability predicate has a code whose total run equals the transformer's image on every input state.

## Information and witness contracts

- `feasible_strict_subset_implies_strict_predicates`: A strict feasible subset and an excluded prior state whose observation differs from every posterior observation make the induced posterior receipt predicate strictly stronger.
- `b4_information_reduction_derives_strict_predicates`: With a correct Boolean equality test on observations, a strict feasible subset and a distinguishing excluded state yield two receipt predicates with strict strengthening.
- `strengthening_requires_structure_addition` (`Kernel.NoFreeInsight.NoFreeInsight.strengthening_requires_structure_addition`): If a strictly stronger receipt predicate is certified after a bounded run from certificate address zero, that run contains a structure-addition event.
- `info_priced_cert_executions_bound`: The number of executed certificate setters in a bounded VM run is at most its mu increment.
- `current_schedule_not_globally_cert_priced`: It is not the case that every instruction satisfies `MuChaitin.cert_priced` (for a cert-setter, `cert_payload_size` is at most `instruction_cost`).
- `observation_partition_reduction_implies_posterior_representative_reduction`: An observation-partition reduction supplies the posterior-representative reduction contract for the same observation, tree, and feasible sets.
- `info_priced_arbitrary_feasible_reduction_bound`: Given a tree whose depth is paid by the bounded trace, a nonempty posterior, and the tree's covering inequality, the rounded-log feasible-size difference is at most the trace's mu increment.
- `info_priced_weighted_feasible_reduction_bound`: Given a tree whose depth is paid by the bounded trace, positive posterior mass, and the weighted covering inequality, the defined weighted entropy reduction is at most the mu increment.
- `exists_covering_tree`: Every pair of feasible lists with a nonempty posterior has a decision tree satisfying the defined size-covering inequality.
- `info_priced_reduction_no_tree_hypothesis`: If a bounded trace pays for the specified complete tree and the posterior is nonempty, its mu increment bounds the rounded-log feasible-size difference.
- `partition_structural_ops_not_cert_setters`: PNEW, PSPLIT, and PMERGE are outside the certificate-address setter class for every choice of operands and cost.
- `partition_structural_ops_can_be_free`: There are zero-cost PNEW, PSPLIT, and PMERGE instructions.
- `partition_structural_trace_cannot_certify`: An instruction list made only of partition-structural instructions preserves the certificate address.
- `partition_refinement_nonfree`: A trace from certificate address zero to nonzero contains a certificate setter costing at least one and raises mu by at least one; no partition-refinement premise is required.
- `partition_free_but_certification_nonfree`: Zero-cost partition-structural instructions exist and are not certificate setters, while every trace changing certificate address zero to nonzero raises mu by at least one.
- `chsh_trial_preserves_cert_addr`: Every CHSH_TRIAL step leaves the certificate-address register unchanged.
- `chsh_trial_preserves_vm_certified`: Every CHSH_TRIAL step preserves the VM certification flag.
- `certified_witness_insight_nonfree`: A step satisfying the defined witness-insight event costs at least one and raises mu by at least one.
- `nonlocal_witness_insight_nonfree`: A step from an uncertified state to a state with a certified nonlocal witness costs at least one and raises mu by at least one.
- `witness_insight_nonfree_general`: An instruction-list run from uncertified to certified with a certified CHSH violation raises mu by at least one.
- `witness_insight_complete_taxonomy`: CHSH_TRIAL is never a certification-insight event, every such event costs at least one, and a trace from uncertified to a certified CHSH violation raises mu by at least one.
- `certified_insight_nonfree`: For any VM state and instruction, if the step moves `csr_cert_addr` from zero to nonzero or moves `vm_certified` from false to true, then `instruction_cost` of the instruction is at least 1 and `vm_mu` after `vm_apply` is at least `vm_mu` before plus 1.
- `compression_priced_trace_floor`: On an enumerated finite state space with permanent certification and compression pricing, an instruction-list run from uncertified to certified costs at least one.
- `priced_reset_satisfies_premises`: The two-state Blank/Stamped machine is finite, keeps its stamp permanently, and prices every merging step at one.
- `step_price_is_exact`: The defined full-state certification-flip indicator price meets the flip floor and never overcharges.
- `categorical_extension_nofi_consistent`: Every MORPH_ASSERT instruction is in the certificate-setter class and has positive cost.
- `locally_consistent_gives_separable_coupling`: A witness tally consistent with the supplied four local deterministic outputs induces a separable setting-outcome coupling.
- `priced_on_traces`: Inside `KernelTraceInstance`, for every `k`, every instruction of the fixed three-instruction trace (`instr_pnew [0] 0`, `instr_morph_id 0 0 0`, `instr_morph_assert 0 "p" "" 8`) satisfies `MuChaitin.cert_priced`.
- `kernel_trace_instance_bound`: In the fixed `KernelTraceInstance` (where `proves_bits k` is `k <= 8`), `proves_bits k` implies `k <= 9`.
- `kernel_trace_instance_inhabited`: In the fixed `KernelTraceInstance`, `proves_bits 8` holds, that is, `8 <= 8`.

## Replicated-record examples

- `toggle_game_refutes_strong_pointer_necessity`: Consensus, authentic observer views, a positive observer count, and coordinator-free evolution do not imply event permanence, because the two-observer toggle game satisfies those premises and revokes its event.
- `durable_consensus_implies_permanence`: A positive observer count, authentic observer views, and durable true views imply event permanence; durability is the premise that supplies the conclusion.
- `vm_certification_is_permanent_consensus`: For every observer count `n` greater than 0 and instruction `i`, the game on VM states whose event is `vm_certified` and whose step is `vm_apply_u s i` has `event_permanent`: if `vm_certified` holds before the step it holds after.

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

## Scalar physics and geometry contracts

- `canonical_reset_heat_exact`: In the frozen two-state reset protocol, the bath heat for an energy gap `Delta` is exactly `Delta / 2`.
- `selected_gap_gives_landauer_heat`: Choosing the two-state energy gap to be `2 * k_B * T * ln 2` makes the frozen reset protocol's bath heat exactly `k_B * T * ln 2`.
- `master_equation_does_not_fix_heat_scale`: Two distinct energy gaps obey the same frozen population master equation but transfer different heat, so those population dynamics alone do not determine an energy scale.
- `calibrated_mu_landauer_energy`: For all reals `k_B` and `T`, every VM state with `vm_mu = 1` has `vm_mu_energy_at_scale (k_B * T * ln 2) s` equal to `k_B * T * ln 2`; the scale is the supplied argument, so this is the arithmetic `vm_mu * scale`.
- `canonical_reset_satisfies_master_equation`: One step of the discrete two-state master equation, with the protocol's fixed time step and transition rates, carries the frozen initial populations exactly to the frozen final populations.
- `vm_minimal_certification_charges_canonical_reset_mu`: `abs_zero` is uncertified, and `vm_apply_u abs_zero (instr_certify 0)` is certified with `vm_mu` equal to `abs_zero`'s `vm_mu` plus `canonical_reset_mu` (which is 1).
- `vm_certification_charges_at_least_canonical_reset_mu`: For any VM state `s` with `vm_certified` false and any instruction `i`, if `vm_apply_u s i` has `vm_certified` true, then `vm_mu s` plus `canonical_reset_mu` (which is 1) is at most `vm_mu` of `vm_apply_u s i`.
- `smaller_gap_refutes_unconditional_landauer_floor`: For positive `k_B` and `T`, the frozen reset protocol with energy gap `k_B * T * ln 2` transfers bath heat strictly less than `k_B * T * ln 2`, so the protocol by itself does not enforce a Landauer floor.

- `zero_mu_traces_satisfy_preservation_budget`: If each input has a bounded error-free zero-mu trace, every Boolean state predicate satisfies `error_free_preservation_budget` with mu bound zero because its positive-mu antecedent is false.
- `tsirelson_rational_lower_witness`: Some correlator satisfying the selected rational coherence predicate has CHSH at least 28284/10000.
- `zero_cost_preserves_radius` (`Kernel.Unitarity.zero_cost_preserves_radius`): If both radius-loss and radius-gain inequalities are supplied and formal cost is zero, the evolution preserves squared radius on the unit ball.
- `ball_trace_contract_from_premises`: Positivity and trace preservation supply the defined scalar ball-and-trace contract, with no assertion of complete positivity for operators.
- `master_tsirelson_conditional` (`PhysicsConditionalClosure.master_tsirelson_conditional`): Under the section's physical quantum bridge, correlations satisfying its honest-quantum predicate have absolute CHSH value at most the defined square root of eight.
- `no_cloning_from_conservation` (`Kernel.NoCloning.no_cloning_from_conservation`): A nontrivial input, the scalar conservation inequality, and a perfect-copy operation imply that the operation's formal cost is nonzero.
- `no_cloning_bloch` (`Kernel.NoCloning.no_cloning_bloch`): For a radius-one input whose squared radius equals the operation's input-information field, scalar conservation and perfect copying imply formal cost at least one.
- `linear_implies_born`: For any `ProbRule` `P` that is valid (both outcome values non-negative on the unit ball, outcomes summing to 1 everywhere, `P 0 0 1 0 = 1`, and `P 0 0 (-1) 0 = 0`) and affine in `z` on the unit ball (`P x y z 0 = a * z + b` for some reals `a` and `b`), `P x y z 0` equals `(1 + z) / 2` for every `x, y, z` with `x^2 + y^2 + z^2 <= 1`.
- `valid_linear_rule_is_born_with_cost_side_condition`: For any valid `ProbRule` `P` that is affine in `z` on the unit ball and satisfies `measurement_cost_nonnegative P` (the linear-entropy cost `(1 - x^2 - y^2 - z^2) / 2` is non-negative on the unit ball, a condition that does not inspect `P`), `P x y z 0` equals `(1 + z) / 2` and `P x y z 1` equals `(1 - z) / 2` for every `x, y, z` with `x^2 + y^2 + z^2 <= 1`.
- `unitary_cannot_clone`: Under conservation, the radius upper bound, zero formal cost, a valid Bloch vector, and positive input radius, two equal copies of the output radius cannot both equal the input radius while their sum satisfies the displayed conservation inequality.
- `nonunitary_requires_mu`: If formal radius loss is bounded by formal cost on the unit ball and is positive at one valid input, formal cost is positive.
- `lindblad_requires_mu`: Given a positive gamma, the defined dissipation bound, information conservation, and radius loss exactly gamma at (1,0,0), formal cost is at least gamma.
- `zero_cost_preserves_purity` (`Kernel.Unitarity.zero_cost_preserves_purity`): If formal radius loss is bounded by cost and cost is zero, output squared radius is at least input squared radius on the unit ball.
- `erasure_irreversible`: An Erasure record losing at least one bit has defined fan-in greater than one.
- `erasure_decreases_entropy`: An Erasure record losing at least one bit has negative integer entropy difference as defined from its bit counts.
- `landauer_information_bound`: A PhysicalErasure record's environment-entropy increase is at least its erased-bit count under the entropy-balance premise carried in the record.
- `erasure_additive`: Composable Erasure bit counts have erased-bit differences that add to the total input-output difference.
- `mu_cost_positive_for_projection`: Projecting a positive level of a ThieleManifold record to its fourth component has positive cost under the record's level and projection contracts.
- `z_action_identity`: Shifting a state's mu by the integer zero returns that state.
- `z_action_composition`: Two integer shifts of mu compose by addition when both intermediate and final integer balances are nonnegative.
- `z_action_inverse`: An integer mu shift followed by its negative returns the original state when the first balance is nonnegative.
- `noether_forward`: For two VM states, if their `Observable_partition` (the list of module regions), graph, registers, memory, CSRs, program counter, `mu` tensor, error flag, logic accumulator, `mstatus`, witness counts, and certified flag are equal, then some integer `delta` has `z_gauge_shift delta s1 = s2` (the shift changes `vm_mu` by `delta` and keeps every other field).
- `vm_step_mu_monotonic`: Every VM step preserves or increases mu.
- `vm_step_orbit_equiv`: A VM step commutes with a supplied integer mu shift when the shifted initial balance is nonnegative.
- `exec_trace_no_signaling_outside_cone`: An executed trace from a well-formed graph preserves a valid module's observable region when the module lies outside the trace's causal cone.
- `calibration_residual_zero_iff`: The defined calibration residual is zero exactly when angle-defect curvature equals the supplied coupling constant times the mu Laplacian.
- `total_mu_laplacian_zero`: Summing the mu Laplacian over the graph's module list gives zero.
- `strong_bridge_counterexample`: For positive natural d, the degree-six defect computed from the specified uniform triangle angle differs from the defect computed using pi/3.
- `unit_residual_is_nonzero`: Any real quantity equal to one is nonzero.
- `pi_times_unit_is_nonzero`: Multiplying a real quantity equal to one by pi gives a nonzero result.
- `affine_off_diagonal_ricci_zero`: Under the named nonuniform isotropic metric predicate, off-diagonal Ricci entries at vertex 1 of the boundary 4-simplex vanish for indices below four.
- `affine_full_tensor_efe`: Under that metric predicate and structural mass one at vertex 1, every Einstein-tensor entry there equals three times the modeled mass stress-energy entry for indices below four.
- `affine_ricci_offdiag_outer`: Under that metric predicate, off-diagonal Ricci entries at vertices 0, 2, 3, or 4 equal 3/32 for indices below four.
- `affine_ricci_diag_outer`: Under that metric predicate, diagonal Ricci entries at vertices 0, 2, 3, or 4 equal -45/32 for indices below four.
- `affine_ricci_scalar_outer`: Under that metric predicate, Ricci scalars at vertices 0, 2, 3, or 4 equal -45/8.
- `affine_einstein_outer`: Under that metric predicate, Einstein-tensor entries at vertices 0, 2, 3, or 4 equal 45/32 on the diagonal and 3/32 off it for indices below four.
- `affine_efe_fails_outer_offdiag`: Under that metric predicate, the off-diagonal Einstein entries at vertices 0, 2, 3, or 4 differ from three times modeled mass stress-energy for indices below four.
- `self_reference_requires_metalevel`: For every `System` (a dimension number and a map on propositions) that contains a self-reference (some proposition `P` with `sentences S P` and `P` true), there is a `System` `Meta_S` that can reason about it (every proposition `S` expresses, `Meta_S` expresses), has strictly greater dimension, and itself contains a self-reference.
- `embed_step_compute`: For instructions outside the sixteen explicitly excluded structural, call/return, witness, tensor, and morphism opcode cases, abstracting the intermediate Kami step equals applying the VM step to the abstraction.
- `five_labeled_models_have_selected_pointer`: In the five synthetic labelled mirror models, each selected flag is returned by every stipulated observer and its named rival is not.

- `F3_calibration_forces_flat_faces`: If every region of the partition graph is a normalized triangle and calibration holds at every module, then at every module the mu-Laplacian is zero, the angle-defect curvature is zero, and the angles of its triangles sum to 2*PI.
- `F3_calibration_forces_five_triangles`: Under the same hypotheses every module lies in at least five triangles.
- `F3_calibration_obstruction_closed`: A well-formed triangulated partition graph with distinct module identifiers and no boundary edges cannot be calibrated at every module.
- `F3_calibration_obstruction_min_degree4`: A well-formed triangulated partition graph with distinct module identifiers in which every vertex lies in at least four faces cannot be calibrated at every module.
- `F3_calibration_obstruction`: No VM state whose partition graph is well-formed triangulated, has connected vertex links, and has distinct module identifiers is calibrated at every module.
- `F3_obstruction_hypotheses_satisfiable`: A concrete VM state (an octahedron next to a zigzag 9-gon) satisfies every hypothesis of `F3_calibration_obstruction`.
- `vm_reachable_regions_separate`: From a state with no modules, a well-formed graph and at most 64 module numbers issued, every reachable state has pairwise-disjoint module regions and distinct module numbers.
- `reachable_no_adjacent_modules`: On every state reachable from `init_state`, two different module numbers are never adjacent by region, every module number has no neighbors and lies in no `module_triangles` entry, and `face_triangle_count` is 0.
- `reachable_flat_reading`: On every state reachable from `init_state`, every module number has mu-Laplacian 0, angle-defect curvature 2*PI, and calibration residual 2*PI.
- `reachable_calibrated_iff_no_modules`: A state reachable from `init_state` is calibrated at every module exactly when it has no modules.
- `reachable_triangulated_isolated`: A state reachable from `init_state` whose graph is well-formed triangulated has no interior edge, `B = E = V = 3F`, and Euler characteristic `F`.
- `reachable_triangulated_exists`: The state one PNEW of addresses 0, 1, 2 reaches from `init_state` is reachable, well-formed triangulated, has one face, and has Euler characteristic 1.
- `euler_component`: For a partition graph with distinct module identifiers, triangular regions, and every edge in one or two faces, whose modules are exactly those reachable from one module through shared edges, `V + F <= E + 2`, and `V + F <= E + 1` when some edge is on the boundary.
