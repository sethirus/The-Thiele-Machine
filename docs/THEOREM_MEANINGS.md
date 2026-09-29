# What each cited theorem says

Coq checks that a proof matches its statement. It does not check that the
name or the prose around a theorem means what the statement says. This file
closes that gap for every theorem the README, the monograph, the
mathematical specification, the technical disclosure, and
`THIELE_MACHINE.txt` cite. Each entry is one plain sentence saying what the
Coq statement asserts, premises included.

`tests/test_theorem_meanings.py` fails when a document cites a theorem that
has no entry here, or when an entry names a theorem that no longer exists.
The entries describe the current statements. Their accuracy requires reading
the quantified premises and conclusion; the gate checks coverage and names.
Where several modules use the same short name, the parenthesized qualified
name identifies the theorem meant by unqualified citations in these documents.
An explicitly qualified citation keeps its own module identity.

## Certification cost

- `universal_nfi_any_substrate`: In any `CertificationSystem`, whose record includes the rule that a step switching certification on costs at least one, a trace from an uncertified state to a certified one has total cost at least one.
- `abstract_nfi`: In an `AbstractCertMachine`, a trace that starts uncertified and ends certified contains an instruction in the cert-setter class.
- `cert_addr_setter_cost_pos`: Every VM instruction in the cert-setter class costs at least one.
- `no_free_certification`: A single VM step that moves `csr_cert_addr` from zero to nonzero has instruction cost at least one.
- `no_free_certification_certified`: A single VM step that switches `vm_certified` from false to true has instruction cost at least one.
- `certification_requires_positive_mu`: A single VM step that switches on either certification channel raises `vm_mu` by at least one.
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
- `history_core_equiv_thiele`: Under the dated Round 1 relation, the history-carrying core and the Thiele core cover each other's initial states and agree after every related step on certification, next-step cost, and the relation obtained by forgetting retained history.
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

## The ledger

- `run_writer_is_run_and_cost`: Running a trace in the writer monad over the natural numbers returns the state the trace reaches and the trace's total cost.
- `a2_iff_nonnegative_amortized_cost`: For any step function, cost, and yes/no reading, A2 holds exactly when every step's cost plus the change in the potential "one if uncertified, zero otherwise" is non-negative.
- `nfi_by_potential`: Under A2, a trace from an uncertified state to a certified one costs at least one, by the potential method's telescoping bound.
- `certification_system_is_potential_method`: Every `CertificationSystem` has non-negative amortized cost under the certification potential.

- `vm_apply_mu` (`Kernel.MuLedgerConservation.vm_apply_mu`): One VM step raises `vm_mu` by exactly the instruction's cost.
- `mu_is_initial_monotone` (`Kernel.MuInitiality.mu_is_initial_monotone`): A measure that is zero at the initial state and rises by the kernel's instruction cost on every step equals `vm_mu` on every reachable state.
- `instruction_consistent_measure_equals_mu` (`Kernel.MuInitiality.instruction_consistent_measure_equals_mu`): A measure that is zero at the initial state and rises by the instruction cost on every step equals `vm_mu` on every reachable state.
- `mu_is_universal` (`Kernel.MuInitiality.mu_is_universal`): Every `CostFunctional` record equals `vm_mu` on every reachable state.
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
- `D5_thiele_strictly_extends_classical`: Classical programs leave the graph, `csr_cert_addr`, and certification unchanged, and some VM step changes `pg_next_id` where no classical program from that state does.
- `thiele_simulates_turing`: Lifting a Turing configuration and running the file-local Thiele model for `n` steps gives the Turing machine's configuration after `n` steps.
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

## Categories

- `relational_compose_assoc` (`Kernel.CategoryLaws.relational_compose_assoc`): Relational composition of coupling relations is associative up to membership.
- `morph_graph_compose_assoc`: For three stored morphisms whose ends match, the two groupings of their coupling compositions agree up to membership.
- `graph_compose_morphisms_coupling`: A successful `COMPOSE` stores a morphism whose coupling is the other input's coupling when one input is an identity, and their relational composition otherwise.

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
- `column_contractive_iff_npa_psd`: Four correlators are column-contractive exactly when their zero-marginal NPA moment matrix is symmetric and PSD. (Renamed from `..._quantum_realizable`: PSD of this matrix is NPA's level-1 test, not quantum realizability.)
- `zero_marginal_npa_column_contractive_implies_psd`: The three column-contractivity inequalities imply the zero-marginal NPA matrix is PSD.
- `npa_psd_implies_column_contractive`: PSD of the zero-marginal NPA matrix implies column contractivity.
- `column_contractive_iff_general_realizable`: Column contractivity is equivalent to the dimension-generic PSD predicate at size five.
- `npa_psd_implies_tsirelson_bound`: If the zero-marginal NPA matrix is symmetric and PSD, the CHSH value squared is at most 8.
- `column_contractive_check_witness_sound`: If the integer witness check passes, the witness-derived correlators are column-contractive.
- `chsh_lassert_no_trap_implies_npa_psd`: A `CHSH_LASSERT` step that advances without setting the error flag implies the witness-derived zero-marginal NPA matrix is symmetric and PSD. (Renamed from `..._quantum_realizable`.)
- `chsh_lassert_1ab_no_trap_implies_npa_psd_q1ab`: A `CHSH_LASSERT_1AB` step that advances without error implies the 9 by 9 level-1+AB matrix at the witness correlators and zero higher moments is symmetric and PSD. (Renamed.)
- `state_column_contractive_implies_npa_gram`: A state whose correlators are column-contractive has a symmetric PSD zero-marginal NPA matrix. (Renamed from `..._quantum_gram`.)
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

## Hardware and extraction

- `driven_step_wf`: One Kami model step, read through the abstraction, equals `vm_apply` on the abstracted state whenever `WFDrivenPrecondition` holds.
- `driven_trace_commutes`: A fuel-bounded driven Kami run, read through the abstraction, equals the VM run whenever `WFDrivenRun` holds at every visited state.
- `driven_step_compose`: Under the extended hardware invariant, one Kami `COMPOSE` step equals the VM's `COMPOSE` step through the abstraction.
- `kami_register_write_matches_vm`: Writing a register in a Kami snapshot gives the same register list as `write_reg` on the abstracted state. (Renamed from `kami_refines_vm_step`: this is one register-write lemma, not step refinement.)
- `morph_table_wf_kami_step_preserved`: Every Kami step preserves morph-table well-formedness.
- `coupling_desc_safe_kami_step_preserved`: Every Kami step preserves coupling-descriptor safety.
- `coupling_wf_kami_step_preserved`: Every Kami step preserves coupling well-formedness, given coupling-descriptor safety.
- `fsm_retirement_refinement`: From a reset boundary state, every admitted run keeps the table invariants, ends at the snapshot the Kami run list computes, and is an actual multistep execution of the CPU core.
- `admitted_run_progress`: An admitted run from a boundary state reaches its end boundary in some number of rule runs, matches the Kami run list, and is an actual multistep execution.
- `rtl_inventory_arithmetic`: `37 + 10 + 0 = 47`. It records the synthesized-opcode count and checks no opcode. (Renamed from `rtl_coverage_partition`.)
- `rtl_gap_registry_empty`: The hand-written RTL gap list is empty. (Renamed from `rtl_gap_count`.)
- `ocaml_observable_nofi_and_monotone`: On the Coq-side observable the OCaml runner is tested against, certification costs at least one and mu never decreases. (Renamed from `ocaml_bisimulation_closure`, whose third part, totality, holds for any Coq function.)
- `ocaml_runner_observable_defined`: For every state and instruction, the Coq-side observable is defined. This is true of any Coq function; the binary's agreement is tested, not proved. (Renamed from `ocaml_runner_agrees`.)
- `receipt_encoding_roundtrip`: Unpacking a packed receipt returns its mu, certification bit, and memory.

## Physics files

- `full_efe_uniform_two_vertex`: For a uniform diagonal two-vertex metric, the computed curved Einstein tensor equals zero times the stress-energy, that is, zero. Both sides vanish; this does not derive general relativity.

## Models from other fields

- `quote_cannot_attest_unmeasured_state`: In the scoped TPM quote-field abstraction, whose quote authenticity is assumed externally rather than modeled, no function of the selected-PCR digest and nonce returns the additional runtime Boolean for every platform.
- `quote_decides_measured_claims`: In the same model, every supplied Boolean function of the retained selected-PCR digest is computed by some Boolean function of the quote.
- `quote_projection_faithful`: Two modeled quotes have equal classical-transcript encodings exactly when their nonce and retained selected-PCR digest agree.
- `quote_runtime_verifier_separation`: Any Boolean verifier that returns the modeled runtime claim on every full platform state fails to factor through the lossless encoding of its quote, by the named verifier corollary and an explicit truth-label adapter.

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
- `structural_trace_preserves_cert_addr`: An instruction-list run containing no certificate-address setter preserves the certificate address.
- `graph_certify_morphism_lookup`: If a morphism lookup succeeds, certifying that morphism makes the same lookup return the same fields with its certification cost replaced by the supplied cost.
- `forget_kernel_is_eq_on_classical`: Two VM states have equal `forget` projections exactly when they agree on the fields in `eq_on_classical`.
- `blindness_non_injective`: Two distinct VM states have the same `forget` projection.
- `certification_is_lost`: Two VM states have the same `forget` projection and different certification flags.
- `mu_ledger_necessity` (`NecessityOfMuLedger.mu_ledger_necessity`): No function of the strict memory-register-PC projection recovers both mu and certification on every VM state.
- `vm_mu_not_classically_determined` (`NecessityOfMuLedger.vm_mu_not_classically_determined`): No function of the strict memory-register-PC projection recovers mu on every VM state.
- `vm_certified_not_classically_determined` (`NecessityOfMuLedger.vm_certified_not_classically_determined`): No function of the strict memory-register-PC projection recovers certification on every VM state.
- `vm_apply_certify_strict_shadow` (`NecessityOfMuLedger.vm_apply_certify_strict_shadow`): CERTIFY preserves memory and registers and increments PC in the strict projection.
- `vm_apply_pnew_strict_shadow` (`NecessityOfMuLedger.vm_apply_pnew_strict_shadow`): PNEW preserves memory and registers and increments PC in the strict projection.
- `mu_ledger_necessity_universal`: From every VM state, CERTIFY 0 and PNEW [] 0 produce the same strict projection, while CERTIFY adds one to mu and sets certification and PNEW preserves mu.
- `po1_trace_necessity`: Appending CERTIFY 0 or PNEW [] 0 to any instruction-list prefix from `po1_init` gives equal strict projections and strictly greater mu in the CERTIFY case.
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
- `D4_strictness`: Some VM instruction changes the graph's next-module identifier from a state where every classical instruction-list run preserves that identifier.
- `nat_recursion_theorem`: For the candidate-decider-dependent nat substrate, every transformer selected by its representability predicate has a code whose total run equals the transformer's image on every input state.

## Information and witness contracts

- `feasible_strict_subset_implies_strict_predicates`: A strict feasible subset and an excluded prior state whose observation differs from every posterior observation make the induced posterior receipt predicate strictly stronger.
- `b4_information_reduction_derives_strict_predicates`: With a correct Boolean equality test on observations, a strict feasible subset and a distinguishing excluded state yield two receipt predicates with strict strengthening.
- `strengthening_requires_structure_addition` (`Kernel.NoFreeInsight.NoFreeInsight.strengthening_requires_structure_addition`): If a strictly stronger receipt predicate is certified after a bounded run from certificate address zero, that run contains a structure-addition event.
- `info_priced_cert_executions_bound`: The number of executed certificate setters in a bounded VM run is at most its mu increment.
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
- `chsh_trial_not_cert_addr_setter`: Every CHSH_TRIAL instruction is outside the certificate-address setter class.
- `chsh_trial_preserves_vm_certified`: Every CHSH_TRIAL step preserves the VM certification flag.
- `certified_witness_insight_nonfree`: A step satisfying the defined witness-insight event costs at least one and raises mu by at least one.
- `nonlocal_witness_insight_nonfree`: A step from an uncertified state to a state with a certified nonlocal witness costs at least one and raises mu by at least one.
- `witness_insight_nonfree_general`: An instruction-list run from uncertified to certified with a certified CHSH violation raises mu by at least one.
- `witness_insight_complete_taxonomy`: CHSH_TRIAL is never a certification-insight event, every such event costs at least one, and a trace from uncertified to a certified CHSH violation raises mu by at least one.
- `compression_priced_trace_floor`: On an enumerated finite state space with permanent certification and compression pricing, an instruction-list run from uncertified to certified costs at least one.
- `priced_reset_satisfies_premises`: The two-state Blank/Stamped machine is finite, keeps its stamp permanently, and prices every merging step at one.
- `step_price_is_exact`: The defined full-state certification-flip indicator price meets the flip floor and never overcharges.
- `categorical_extension_nofi_consistent`: Every MORPH_ASSERT instruction is in the certificate-setter class and has positive cost.
- `locally_consistent_gives_separable_coupling`: A witness tally consistent with the supplied four local deterministic outputs induces a separable setting-outcome coupling.

## Replicated-record examples

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

## Scalar physics and geometry contracts

- `zero_mu_traces_satisfy_preservation_budget`: If each input has a bounded error-free zero-mu trace, every Boolean state predicate satisfies `error_free_preservation_budget` with mu bound zero because its positive-mu antecedent is false.
- `tsirelson_rational_lower_witness`: Some correlator satisfying the selected rational coherence predicate has CHSH at least 28284/10000.
- `zero_cost_preserves_radius` (`Kernel.Unitarity.zero_cost_preserves_radius`): If both radius-loss and radius-gain inequalities are supplied and formal cost is zero, the evolution preserves squared radius on the unit ball.
- `ball_trace_contract_from_premises`: Positivity and trace preservation supply the defined scalar ball-and-trace contract, with no assertion of complete positivity for operators.
- `master_tsirelson_conditional` (`PhysicsConditionalClosure.master_tsirelson_conditional`): Under the section's physical quantum bridge, correlations satisfying its honest-quantum predicate have absolute CHSH value at most the defined square root of eight.
- `no_cloning_from_conservation` (`Kernel.NoCloning.no_cloning_from_conservation`): A nontrivial input, the scalar conservation inequality, and a perfect-copy operation imply that the operation's formal cost is nonzero.
- `no_cloning_bloch` (`Kernel.NoCloning.no_cloning_bloch`): For a radius-one input whose squared radius equals the operation's input-information field, scalar conservation and perfect copying imply formal cost at least one.
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
- `embed_step_compute`: For instructions outside the sixteen explicitly excluded structural, call/return, witness, tensor, and morphism opcode cases, abstracting the intermediate Kami step equals applying the VM step to the abstraction.
- `five_labeled_models_have_selected_pointer`: In the five synthetic labelled mirror models, each selected flag is returned by every stipulated observer and its named rival is not.
