# Thiele Machine - Coq Proofs

**Mission:** Main Thiele Machine proofs including Bell inequality verification, deliverables, and machine semantics.

## Structure

- `AbstractLTS.v` - Abstract LTS - Defines: StateRec, InstructionType, Trace (+1 more); Key results: partition_wellformed, step_deterministic, module_independence (+19 more)
- `AlgebraicLaws.v` - Algebraic Laws - Key results: region_merge_associative, pmerge_associativity, run_identity (+3 more)
- `AmortizedAnalysis.v` - Amortized Analysis - Defines: Instance, Partition; Key results: basic_amortization, amortization_improves_with_reuse, practical_amortization_bounds (+1 more)
- `Axioms.v` - Axioms - Key results: tm_iterate_pc, decode_encode_id, utm_catalogue_static_check (+5 more)
- `BellArtifacts.v` - Bell Artifacts - Key results: csv_supra_quantum_p_nonneg, csv_supra_quantum_p_norm, csv_supra_quantum_p_nosig_A (+5 more)
- `BellCheck.v` - Bell Check - Defines: SettingAggregate, BellSummary; Key results: classical_gap_plus, violation_margin_plus, Qle_plus_nonneg (+5 more)
- `BellInequality.v` - Bell Inequality - Defines: Bit, Box, Response (+4 more); Key results: eqb_eq, eqb_neq, bit_to_nat_roundtrip (+207 more)
- `BellReceiptLocalBound.v` - Bell Receipt Local Bound - Key results: local_fragment_CHSH_le_2_end_to_end
- `BellReceiptLocalGeneral.v` - Bell Receipt Local General - Key results: bit_eqb_refl, bit_eqb_eq, B0_neq_B1 (+11 more)
- `BellReceiptSemantics.v` - Bell Receipt Semantics - Defines: Trial
- `BellReceiptSoundness.v` - Bell Receipt Soundness - Key results: is_bit_nat_true_cases, andb4_true, trial_of_metadata_cert_for_chsh_trial (+3 more)
- `Bisimulation.v` - Bisimulation
- `BlindSighted.v` - Blind Sighted - Defines: Partition, MuLedger, ThieleState (+2 more); Key results: TM_as_BlindThiele, Blind_is_restriction_of_Sighted
- `CompositionPrimitive.v` - Composition Primitive - Key results: no_independent_global_semantics, meaning_preserved_under_composition
- `ComputationIsomorphism.v` - Computation Isomorphism - Key results: execution_is_computable, classical_embedding, cost_model_divergence
- `Confluence.v` - Confluence - Key results: independent_steps_confluence
- `CoreSemantics.v` - Core Semantics - Defines: Partition, MuLedger, Instruction (+1 more); Key results: region_eqb_refl, find_module_in_list_app, add_module_preserves (+20 more)
- `DiscoveryProof.v` - Discovery Proof - Defines: Problem, PartitionCandidate; Key results: eigen_complexity, count_occ_nat_eq, count_occ_seq_in_range (+23 more)
- `DissipativeEmbedding.v` - Dissipative Embedding - Key results: encoded_modules_length, decode_modules_encoded, decode_encode_id (+4 more)
- `EfficientDiscovery.v` - Efficient Discovery - Defines: Problem, PartitionCandidate, MuLedger; Key results: covers_range_trivial_range_partition, discovery_polynomial_time, discovery_produces_valid_partition_spec (+6 more)
- `Embedding_TM.v` - Embedding TM - Key results: tm_embeds, space_overhead_linear, thiele_is_turing_complete (+1 more)
- `EncodingBridge.v` - Encoding Bridge - Key results: tm_decode_encode_roundtrip
- `GoldenVectors.v` - Golden Vectors - Definitions: golden1_state, golden1_encoding, golden1_hash (+10 more)
- `HardwareBridge.v` - Hardware Bridge - Defines: RTLState; Key results: rtl_step_preserves_program, decode_program_nth
- `HardwareVMHarness.v` - Hardware VMHarness - Key results: rtl_mu_conservation, rtl_irreversibility_lower_bound
- `Hash256.v` - Hash256 - Definitions: modulus, mix, fold_mix (+3 more)
- `HyperThiele.v` - Hyper Thiele - Defines: InstrKind, Instr, Prog (+2 more)
- `HyperThiele_Halting.v` - Hyper Thiele Halting
- `HyperThiele_Oracle.v` - Hyper Thiele Oracle - Defines: Cmd; Key results: compile_preserves_oracle_outputs
- `Impossibility.v` - Impossibility - Defines: ProbabilisticTM, PTMArchitecture; Key results: PTM_strategy_realizes, PTM_CHSH_expectation_unfold, impossibility_of_re_encoding
- `InfoTheory.v` - Info Theory - Key results: question_cost_nonnegative, log2_monotonic, mu_bounds_shannon_entropy (+6 more)
- `LawCheck.v` - Law Check - Defines: UpdateCoefficients, LagrangianCoefficients, LawSummary
- `ListHelpers.v` - List Helpers
- `LogicIsomorphism.v` - Logic Isomorphism - Defines: ThieleProp, ThieleProof; Key results: proof_is_execution, proof_equivalence
- `MuAlignmentExample.v` - Mu Alignment Example - Key results: test_clause_size, lassert_xor_mu_cost, lassert_mu_cost_formula (+1 more)
- `MuAlu.v` - Mu Alu - Defines: MuAccumulator; Key results: q16_add_comm, q16_add_zero, saturate_idempotent
- `NUSD.v` - NUSD - Key results: app_rev_singleton, rev_rev
- `Oracle.v` - Oracle - Defines: T1_State, T1_Receipt, T1_ReceiptWitness (+1 more); Key results: t1_bootstrap_total_zero, ledger_sum_app_singleton, t1_charge_mu_total (+37 more)
- `OracleImpossibility.v` - Oracle Impossibility - Defines: TMState; Key results: halts_or_not
- `PartitionDiscoveryIsomorphism.v` - Partition Discovery Isomorphism - Defines: VariableGraph, Partition, DiscoveryResult (+1 more); Key results: spectral_produces_valid, implementation_produces_valid, spectral_is_polynomial (+1 more)
- `PartitionLogic.v` - Partition Logic - Defines: Partition, LocalWitness, GlobalWitness; Key results: Permutation_length_eq, fold_left_add_zeros, sum_const_zero (+7 more)
- `PhaseThree.v` - Phase Three - Defines: HeadToHeadSummary; Key results: Qlt_plus_pos, head_to_head_gap_cancel, head_to_head_gap_implies_better
- `PhysicsEmbedding.v` - Physics Embedding - Key results: lattice_encoded_modules_length, decode_cell_from_lattice_cell, lattice_decode_encoded (+8 more)
- `QHelpers.v` - QHelpers - Key results: Qeq_cross_mul, Qeq_le_compat, Qeq_lt_compat (+1 more)
- `QuantumAdmissibilityDeliverableB.v` - Quantum Admissibility Deliverable B - Key results: admissible_generator_implies_CHSH_le_kernel_bound, TsirelsonApprox_gap_to_kernel_bound
- `QuantumAdmissibilityTsirelson.v` - Quantum Admissibility Tsirelson - Key results: two_le_kernel_tsirelson_bound, quantum_admissible_implies_CHSH_le_tsirelson
- `QuantumTheorems.v` - Quantum Theorems - Key results: superposition_emergence, interference_emergence, entanglement_emergence (+2 more)
- `RepresentationTheorem.v` - Representation Theorem - Key results: gauge_preserved_by_step, gauge_trace_preservation, instr_to_label_injective (+1 more)
- `SemanticBridge.v` - Semantic Bridge - Key results: partition_conversion_roundtrip, ledger_conversion_roundtrip, state_correspondence (+3 more)
- `Separation.v` - Separation - Defines: ExpanderGraph, TseitinInstance; Key results: thiele_sighted_steps_polynomial_forall_Z, thiele_mu_cost_quadratic_forall_Z, thiele_sighted_steps_polynomial_forall (+2 more)
- `Simulation.v` - Simulation - Key results: decode_encode_id_tm, utm_program_blind, all_steps_ok_tail (+2 more)
- `Spaceland.v` - Spaceland - Defines: Label, Spaceland, Morphism (+1 more)
- `SpacelandComplete.v` - Spaceland Complete - Defines: Label, step, Trace; Key results: step_det, mu_nonneg, valid_trace_cons (+14 more)
- `SpacelandCore.v` - Spaceland Core - Defines: Label, Trace, Label (+1 more); Key results: mu_cost_nonneg, step_det, mu_nonneg (+5 more)
- `SpacelandProved.v` - Spaceland Proved - Defines: Label, step, Trace; Key results: step_det, mu_nonneg, mu_blind (+5 more)
- `Spaceland_Simple.v` - Spaceland Simple - Defines: Label, Trace, Receipt
- `SpecSound.v` - Spec Sound - Defines: ProofArtifact, ProblemType, CoreState (+5 more); Key results: Soundness_aux, Soundness_receipts, Completeness_receipts (+2 more)
- `SpectralApproximation.v` - Spectral Approximation - Key results: sumR_ext, sum_nat_ext, sumR_const (+19 more)
- `StructuredInstances.v` - Structured Instances - Defines: partition_type; Key results: tseitin_speedup_example, linear_structure_discovery, modular_circuit_speedup (+2 more)
- `Subsumption.v` - Subsumption - Key results: turing_strictly_contained_in_thiele
- `ThieleFoundations.v` - Thiele Foundations - Defines: TuringMachine, CoreThieleMachine, Configuration (+2 more); Key results: 1, Turing_Embedding_Properties, Semantic_Strictness (+1 more)
- `ThieleKernelCausality.v` - Thiele Kernel Causality - Defines: PDiscoverNot; Key results: no_superluminal_influence_pdiscover_trace, graph_lookup_add_module_other, graph_lookup_remove_modules_other (+6 more)
- `ThieleMachine.v` - Thiele Machine - Defines: CSR, InstrKind, Instr (+6 more); Key results: option_event_eqb_refl, cert_eqb_refl, option_event_eqb_eq (+12 more)
- `ThieleMachineConcrete.v` - Thiele Machine Concrete - Defines: ThieleInstr, ThieleEvent, ConcreteState (+5 more); Key results: cert_for_query_metadata_empty, cert_for_pyexec_metadata_empty, chsh_metadata_only_from_chsh_trial (+17 more)
- `ThieleMachineConcretePack.v` - Thiele Machine Concrete Pack
- `ThieleMachineModular.v` - Thiele Machine Modular
- `ThieleMachineSig.v` - Thiele Machine Sig - Defines: StepObs; Key results: check_step_sound, mu_lower_bound, check_step_complete (+1 more)
- `ThieleMachineUniv.v` - Thiele Machine Univ
- `ThieleProc.v` - Thiele Proc - Defines: Interface, Category; Key results: seq_prog_nil_l, seq_prog_nil_r, seq_prog_assoc (+16 more)
- `ThieleProofCarryingReality.v` - Thiele Proof Carrying Reality - Key results: concrete_exec_trace_of, supra_quantum_receipts_replay_ok
- `ThieleSpaceland.v` - Thiele Spaceland - Defines: Trace, Receipt, StepWitness (+3 more); Key results: partition_wellformed, LCompute_not_LSplit, LCompute_not_LMerge (+34 more)
- `ThieleUnificationDemo.v` - Thiele Unification Demo - Definitions: init_csrs, init_vm, trace
- `ThieleUnificationProtocol.v` - Thiele Unification Protocol - Key results: run_functorial, mu_monotone, mu_ledger_conservation (+5 more)
- `ThieleUnificationTensor.v` - Thiele Unification Tensor - Key results: pg_next_id_graph_add_axiom, pg_next_id_graph_add_axioms, graph_lookup_insert_modules_same (+5 more)
- `TsirelsonBoundBridge.v` - Tsirelson Bound Bridge - Key results: TsirelsonApprox_Qabs_le_kernel_bound
- `UTMStaticCheck.v` - UTMStatic Check - Key results: utm_catalogue_static_check_proved
- `WaveCheck.v` - Wave Check - Defines: WaveCoefficients, WavePDEParams, WaveSummary; Key results: wave_coeffs_symmetric, wave_coeffs_match, standard_wave_verified (+1 more)
- `WaveEmbedding.v` - Wave Embedding - Key results: decode_cell_from_wave_cell, wave_decode_encoded, wave_decode_encode_id (+6 more)

## Verification Status

| File | Admits | Status |
|:---|:---:|:---:|
| `AbstractLTS.v` | 0 | ✅ |
| `AlgebraicLaws.v` | 0 | ✅ |
| `AmortizedAnalysis.v` | 0 | ✅ |
| `Axioms.v` | 0 | ✅ |
| `BellArtifacts.v` | 0 | ✅ |
| `BellCheck.v` | 0 | ✅ |
| `BellInequality.v` | 0 | ✅ |
| `BellReceiptLocalBound.v` | 0 | ✅ |
| `BellReceiptLocalGeneral.v` | 0 | ✅ |
| `BellReceiptSemantics.v` | 0 | ✅ |
| `BellReceiptSoundness.v` | 0 | ✅ |
| `Bisimulation.v` | 0 | ✅ |
| `BlindSighted.v` | 0 | ✅ |
| `CompositionPrimitive.v` | 0 | ✅ |
| `ComputationIsomorphism.v` | 0 | ✅ |
| `Confluence.v` | 0 | ✅ |
| `CoreSemantics.v` | 0 | ✅ |
| `DiscoveryProof.v` | 0 | ✅ |
| `DissipativeEmbedding.v` | 0 | ✅ |
| `EfficientDiscovery.v` | 0 | ✅ |
| `Embedding_TM.v` | 0 | ✅ |
| `EncodingBridge.v` | 0 | ✅ |
| `GoldenVectors.v` | 0 | ✅ |
| `HardwareBridge.v` | 0 | ✅ |
| `HardwareVMHarness.v` | 0 | ✅ |
| `Hash256.v` | 0 | ✅ |
| `HyperThiele.v` | 0 | ✅ |
| `HyperThiele_Halting.v` | 0 | ✅ |
| `HyperThiele_Oracle.v` | 0 | ✅ |
| `Impossibility.v` | 0 | ✅ |
| `InfoTheory.v` | 0 | ✅ |
| `LawCheck.v` | 0 | ✅ |
| `ListHelpers.v` | 0 | ✅ |
| `LogicIsomorphism.v` | 0 | ✅ |
| `MuAlignmentExample.v` | 0 | ✅ |
| `MuAlu.v` | 0 | ✅ |
| `NUSD.v` | 0 | ✅ |
| `Oracle.v` | 0 | ✅ |
| `OracleImpossibility.v` | 0 | ✅ |
| `PartitionDiscoveryIsomorphism.v` | 0 | ✅ |
| `PartitionLogic.v` | 0 | ✅ |
| `PhaseThree.v` | 0 | ✅ |
| `PhysicsEmbedding.v` | 0 | ✅ |
| `QHelpers.v` | 0 | ✅ |
| `QuantumAdmissibilityDeliverableB.v` | 0 | ✅ |
| `QuantumAdmissibilityTsirelson.v` | 0 | ✅ |
| `QuantumTheorems.v` | 0 | ✅ |
| `RepresentationTheorem.v` | 0 | ✅ |
| `SemanticBridge.v` | 0 | ✅ |
| `Separation.v` | 0 | ✅ |
| `Simulation.v` | 0 | ✅ |
| `Spaceland.v` | 0 | ✅ |
| `SpacelandComplete.v` | 0 | ✅ |
| `SpacelandCore.v` | 0 | ✅ |
| `SpacelandProved.v` | 0 | ✅ |
| `Spaceland_Simple.v` | 0 | ✅ |
| `SpecSound.v` | 0 | ✅ |
| `SpectralApproximation.v` | 0 | ✅ |
| `StructuredInstances.v` | 0 | ✅ |
| `Subsumption.v` | 0 | ✅ |
| `ThieleFoundations.v` | 0 | ✅ |
| `ThieleKernelCausality.v` | 0 | ✅ |
| `ThieleMachine.v` | 0 | ✅ |
| `ThieleMachineConcrete.v` | 0 | ✅ |
| `ThieleMachineConcretePack.v` | 0 | ✅ |
| `ThieleMachineModular.v` | 0 | ✅ |
| `ThieleMachineSig.v` | 0 | ✅ |
| `ThieleMachineUniv.v` | 0 | ✅ |
| `ThieleProc.v` | 0 | ✅ |
| `ThieleProofCarryingReality.v` | 0 | ✅ |
| `ThieleSpaceland.v` | 0 | ✅ |
| `ThieleUnificationDemo.v` | 0 | ✅ |
| `ThieleUnificationProtocol.v` | 0 | ✅ |
| `ThieleUnificationTensor.v` | 0 | ✅ |
| `TsirelsonBoundBridge.v` | 0 | ✅ |
| `UTMStaticCheck.v` | 0 | ✅ |
| `WaveCheck.v` | 0 | ✅ |
| `WaveEmbedding.v` | 0 | ✅ |

**Result:** All 78 files verified with 0 admits.
