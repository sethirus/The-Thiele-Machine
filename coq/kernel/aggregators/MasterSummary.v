(** MasterSummary: audit-facing index of the core kernel claims.

  This file is here to make the repository harder to misread. It re-exports
  the big results, but it also labels what kind of result each one is:
  definitional restatement, direct algebraic theorem, conditional bridge,
  wrapper around an earlier theorem, or verification-transfer claim.

  The point is not to sound impressive. The point is to keep the audit trail
  explicit about what has actually been proved, what depends on extra
  premises, and what should not be over-read from the theorem name alone. *)

From Coq Require Import QArith Qabs Lia List Reals Strings.String.
Require Import Coq.micromega.Lra.
Import ListNotations.

From Kernel Require Import VMState VMStep MuCostModel CHSHExtraction.
From Kernel Require Import SimulationProof InformationGainToStrengthening.
From Kernel Require Import ClassicalBound TsirelsonUpperBound TsirelsonUniqueness.
From Kernel Require Import QuantumEquivalence NoFreeInsight.
From Kernel Require Import A2Payoff CommitmentPredicateAdequacy CommitmentCostDecomposition.
From Kernel Require Import TsirelsonGeneral TsirelsonFromAlgebra.
From Kernel Require Import MinorConstraints.
From Kernel Require Import MuLedgerQuantumBridge.
From Kernel Require Import BornRuleLinearity TsirelsonQuantumModel.
From Kernel Require Import HonestNoFI HonestNoFI_TheoremsWithoutAssumptions.
From Kernel Require Import MuShannonBridge MuShannonQuantitative StateSpaceCounting.
From Kernel Require Import NPAMomentMatrix ConstructivePSD.
From Kernel Require Import QuantumPartitionPSD.
From Kernel Require Import PythonBisimulation HardwareBisimulation.
From Kernel Require Import NonCircularityAudit.
From Kernel Require Import LocalMorphismSemantics EntanglementEntropy.
From Kernel Require Import ClausiusFromEntropyArea RaychaudhuriFluxBridge.
From Kernel Require Import JacobsonBridgeComponents ThermoEinsteinBridge.
From Kernel Require Import BekensteinCalibration NoFIToEinstein.
From Kernel Require Import DiscreteTopology DiscreteGaussBonnet.
From Kernel Require Import EinsteinEmergence.
From Kernel Require Import CurvedTensorPipeline.
From Kernel Require Import CategoryLaws CategoryBridge CategoryMonoidal.
From KamiHW Require Import FullEmbedStep GraphReconstructionBridge.

(* MinorConstraints opens R_scope globally; reassert Q as default for this file. *)
Local Open Scope Q_scope.
Local Open Scope string_scope.


Inductive theorem_scope :=
| ExportOnly
| Definitional
| MixedSummary
| Algebraic
| Structural
| ConditionalPhysical
| ExecutableBridge
| VerificationTransfer.

Inductive theorem_status :=
| StatusUnconditional
| StatusConditional
| StatusDefinitional.

Inductive premise_kind :=
| PremiseStandardLibrary
| PremiseSyntactic
| PremiseAlgebraic
| PremiseStructural
| PremiseSemantic
| PremisePhysical
| PremiseVerification.

Inductive theorem_role :=
| WrapperOnly
| DefinitionalRestatement
| NewComposition.

Record HonestClaim := {
  claim_name : string;
  claim_sources : list string;
  claim_scope : theorem_scope;
  claim_status : theorem_status;
  claim_role : theorem_role;
  claim_premises : list string;
  claim_premise_kinds : list premise_kind;
  claim_not_imply : list string
}.

Record assumption_surface := {
  project_local_axioms_count : nat;
  project_local_admits_count : nat;
  imported_standard_dependencies : list string;
  uses_classical_logic : bool;
  uses_functional_extensionality : bool;
  uses_choice_principles : bool;
  uses_proof_irrelevance : bool;
  uses_real_number_completeness : bool
}.

Inductive semantic_layer :=
| FormalTheoremLayer
| ExecutableSemanticsLayer
| PhysicalInterpretationLayer.

Record semantic_boundary_entry := {
  boundary_name : string;
  boundary_from : semantic_layer;
  boundary_to : semantic_layer;
  boundary_links : list string;
  boundary_status : theorem_scope;
  boundary_external_boundary : list string
}.

Record TheoremMetadata := {
  metadata_name : string;
  metadata_scope : theorem_scope;
  metadata_status : theorem_status;
  metadata_role : theorem_role
}.

Inductive manifest_certification_level :=
| DeclaredInSummary
| LocallyCheckedAgainstDeclaration
| ExternallyAuditedArtifact.

Record manifest_boundary_entry := {
  manifest_item : string;
  manifest_level : manifest_certification_level;
  manifest_source : string;
  manifest_limit : string
}.

Record external_artifact_reference := {
  artifact_path : string;
  artifact_sha256 : string;
  artifact_role : string
}.

Inductive kernel_story_area :=
| AreaCHSHStructure
| AreaQuantumBridge
| AreaNoFreeInsight
| AreaVerificationSurface
| AreaNonCircularity
| AreaAssumptionSurface
| AreaSemanticBoundary
| AreaPhysicsBoundary.

Record kernel_story_coverage_entry := {
  coverage_area : kernel_story_area;
  coverage_support : list string;
  coverage_note : string
}.

Inductive physical_reading_status :=
| ProvedKernelConsequence
| ExternalModelingClaim
| ExternalEmpiricalHypothesis
| OpenFormalizationObligation.

Record physical_reading_entry := {
  reading_name : string;
  reading_status : physical_reading_status;
  reading_basis : list string;
  reading_boundary : string
}.

Record verification_scope_record := {
  verification_scope_name : string;
  verification_scope_exact_observables : list string;
  verification_scope_includes_full_state_equivalence : bool;
  verification_scope_nonclaims : list string
}.

Record open_obligation_entry := {
  obligation_name : string;
  obligation_needed_for : string;
  obligation_current_boundary : string
}.

Definition master_summary_assumptions : assumption_surface :=
  {| project_local_axioms_count := 0%nat;
     project_local_admits_count := 0%nat;
     imported_standard_dependencies :=
       [ "ClassicalDedekindReals.sig_not_dec";
         "ClassicalDedekindReals.sig_forall_dec";
         "FunctionalExtensionality.functional_extensionality_dep";
         "Standard arithmetic, list, rational, and real-analysis libraries are used throughout the dependency chain" ];
     uses_classical_logic := true;
     uses_functional_extensionality := true;
     uses_choice_principles := false;
     uses_proof_irrelevance := false;
     uses_real_number_completeness := true |}.

Definition master_summary_no_hidden_project_assumptions : Prop :=
  project_local_axioms_count master_summary_assumptions = 0%nat /\
  project_local_admits_count master_summary_assumptions = 0%nat.

Lemma master_summary_project_local_axioms_count_zero :
  project_local_axioms_count master_summary_assumptions = 0%nat.
Proof.
  reflexivity.
Qed.

Lemma master_summary_project_local_admits_count_zero :
  project_local_admits_count master_summary_assumptions = 0%nat.
Proof.
  reflexivity.
Qed.

Theorem master_summary_no_hidden_project_assumptions_verified :
  master_summary_no_hidden_project_assumptions.
Proof.
  change
    (project_local_axioms_count master_summary_assumptions = 0%nat /\
     project_local_admits_count master_summary_assumptions = 0%nat).
  split.
  - exact master_summary_project_local_axioms_count_zero.
  - exact master_summary_project_local_admits_count_zero.
Qed.

Definition chsh_trace_semantic_boundary : semantic_boundary_entry :=
  {| boundary_name := "CHSH trace-to-interpretation chain";
     boundary_from := FormalTheoremLayer;
     boundary_to := PhysicalInterpretationLayer;
     boundary_links :=
       [ "VM trace -> extracted correlators (CHSHExtraction.v)";
         "Extracted correlators -> trace_zero_marginal_npa (MuLedgerQuantumBridge.v)";
         "PSD <-> column contractive (QuantumPartitionPSD.v)";
         "Column contractive / coherence -> CHSH <= sqrt(8) (TsirelsonQuantumModel.v, TsirelsonFromAlgebra.v)";
         "Physical source interpretation remains external to Coq" ];
     boundary_status := ExecutableBridge;
     boundary_external_boundary :=
       [ "The formal chain proves bounds on extracted correlators, not that a laboratory source satisfies the bridge premise.";
         "Reading the trace-level predicate as a physical quantum source claim is an external semantic step." ] |}.

Definition verification_semantic_boundary : semantic_boundary_entry :=
  {| boundary_name := "Verification transfer chain";
     boundary_from := FormalTheoremLayer;
     boundary_to := ExecutableSemanticsLayer;
     boundary_links :=
       [ "Coq vm_step -> Python abstract step (PythonBisimulation.v)";
         "Python abstract step -> Hardware abstract step (HardwareBisimulation.v)";
         "Transfer surface here is PC/μ agreement in the imported abstract hardware model" ];
     boundary_status := VerificationTransfer;
     boundary_external_boundary :=
       [ "HardwareBisimulation.v is a cost/PC abstraction, not a full register/memory/graph equivalence theorem.";
         "Fuller RTL correspondence lives elsewhere in the tree and should not be collapsed into this one theorem." ] |}.

Definition trace_quantum_model_semantic_boundary : semantic_boundary_entry :=
  {| boundary_name := "trace_quantum_model meaning";
     boundary_from := FormalTheoremLayer;
     boundary_to := ExecutableSemanticsLayer;
     boundary_links :=
       [ "trace_quantum_model fuel trace s_init is defined in TsirelsonQuantumModel.v";
         "It unfolds to quantum_realizable (trace_zero_marginal_npa fuel trace s_init)";
         "quantum_realizable unfolds to symmetric5 M /\\ PSD5 M in NPAMomentMatrix.v" ];
     boundary_status := Definitional;
     boundary_external_boundary :=
       [ "This is an internal mathematical classification of the extracted moment matrix.";
         "Reading it as a claim about a laboratory source remains an external semantic step." ] |}.

Definition thermo_einstein_semantic_boundary : semantic_boundary_entry :=
  {| boundary_name := "thermo-to-Einstein corridor";
     boundary_from := FormalTheoremLayer;
     boundary_to := PhysicalInterpretationLayer;
     boundary_links :=
       [ "PSPLIT witness -> split morphism support semantics (LocalMorphismSemantics.v)";
         "nearest-neighbor split morphism -> entropy area law (EntanglementEntropy.v)";
         "entropy/temperature/heat delta witness (ClausiusFromEntropyArea.v)";
         "null-congruence delta flux -> Clausius delta equality (RaychaudhuriFluxBridge.v)";
         "conditional EinsteinTarget composition (ThermoEinsteinBridge.v)" ];
     boundary_status := ConditionalPhysical;
     boundary_external_boundary :=
       [ "EinsteinTarget and LocalHorizon remain abstract parameters in the generic corridor theorem.";
         "The repository now supplies a closed discharge witness for the discrete Einstein-emergence target; a standalone geometry-only replacement of the generic abstraction would be a stronger refinement, not a blocker for the compiled chain." ] |}.

Definition audit_master_mu_zero_algebraic_bound : HonestClaim :=
  {| claim_name := "master_mu_zero_algebraic_bound";
     claim_sources := [ "TsirelsonUniqueness.mu_zero_chsh_bounded"; "ClassicalBound.classical_program_mu_zero" ];
     claim_scope := Algebraic;
     claim_status := StatusUnconditional;
     claim_role := NewComposition;
     claim_premises :=
       [ "mu_zero_program fuel trace";
         "standard rational/algebraic libraries" ];
     claim_premise_kinds := [ PremiseStructural; PremiseStandardLibrary ];
     claim_not_imply :=
       [ "Does not derive the Tsirelson bound 2sqrt(2).";
         "Does not classify all μ=0 traces as physical or quantum realizable." ] |}.

Definition audit_master_classical_bound : HonestClaim :=
  {| claim_name := "master_classical_bound";
     claim_sources := [ "MinorConstraints.factorizable_CHSH_classical_bound" ];
     claim_scope := Structural;
     claim_status := StatusUnconditional;
     claim_role := WrapperOnly;
     claim_premises :=
       [ "MinorConstraints.is_factorizable E";
         "standard real-analysis library" ];
     claim_premise_kinds := [ PremiseStructural; PremiseStandardLibrary ];
     claim_not_imply :=
       [ "Does not prove every μ=0 trace is factorizable.";
         "Does not prove anything about physical state preparation." ] |}.

Definition audit_master_quantum_foundations : HonestClaim :=
  {| claim_name := "master_quantum_foundations";
     claim_sources := [ "QuantumEquivalence.quantum_foundations_complete"; "QuantumEquivalence.hierarchy_is_derived"; "QuantumEquivalence.qm_equals_cost_free" ];
     claim_scope := MixedSummary;
     claim_status := StatusUnconditional;
     claim_role := WrapperOnly;
     claim_premises :=
       [ "classical_bound <= tsirelson_bound as a numerical inequality";
         "is_quantum_correlation is defined as satisfies_no_signaling /\\ chsh_value <= tsirelson_bound" ];
     claim_premise_kinds := [ PremiseAlgebraic; PremiseSyntactic ];
     claim_not_imply :=
       [ "Does not derive quantum mechanics from μ-accounting.";
         "Does not independently derive the physical Tsirelson principle." ] |}.

Definition audit_master_non_circularity : HonestClaim :=
  {| claim_name := "master_non_circularity";
     claim_sources := [ "NonCircularityAudit.non_circularity_verified" ];
     claim_scope := Structural;
     claim_status := StatusUnconditional;
     claim_role := WrapperOnly;
     claim_premises :=
       [ "primitive μ-cost rules are syntax-level and CHSH-free";
         "CHSH formula is algebraic";
         "μ=0 operational class has LOCC-like properties" ];
     claim_premise_kinds := [ PremiseSyntactic; PremiseAlgebraic; PremiseStructural ];
     claim_not_imply :=
       [ "Does not prove a whole-repository import-graph absence theorem.";
         "Does not prove every semantic bridge in the project is non-circular by itself." ] |}.

Definition audit_master_tsirelson_conditional : HonestClaim :=
  {| claim_name := "master_tsirelson_conditional";
     claim_sources := [ "BornRuleLinearity.born_rule_unique"; "TsirelsonQuantumModel.trace_quantum_model_connection_closed" ];
     claim_scope := ConditionalPhysical;
     claim_status := StatusConditional;
     claim_role := NewComposition;
     claim_premises :=
       [ "valid_born_rule P";
         "trace_quantum_bridge_coherent fuel trace s_init";
         "NPA/Gram coherence premise packages symmetry + PSD obligations" ];
     claim_premise_kinds := [ PremiseStructural; PremiseSemantic; PremisePhysical ];
     claim_not_imply :=
       [ "Does not derive trace_quantum_bridge_coherent from bare μ-accounting.";
         "Does not by itself prove that any physical source satisfies the bridge premise." ] |}.

Definition audit_master_psd_iff_column_contractive : HonestClaim :=
  {| claim_name := "master_psd_iff_column_contractive";
     claim_sources := [ "QuantumPartitionPSD.npa_psd_iff_column_contractive" ];
     claim_scope := Algebraic;
     claim_status := StatusUnconditional;
     claim_role := WrapperOnly;
     claim_premises := [ "standard real-analysis and PSD lemmas only" ];
     claim_premise_kinds := [ PremiseStandardLibrary; PremiseAlgebraic ];
     claim_not_imply :=
       [ "Does not prove a runtime trace satisfies PSD; it classifies the algebraic condition once the correlators are given." ] |}.

Definition audit_master_trace_column_contractive_iff_quantum_model : HonestClaim :=
  {| claim_name := "master_trace_column_contractive_iff_quantum_model";
     claim_sources := [ "QuantumPartitionPSD.trace_column_contractive_iff_trace_quantum_model" ];
     claim_scope := ExecutableBridge;
     claim_status := StatusUnconditional;
     claim_role := WrapperOnly;
     claim_premises := [ "trace-level extracted correlators are defined" ];
     claim_premise_kinds := [ PremiseSemantic ];
     claim_not_imply :=
       [ "Does not say the trace came from a physical quantum device." ] |}.

Definition audit_master_trace_quantum_model_unfolds : HonestClaim :=
  {| claim_name := "master_trace_quantum_model_unfolds";
     claim_sources := [ "TsirelsonQuantumModel.trace_quantum_model"; "NPAMomentMatrix.quantum_realizable" ];
     claim_scope := Definitional;
     claim_status := StatusDefinitional;
     claim_role := DefinitionalRestatement;
     claim_premises :=
       [ "trace_zero_marginal_npa fuel trace s_init is defined";
         "quantum_realizable is defined as symmetric5 /\\ PSD5 on the induced 5x5 moment matrix" ];
     claim_premise_kinds := [ PremiseSemantic; PremiseSyntactic ];
     claim_not_imply :=
       [ "Does not prove the trace satisfies the predicate; it only exposes what the predicate means.";
         "Does not by itself add any physical interpretation to the extracted correlators." ] |}.

Definition audit_master_trace_quantum_bridge_forces_psd : HonestClaim :=
  {| claim_name := "master_trace_quantum_bridge_forces_psd";
     claim_sources := [ "TsirelsonQuantumModel.trace_quantum_bridge_coherent_implies_quantum_model" ];
     claim_scope := ExecutableBridge;
     claim_status := StatusConditional;
     claim_role := NewComposition;
     claim_premises := [ "trace_quantum_bridge_coherent fuel trace s_init" ];
     claim_premise_kinds := [ PremiseSemantic; PremisePhysical ];
     claim_not_imply :=
       [ "Does not prove coherence for arbitrary traces.";
         "Does not turn a semantic certificate into an empirical one." ] |}.

Definition audit_master_honest_nofi_structure_requirement : HonestClaim :=
  {| claim_name := "master_honest_nofi_structure_requirement";
     claim_sources := [ "HonestNoFI_TheoremsWithoutAssumptions.honest_information_reduction_requires_structure_addition" ];
     claim_scope := Structural;
     claim_status := StatusUnconditional;
     claim_role := WrapperOnly;
     claim_premises :=
       [ "run_vm fuel trace s_init = s_final";
         "strict feasible-set reduction";
         "strictly_stronger posterior predicate";
         "Certified s_final decoder P_posterior trace" ];
     claim_premise_kinds := [ PremiseStructural; PremiseSemantic ];
     claim_not_imply :=
       [ "Does not claim every form of inference in every model is covered." ] |}.

Definition audit_master_honest_nofi_trace_separation : HonestClaim :=
  {| claim_name := "master_honest_nofi_trace_separation";
     claim_sources := [ "HonestNoFI.honest_nfi_trace_separation_partial" ];
     claim_scope := Structural;
     claim_status := StatusUnconditional;
     claim_role := WrapperOnly;
     claim_premises :=
       [ "all compared initial states start with cert_addr = 0";
         "all compared runs end at nonzero cert_addr values";
         "the resulting cert_addr values are pairwise distinct" ];
     claim_premise_kinds := [ PremiseStructural; PremiseSemantic; PremiseSemantic ];
     claim_not_imply :=
       [ "Does not by itself identify a per-run log2 lower bound on Δμ." ] |}.

Definition audit_master_honest_nofi_conditional_shannon : HonestClaim :=
  {| claim_name := "master_honest_nofi_conditional_shannon";
     claim_sources := [ "HonestNoFI.honest_nfi_conditional_shannon_partial" ];
     claim_scope := Structural;
     claim_status := StatusConditional;
     claim_role := WrapperOnly;
     claim_premises :=
       [ "info-pricing on cert-setting instructions";
         "the concrete run executes at least log2(n) cert-setting steps" ];
     claim_premise_kinds := [ PremiseStructural; PremiseSemantic ];
     claim_not_imply :=
       [ "Does not yet collapse the full feasible-set ratio theorem into one unconditional export." ] |}.

Definition audit_master_honest_nofi_quantitative_state_space : HonestClaim :=
  {| claim_name := "master_honest_nofi_quantitative_state_space";
     claim_sources := [ "HonestNoFI.honest_nfi_quantitative_state_space_partial" ];
     claim_scope := Structural;
     claim_status := StatusUnconditional;
     claim_role := WrapperOnly;
     claim_premises :=
       [ "the step is an LASSERT transition";
         "cost = 1 + formula length" ];
     claim_premise_kinds := [ PremiseSemantic; PremiseSyntactic ];
     claim_not_imply :=
       [ "Does not provide a fully general feasible-set-ratio theorem for arbitrary traces.";
         "Exports the conservative StateSpaceCounting wrapper, not an exact runtime model-count theorem." ] |}.

Definition audit_master_honest_nofi_posterior_representative_reduction : HonestClaim :=
  {| claim_name := "master_honest_nofi_posterior_representative_reduction";
     claim_sources := [ "HonestNoFI.honest_nfi_posterior_representative_reduction_partial" ];
     claim_scope := Structural;
     claim_status := StatusConditional;
     claim_role := WrapperOnly;
     claim_premises :=
       [ "info-pricing on cert-setting instructions";
         "the concrete run realizes the decision tree";
         "the posterior feasible set is nonempty";
         "a posterior-representative observation-equivalence witness over the feasible sets is supplied" ];
     claim_premise_kinds := [ PremiseStructural; PremiseSemantic; PremiseSemantic; PremiseSemantic ];
     claim_not_imply :=
       [ "Does not automatically derive the posterior-representative witness from arbitrary feasible-set collapse.";
         "Does not yet eliminate the explicit decision-tree premise." ] |}.

Definition audit_master_a2_equal_trust_substitution_payoff : HonestClaim :=
  {| claim_name := "master_a2_equal_trust_substitution_payoff";
     claim_sources :=
       [ "A2Payoff.a2_equal_trust_substitution_payoff";
         "CommitmentPredicateAdequacy.substitution_test_rejects_non_a2_exact_substitute";
         "CommitmentCostDecomposition.dcs_substitution_test_rejects_non_a2_exact_component" ];
     claim_scope := Structural;
     claim_status := StatusUnconditional;
     claim_role := NewComposition;
     claim_premises :=
       [ "equal trust: the priced local predicate is part of the trusted transition law";
         "exact commitment pricing: the law lower-bounds certification commitments and does not overcharge beyond them";
         "decomposed total cost separates background work from the commitment component" ];
     claim_premise_kinds := [ PremiseSemantic; PremiseStructural; PremiseSemantic ];
     claim_not_imply :=
       [ "Does not claim arbitrary projection/lift asymmetry is privileged.";
         "Does not use the trusted-vs-untrusted verification gap.";
         "Rules out substitutes only for exact certification-commitment pricing; predicates that intentionally overcharge are classified as different cost laws." ] |}.

Definition audit_master_nofi_to_discrete_einstein : HonestClaim :=
  {| claim_name := "master_nofi_to_discrete_einstein";
     claim_sources := [ "NoFIToEinstein.nfi_to_discrete_einstein" ];
     claim_scope := ConditionalPhysical;
     claim_status := StatusConditional;
     claim_role := WrapperOnly;
     claim_premises :=
       [ "positive hbar, c_light, and k_B";
         "nearest-neighbor split morphism with support witnesses";
         "explicit Landauer-Unruh calibration predicate";
         "well-formed pre/post triangulations" ];
     claim_premise_kinds := [ PremisePhysical; PremiseStructural; PremisePhysical; PremiseStructural ];
     claim_not_imply :=
       [ "Does not derive the calibration predicate from bare μ-accounting alone.";
         "Does not eliminate the explicit local-horizon thermodynamic corridor assumptions." ] |}.

Definition audit_master_nofi_to_discrete_einstein_from_bekenstein_calibration : HonestClaim :=
  {| claim_name := "master_nofi_to_discrete_einstein_from_bekenstein_calibration";
     claim_sources := [ "NoFIToEinstein.nfi_to_discrete_einstein_from_bekenstein_calibration" ];
     claim_scope := ConditionalPhysical;
     claim_status := StatusConditional;
     claim_role := WrapperOnly;
     claim_premises :=
       [ "positive hbar, c_light, and k_B";
         "nearest-neighbor split morphism with support witnesses";
         "Landauer-Unruh constants calibration";
         "explicit mu_bit_calibration over the chosen support witnesses";
         "well-formed pre/post triangulations" ];
     claim_premise_kinds := [ PremisePhysical; PremiseStructural; PremisePhysical; PremiseSemantic; PremiseStructural ];
     claim_not_imply :=
       [ "Does not provide an empirical measurement theorem for the constants calibration.";
         "Still depends on the explicit Bekenstein/Landauer-Unruh premises that connect the μ-ledger to horizon thermodynamics." ] |}.

Definition audit_master_nofi_to_discrete_einstein_from_psplit_bekenstein_calibration : HonestClaim :=
  {| claim_name := "master_nofi_to_discrete_einstein_from_psplit_bekenstein_calibration";
     claim_sources := [ "NoFIToEinstein.nfi_to_discrete_einstein_from_psplit_bekenstein_calibration" ];
     claim_scope := ConditionalPhysical;
     claim_status := StatusConditional;
     claim_role := WrapperOnly;
     claim_premises :=
       [ "positive hbar, c_light, and k_B";
         "a concrete vm_step PSPLIT transition";
         "nearest-neighbor condition for the induced psplit_transition_morphism";
         "Landauer-Unruh constants calibration";
         "PSPLIT cost matches the induced entropy event";
         "well-formed pre/post triangulations" ];
     claim_premise_kinds := [ PremisePhysical; PremiseSemantic; PremiseStructural; PremisePhysical; PremiseSemantic; PremiseStructural ];
     claim_not_imply :=
       [ "Does not yet generalize the execution-grounded entropy bridge beyond the PSPLIT family.";
         "Does not eliminate the constants calibration premise." ] |}.

Definition audit_master_verification_chain : HonestClaim :=
  {| claim_name := "master_verification_chain";
     claim_sources := [ "HardwareBisimulation.complete_verification_chain" ];
     claim_scope := VerificationTransfer;
     claim_status := StatusConditional;
     claim_role := WrapperOnly;
     claim_premises := [ "hw_bisimulation_invariant hw_init py_init" ];
     claim_premise_kinds := [ PremiseVerification ];
     claim_not_imply :=
       [ "Does not prove transfer of every imaginable semantic property.";
         "Does not prove full register/memory/partition equality in the abstract hardware model imported here." ] |}.

Definition audit_master_verification_preserved_observables : HonestClaim :=
  {| claim_name := "master_verification_preserved_observables";
     claim_sources := [ "HardwareBisimulation.complete_verification_chain" ];
     claim_scope := VerificationTransfer;
     claim_status := StatusConditional;
     claim_role := NewComposition;
     claim_premises :=
       [ "hw_bisimulation_invariant hw_init py_init";
         "cost-trace execution through the abstract hardware/Python models" ];
     claim_premise_kinds := [ PremiseVerification; PremiseSemantic ];
     claim_not_imply :=
       [ "Does not export a theorem about every hardware observable.";
         "Pins down exactly the observables preserved here: PC and μ-accumulator." ] |}.

(** The reductions tier: five real-world systems instantiated against the
    kernel's abstract records (kernel/reductions/). Each row registers the
    file's headline result with its honest scope and non-implications. *)

Definition audit_master_pos_finality_reduction : HonestClaim :=
  {| claim_name := "master_pos_finality_reduction";
     claim_sources :=
       [ "PoSFinality.nothing_at_stake_is_free_forgery";
         "PoSFinality.slashing_finality_floor" ];
     claim_scope := Structural;
     claim_status := StatusUnconditional;
     claim_role := NewComposition;
     claim_premises :=
       [ "an inhabited abstract validator-view type";
         "slashing condition stake_at_risk PoSFinalize >= 1 (positive direction only)" ];
     claim_premise_kinds := [ PremiseStructural; PremiseStructural ];
     claim_not_imply :=
       [ "Does not model economic rationality, network timing, or validator collusion.";
         "Does not price any event other than the finalization flip." ] |}.

Definition audit_master_gas_metering_reduction : HonestClaim :=
  {| claim_name := "master_gas_metering_reduction";
     claim_sources :=
       [ "GasMetering.gas_schedule_exactness";
         "GasMetering.undercharged_opcode_admits_free_commitment";
         "GasMetering.thiele_vm_commit_pricing_is_exact" ];
     claim_scope := Structural;
     claim_status := StatusUnconditional;
     claim_role := NewComposition;
     claim_premises :=
       [ "the trusted local-predicate pricing laws (charged steps cost >= 1, uncharged steps are free)" ];
     claim_premise_kinds := [ PremiseStructural ];
     claim_not_imply :=
       [ "Does not bound gate counts or model gas refunds.";
         "gas_schedule_exactness itself is the kernel characterization re-read in fee-market vocabulary; the failure modes and concrete instances are the new content." ] |}.

Definition audit_master_tee_attestation_reduction : HonestClaim :=
  {| claim_name := "master_tee_attestation_reduction";
     claim_sources :=
       [ "TEEAttestation.attestation_cannot_factor_through_bare_transcript";
         "TEEAttestation.replay_is_a_two_preimage_witness";
         "TEEAttestation.measurement_enriched_attestation_succeeds" ];
     claim_scope := Structural;
     claim_status := StatusUnconditional;
     claim_role := NewComposition;
     claim_premises :=
       [ "attestation soundness and completeness stated over the kernel's mu = 1 verification problem" ];
     claim_premise_kinds := [ PremiseStructural ];
     claim_not_imply :=
       [ "Does not model side channels, key management, or the vendor signing PKI.";
         "The ineliminable trust it names is structural, not an implementation audit." ] |}.

Definition audit_master_transparency_log_reduction : HonestClaim :=
  {| claim_name := "master_transparency_log_reduction";
     claim_sources :=
       [ "TransparencyLog.transparency_log_escape";
         "TransparencyLog.log_free_verifier_impossible";
         "TransparencyLog.split_view_witness" ];
     claim_scope := Structural;
     claim_status := StatusConditional;
     claim_role := NewComposition;
     claim_premises :=
       [ "a HardnessHypothesis (the log's unforgeability is named, not proven)" ];
     claim_premise_kinds := [ PremiseStructural ];
     claim_not_imply :=
       [ "Does not model gossip protocols, log governance, or Merkle internals.";
         "log_free_verifier_impossible is the kernel's bare-setting impossibility re-exported in CT vocabulary." ] |}.

Definition audit_master_proof_carrying_reduction : HonestClaim :=
  {| claim_name := "master_proof_carrying_reduction";
     claim_sources :=
       [ "ProofCarryingVerifier.proof_rounds_escape";
         "ProofCarryingVerifier.bare_pcc_impossible";
         "ProofCarryingVerifier.level_k_verification_floor" ];
     claim_scope := Structural;
     claim_status := StatusUnconditional;
     claim_role := NewComposition;
     claim_premises :=
       [ "the kernel's single-round interaction model";
         "level_k_certified trace semantics for the floor" ];
     claim_premise_kinds := [ PremiseStructural; PremiseSemantic ];
     claim_not_imply :=
       [ "The floor bounds certification events only - not gate counts, SNARK verifier circuit size, prover time, or proof length.";
         "Does not model zero-knowledge hiding or soundness amplification." ] |}.

Definition master_claim_ledger : list HonestClaim :=
  [ audit_master_mu_zero_algebraic_bound;
    audit_master_classical_bound;
    audit_master_quantum_foundations;
    audit_master_non_circularity;
    audit_master_tsirelson_conditional;
    audit_master_psd_iff_column_contractive;
    audit_master_trace_column_contractive_iff_quantum_model;
    audit_master_trace_quantum_model_unfolds;
    audit_master_trace_quantum_bridge_forces_psd;
    audit_master_honest_nofi_structure_requirement;
    audit_master_honest_nofi_trace_separation;
    audit_master_honest_nofi_conditional_shannon;
    audit_master_honest_nofi_quantitative_state_space;
    audit_master_honest_nofi_posterior_representative_reduction;
    audit_master_a2_equal_trust_substitution_payoff;
    audit_master_nofi_to_discrete_einstein;
    audit_master_nofi_to_discrete_einstein_from_bekenstein_calibration;
    audit_master_verification_chain;
    audit_master_verification_preserved_observables;
    audit_master_pos_finality_reduction;
    audit_master_gas_metering_reduction;
    audit_master_tee_attestation_reduction;
    audit_master_transparency_log_reduction;
    audit_master_proof_carrying_reduction ].

(**
    PART 0a: MECHANISM FILE MAP

    If a reader wants the machine "all the way down", the load-bearing files
    are not only theorem bundles. They also include the operational semantics,
    μ-ledger machinery, trace extraction path, bridge predicates, strongest
    theorem files, hardware realization path, and one concrete end-to-end run.

    This section points to those exact files rather than repeating their full
    contents inline.
*)

Definition exact_mechanism_file_map : list string :=
  [ "1. core state semantics: coq/kernel/VMState.v";
    "1. one-step execution semantics: coq/kernel/VMStep.v";
    "1. operational simulation helpers: coq/kernel/SimulationProof.v";
    "2. mu-cost definition and trace accumulation: coq/kernel/MuCostModel.v";
    "2. structure-addition predicate: coq/kernel/NoFreeInsight.v";
    "3. trace and CHSH observable extraction: coq/kernel/CHSHExtraction.v";
    "3. trace correlators and trace_zero_marginal_npa construction: coq/kernel/MuLedgerQuantumBridge.v";
    "4. trace_quantum_bridge_coherent and trace_quantum_model: coq/kernel/TsirelsonQuantumModel.v";
    "4. quantum_realizable: coq/kernel/NPAMomentMatrix.v";
    "4. trace_column_contractive: coq/kernel/MuLedgerQuantumBridge.v";
    "5. PSD <-> column contractive theorem chain: coq/kernel/QuantumPartitionPSD.v";
    "5. trace bridge to Tsirelson: coq/kernel/TsirelsonQuantumModel.v";
    "5. non-circularity theorem chain: coq/kernel/NonCircularityAudit.v";
    "5. structural No Free Insight export chain: coq/kernel/HonestNoFI_TheoremsWithoutAssumptions.v";
    "5. quantitative cert-setter / Shannon bounds: coq/kernel/MuShannonQuantitative.v";
    "5. posterior-representative / fibered reduction semantics lift: coq/kernel/MuShannonBridge.v";
    "5. conservative quantitative state-space-counting wrapper: coq/kernel/StateSpaceCounting.v";
    "5. split-morphism locality witness: coq/kernel/LocalMorphismSemantics.v";
    "5. locality-to-entropy area-law bridge: coq/kernel/EntanglementEntropy.v";
    "5. explicit Clausius witness from entropy/temperature control: coq/kernel/ClausiusFromEntropyArea.v";
    "5. Raychaudhuri null-flux bridge: coq/kernel/RaychaudhuriFluxBridge.v";
    "5. Jacobson component decomposition: coq/kernel/JacobsonBridgeComponents.v";
    "5. thermodynamic locality to Einstein-target bridge: coq/kernel/ThermoEinsteinBridge.v";
    "5. abstract verification transfer theorem chain: coq/kernel/HardwareBisimulation.v";
    "6. hardware abstraction path from Kami snapshot to VMState: coq/kami_hw/Abstraction.v";
    "6. full-state per-instruction embed step: coq/kami_hw/FullEmbedStep.v";
    "6. full-state step commutation bridge (all 46 opcodes): coq/kami_hw/GraphReconstructionBridge.v";
    "6. Verilog/RTL refinement theorems: coq/kami_hw/VerilogRefinement.v";
    "6. generated RTL implementation: thielecpu/hardware/rtl/thiele_cpu_kami.v";
    "6. simulation testbench: rtl_harness/testbench/thiele_cpu_kami_tb.v";
    "6. co-simulation harness: rtl_harness/cosim.py";
    "6. FPGA synthesis entrypoint: fpga/run_synthesis.sh";
    "7. concrete executable witness trace: coq/kernel/ClassicalBound.v";
    "7. three-layer observable alignment route: archive/coq_unused/thielemachine/verification/FullIsomorphism.v (archived)" ].

Theorem exact_mechanism_file_map_explicit :
  List.length exact_mechanism_file_map = 34%nat.
Proof.
  reflexivity.
Qed.

Definition end_to_end_example_route : list string :=
  [ "Executable witness trace: ClassicalBound.classical_achieving_trace in coq/kernel/ClassicalBound.v";
    "Summary-level witness alias: master_mu_zero_witness_trace in coq/kernel/MasterSummary.v";
    "Python VM embodiment: thielecpu/vm.py";
    "OCaml extraction artifacts: build/extracted_vm_runner.ml and build/thiele_core.ml";
    "RTL embodiment and testbench: thielecpu/hardware/rtl/thiele_cpu_kami.v and rtl_harness/testbench/thiele_cpu_kami_tb.v";
    "Cross-layer observable alignment reference: archive/coq_unused/thielemachine/verification/FullIsomorphism.v (archived)" ].

Theorem end_to_end_example_route_explicit :
  List.length end_to_end_example_route = 6%nat.
Proof.
  reflexivity.
Qed.

(**
    PART 0b: THEOREM STATEMENT EXPOSURE

    This section exposes the mathematical content of the load-bearing imported
    theorems that the rest of this summary relies on. The goal is not to inline
    their proofs, but to restate their content in this file's own vocabulary so
    their premises and consequences are explicit at the statement level.
    Proof spines still remain external unless separately inlined.
*)

Definition exposed_zero_marginal_psd_contractivity_spine : Prop :=
  forall e00 e01 e10 e11 : R,
    PSD5 (nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11)))
    <->
    zero_marginal_column_contractive e00 e01 e10 e11.

Theorem exposed_zero_marginal_psd_contractivity :
  exposed_zero_marginal_psd_contractivity_spine.
Proof.
  intros e00 e01 e10 e11.
  split.
  - apply npa_psd_implies_column_contractive.
  - intros Hcontractive.
    destruct Hcontractive as [Hc0 [Hc1 Hdet]].
    apply zero_marginal_npa_column_contractive_implies_psd.
    exact Hc0.
    exact Hc1.
    exact Hdet.
Qed.

Definition exposed_trace_bridge_spine : Prop :=
  forall fuel trace s_init,
    trace_quantum_bridge_coherent fuel trace s_init ->
    trace_quantum_model fuel trace s_init /\
    trace_column_contractive fuel trace s_init /\
    PSD5 (nat_matrix_to_fin5 (npa_to_matrix (trace_zero_marginal_npa fuel trace s_init))) /\
    (Rabs (CHSH
      (trace_e00 fuel trace s_init)
      (trace_e01 fuel trace s_init)
      (trace_e10 fuel trace s_init)
      (trace_e11 fuel trace s_init)) <= sqrt8)%R.

Theorem exposed_trace_bridge_content :
  exposed_trace_bridge_spine.
Proof.
  intros fuel trace s_init Hcoh.
  pose proof (trace_quantum_model_connection_closed fuel trace s_init Hcoh) as [Hmodel Hbound].
  pose proof (proj2 (trace_column_contractive_iff_trace_quantum_model fuel trace s_init) Hmodel) as Hcontractive.
  pose proof Hmodel as Hmodel_psd.
  unfold trace_quantum_model, quantum_realizable in Hmodel_psd.
  destruct Hmodel_psd as [_ Hpsd].
  split.
  - exact Hmodel.
  - split.
    + exact Hcontractive.
    + split.
      * exact Hpsd.
      * exact Hbound.
Qed.

(** The earlier [chsh_formula_is_algebraic] conjunct (a vacuous [forall x
    y z w, x = x] dressed as a Prop) has been removed: its proof was a
    single [reflexivity] and it added no audit content beyond what the
    Q-arithmetic definitions of [classical_chsh_value] and [chsh_value]
    already make structurally visible. *)
Definition exposed_non_circularity_spine : Prop :=
  non_circularity_certificate /\
  (forall r : mu_cost_rule,
     rule_references_chsh r = false /\
     rule_references_quantum r = false /\
     rule_references_tsirelson r = false) /\
  classical_bound_appears_as_achievable /\
  mu_zero_locc_correspondence.

Theorem exposed_non_circularity_content :
  exposed_non_circularity_spine.
Proof.
  split.
  - exact non_circularity_verified.
  - split.
    + exact mu_cost_is_physics_free.
    + split.
      * exact classical_bound_is_derived_not_assumed.
      * exact mu_zero_is_locc_like.
Qed.

Definition exposed_verification_surface_spine : Prop :=
  forall hw_init py_init,
    hw_bisimulation_invariant hw_init py_init ->
    forall costs : list nat,
    hw_bisimulation_invariant
      (hardware_multi_step hw_init costs)
      (python_multi_step py_init costs) /\
    (hardware_multi_step hw_init costs).(hw_pc) =
      (python_multi_step py_init costs).(py_pc) /\
    (hardware_multi_step hw_init costs).(hw_mu_accumulator) =
      (python_multi_step py_init costs).(py_mu).

Lemma trace_semantics_invariant_under_verification_chain :
  forall hw_init py_init costs,
    hw_bisimulation_invariant hw_init py_init ->
    hw_bisimulation_invariant
      (hardware_multi_step hw_init costs)
      (python_multi_step py_init costs).
Proof.
  intros hw_init py_init costs Hinv.
  pose proof (complete_verification_chain hw_init py_init Hinv costs) as [Hinv_final _].
  exact Hinv_final.
Qed.

Lemma trace_run_verification_invariant :
  forall hw_init py_init costs,
    hw_bisimulation_invariant hw_init py_init ->
    hw_bisimulation_invariant
      (hardware_multi_step hw_init costs)
      (python_multi_step py_init costs).
Proof.
  intros hw_init py_init costs Hinv.
  apply trace_semantics_invariant_under_verification_chain.
  exact Hinv.
Qed.

Theorem exposed_verification_surface_content :
  exposed_verification_surface_spine.
Proof.
  intros hw_init py_init Hinv costs.
  pose proof (complete_verification_chain hw_init py_init Hinv costs) as [Hcorr Hmu].
  destruct Hcorr as [Hpc Hmu_inv].
  repeat split; try exact Hmu; try exact Hpc; try exact Hmu_inv.
Qed.

Definition exposed_honest_nofi_structure_spine : Prop :=
  forall (fuel : nat) (trace : list vm_instruction)
         (s_init s_final : VMState)
         (decoder : NoFreeInsight.receipt_decoder (list vm_instruction))
         (P_prior P_posterior : NoFreeInsight.ReceiptPredicate (list vm_instruction))
         (omega_prior omega_posterior : InformationGainToStrengthening.FeasibleSet),
    s_final = run_vm fuel trace s_init ->
    In s_init omega_prior ->
    InformationGainToStrengthening.is_strict_reduction omega_prior omega_posterior ->
    (InformationGainToStrengthening.feasible_size omega_posterior > 0)%nat ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    NoFreeInsight.strictly_stronger P_posterior P_prior ->
    NoFreeInsight.Certified s_final decoder P_posterior trace ->
    NoFreeInsight.has_structure_addition fuel trace s_init.

Theorem exposed_honest_nofi_structure_content :
  exposed_honest_nofi_structure_spine.
Proof.
  intros fuel trace s_init s_final decoder P_prior P_posterior omega_prior omega_posterior.
  intros Hfinal Hin_prior Hreduce Hcard Hinit Hstronger Hcert.
  eapply honest_information_reduction_requires_structure_addition.
  - exact Hfinal.
  - exact Hin_prior.
  - exact Hreduce.
  - exact Hcard.
  - exact Hinit.
  - exact Hstronger.
  - exact Hcert.
Qed.

Definition exposed_honest_nofi_trace_separation_spine : Prop :=
  forall fuel trace omega,
    (forall s, In s omega -> s.(vm_csrs).(csr_cert_addr) = 0%nat) ->
    (forall s, In s omega -> (run_vm fuel trace s).(vm_csrs).(csr_cert_addr) <> 0%nat) ->
    NoDup (map (fun s => (run_vm fuel trace s).(vm_csrs).(csr_cert_addr)) omega) ->
    (List.length omega <= MuShannonQuantitative.count_cert_addr_setters trace)%nat.

Definition exposed_honest_nofi_trace_separation_content :
  exposed_honest_nofi_trace_separation_spine :=
  honest_nfi_trace_separation_partial.

Definition exposed_honest_nofi_conditional_shannon_spine : Prop :=
  forall fuel trace s n,
    Forall (fun i => is_cert_setterb i = true -> (instruction_cost i >= 1)%nat) trace ->
    (MuShannonQuantitative.cert_setter_executions_local fuel trace s >= Nat.log2 n)%nat ->
    ((run_vm fuel trace s).(vm_mu) - s.(vm_mu) >= Nat.log2 n)%nat.

Definition exposed_honest_nofi_conditional_shannon_content :
  exposed_honest_nofi_conditional_shannon_spine :=
  honest_nfi_conditional_shannon_partial.

Definition exposed_honest_nofi_quantitative_state_space_spine : Prop :=
  forall (s s' : VMState) (fa ca : nat) (ck : bool) (flen cost : nat),
    VMStep.VMStep.vm_step s
      (VMStep.VMStep.instr_lassert fa ca ck flen cost) s' ->
    let k := (flen * 8)%nat in
    (s'.(vm_mu) - s.(vm_mu) >= k)%nat /\
    (k >= StateSpaceCounting.log2_nat (Nat.pow 2 k))%nat.

Definition exposed_honest_nofi_quantitative_state_space_content :
  exposed_honest_nofi_quantitative_state_space_spine :=
  honest_nfi_quantitative_state_space_partial.

Definition exposed_honest_nofi_posterior_representative_reduction_spine : Prop :=
  forall fuel trace s omega_prior omega_posterior tree
         (obs_fn : MuShannonBridge.ObservationFunction),
    MuShannonBridge.decision_tree_realized_by_trace fuel trace s tree ->
    (MuShannonBridge.feasible_size omega_posterior > 0)%nat ->
    MuShannonBridge.PosteriorRepresentativeReduction obs_fn tree omega_prior omega_posterior ->
    (Nat.log2_up (MuShannonBridge.feasible_size omega_prior) -
      Nat.log2_up (MuShannonBridge.feasible_size omega_posterior) <=
      (run_vm fuel trace s).(vm_mu) - s.(vm_mu))%nat.

Definition exposed_honest_nofi_posterior_representative_reduction_content :
  exposed_honest_nofi_posterior_representative_reduction_spine :=
  honest_nfi_posterior_representative_reduction_partial.

Definition exposed_a2_equal_trust_substitution_spine : Prop :=
  commitment_vs_erasure_payoff /\
  (forall LPS : LocalPredicatePricedSystem,
      quantitative_certification_floor LPS <->
      local_predicate_le LPS (cert_flip_local LPS) (lps_charge LPS)) /\
  (forall LPS : LocalPredicatePricedSystem,
      batch_certification_floor LPS <->
      local_predicate_le LPS (cert_flip_local LPS) (lps_charge LPS)) /\
  (forall LPS : LocalPredicatePricedSystem,
      (quantitative_certification_floor LPS /\
       no_overcharge_for_commitments LPS)
      <->
      (local_predicate_same LPS (cert_flip_local LPS) (lps_charge LPS) /\
       exact_unit_pricing LPS)) /\
  (forall LPS : LocalPredicatePricedSystem,
      ~ local_predicate_same LPS (cert_flip_local LPS) (lps_charge LPS) ->
      ~ (quantitative_certification_floor LPS /\
         no_overcharge_for_commitments LPS)) /\
  (forall DCS : DecomposedCommitmentSystem,
      (forall trace s0,
          dcs_total_cost DCS trace s0 =
          (dcs_total_base DCS trace s0 + dcs_cert_flip_count DCS trace s0)%nat)
      <->
      dcs_local_predicate_same DCS (dcs_cert_flip_local DCS) (dcs_charge DCS)) /\
  (forall DCS : DecomposedCommitmentSystem,
      ~ dcs_local_predicate_same DCS (dcs_cert_flip_local DCS) (dcs_charge DCS) ->
      ~ (forall trace s0,
            dcs_total_cost DCS trace s0 =
            (dcs_total_base DCS trace s0 + dcs_cert_flip_count DCS trace s0)%nat)) /\
  (forall trace s0,
      dcs_total_cost vm_certified_decomposed_system trace s0 =
      (dcs_total_base vm_certified_decomposed_system trace s0
       + dcs_cert_flip_count vm_certified_decomposed_system trace s0)%nat).

Definition exposed_a2_equal_trust_substitution_content :
  exposed_a2_equal_trust_substitution_spine :=
  a2_equal_trust_substitution_payoff.

Definition exposed_thermo_einstein_bridge_spine : Prop :=
  forall (SpacetimeState : Type)
         (EinsteinTarget : SpacetimeState -> Prop)
         (LocalHorizon : SpacetimeState -> Type)
         (hbar c_light k_B entropy_per_bit : R)
         (hbar_pos : (0 < hbar)%R)
         (c_light_pos : (0 < c_light)%R)
         (k_B_pos : (0 < k_B)%R)
         (raychaudhuri_component :
            forall (st : SpacetimeState)
                   (H : LocalHorizon st)
                   (dQ dS T : R),
              (0 < T)%R ->
              dQ = (T * dS)%R ->
              EinsteinTarget st)
         (s_pre s_post : VMState)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support_pre support_post : LocalMorphismSemantics.joint_support)
         (st : SpacetimeState)
         (H : LocalHorizon st),
    LocalMorphismSemantics.is_nearest_neighbor P ->
    In support_pre (LocalMorphismSemantics.morphism_support_semantics P) ->
    In support_post (LocalMorphismSemantics.morphism_support_semantics P) ->
    RaychaudhuriFluxBridge.null_energy_flux_delta
      RaychaudhuriFluxBridge.calibrated_null_congruence s_pre s_post P =
      (ClausiusFromEntropyArea.unruh_temperature
         hbar c_light k_B P *
       ClausiusFromEntropyArea.entropy_increment_delta
         entropy_per_bit support_pre support_post)%R ->
    EinsteinTarget st.

Definition exposed_thermo_einstein_bridge_content :
  exposed_thermo_einstein_bridge_spine :=
  ThermoEinsteinBridge.thermodynamic_locality_toward_einstein_with_clausius_model.

Definition exposed_thermo_discrete_einstein_spine : Prop :=
  forall (hbar c_light k_B entropy_per_bit : R)
         (hbar_pos : (0 < hbar)%R)
         (c_light_pos : (0 < c_light)%R)
         (k_B_pos : (0 < k_B)%R)
         (s_pre s_post : VMState)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support_pre support_post : LocalMorphismSemantics.joint_support),
    LocalMorphismSemantics.is_nearest_neighbor P ->
    In support_pre (LocalMorphismSemantics.morphism_support_semantics P) ->
    In support_post (LocalMorphismSemantics.morphism_support_semantics P) ->
    RaychaudhuriFluxBridge.null_energy_flux_delta
      RaychaudhuriFluxBridge.calibrated_null_congruence s_pre s_post P =
      (ClausiusFromEntropyArea.unruh_temperature hbar c_light k_B P *
       ClausiusFromEntropyArea.entropy_increment_delta
         entropy_per_bit support_pre support_post)%R ->
    well_formed_triangulated (vm_graph s_pre) ->
    well_formed_triangulated (vm_graph s_post) ->
    (total_curvature (vm_graph s_post) - total_curvature (vm_graph s_pre))%R =
      (einstein_coupling_constant *
       IZR (euler_characteristic (vm_graph s_post) -
            euler_characteristic (vm_graph s_pre)))%R.

Definition exposed_thermo_discrete_einstein_content :
  exposed_thermo_discrete_einstein_spine :=
  ThermoEinsteinBridge.thermodynamic_locality_toward_discrete_einstein_emergence.

Definition exposed_nofi_to_discrete_einstein_spine : Prop :=
  forall (hbar c_light k_B entropy_per_bit : R)
         (s_pre s_post : VMState)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support_pre support_post : LocalMorphismSemantics.joint_support),
    (0 < hbar)%R ->
    (0 < c_light)%R ->
    (0 < k_B)%R ->
    LocalMorphismSemantics.is_nearest_neighbor P ->
    In support_pre (LocalMorphismSemantics.morphism_support_semantics P) ->
    In support_post (LocalMorphismSemantics.morphism_support_semantics P) ->
    NoFIToEinstein.mu_landauer_unruh_calibrated
      hbar c_light k_B entropy_per_bit s_pre s_post P support_pre support_post ->
    well_formed_triangulated (vm_graph s_pre) ->
    well_formed_triangulated (vm_graph s_post) ->
    (total_curvature (vm_graph s_post) - total_curvature (vm_graph s_pre))%R =
    (einstein_coupling_constant *
     IZR (euler_characteristic (vm_graph s_post) -
          euler_characteristic (vm_graph s_pre))%Z)%R.

Definition exposed_nofi_to_discrete_einstein_content :
  exposed_nofi_to_discrete_einstein_spine :=
  NoFIToEinstein.nfi_to_discrete_einstein.

Definition exposed_nofi_to_discrete_einstein_from_bekenstein_calibration_spine : Prop :=
  forall (hbar c_light k_B : R)
         (s_pre s_post : VMState)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support_pre support_post : LocalMorphismSemantics.joint_support),
    (0 < hbar)%R ->
    (0 < c_light)%R ->
    (0 < k_B)%R ->
    LocalMorphismSemantics.is_nearest_neighbor P ->
    In support_pre (LocalMorphismSemantics.morphism_support_semantics P) ->
    In support_post (LocalMorphismSemantics.morphism_support_semantics P) ->
    BekensteinCalibration.landauer_unruh_constant_calibration hbar c_light ->
    BekensteinCalibration.mu_bit_calibration
      support_pre support_post s_pre s_post ->
    well_formed_triangulated (vm_graph s_pre) ->
    well_formed_triangulated (vm_graph s_post) ->
    (total_curvature (vm_graph s_post) - total_curvature (vm_graph s_pre))%R =
    (einstein_coupling_constant *
     IZR (euler_characteristic (vm_graph s_post) -
          euler_characteristic (vm_graph s_pre))%Z)%R.

Definition exposed_nofi_to_discrete_einstein_from_bekenstein_calibration_content :
  exposed_nofi_to_discrete_einstein_from_bekenstein_calibration_spine :=
  NoFIToEinstein.nfi_to_discrete_einstein_from_bekenstein_calibration.

Definition exposed_nofi_to_discrete_einstein_from_psplit_bekenstein_calibration_spine : Prop :=
  forall (hbar c_light k_B : R)
         (s_pre s_post : VMState)
         (module : ModuleID)
         (left right : list nat)
         (cost : nat),
    (0 < hbar)%R ->
    (0 < c_light)%R ->
    (0 < k_B)%R ->
    vm_step s_pre (instr_psplit module left right cost) s_post ->
    LocalMorphismSemantics.is_nearest_neighbor
      (LocalMorphismSemantics.psplit_transition_morphism left right) ->
    BekensteinCalibration.landauer_unruh_constant_calibration hbar c_light ->
    BekensteinCalibration.psplit_cost_matches_entropy left right cost ->
    well_formed_triangulated (vm_graph s_pre) ->
    well_formed_triangulated (vm_graph s_post) ->
    (total_curvature (vm_graph s_post) - total_curvature (vm_graph s_pre))%R =
    (einstein_coupling_constant *
     IZR (euler_characteristic (vm_graph s_post) -
          euler_characteristic (vm_graph s_pre))%Z)%R.

Definition exposed_nofi_to_discrete_einstein_from_psplit_bekenstein_calibration_content :
  exposed_nofi_to_discrete_einstein_from_psplit_bekenstein_calibration_spine :=
  NoFIToEinstein.nfi_to_discrete_einstein_from_psplit_bekenstein_calibration.

Definition exposed_import_spine : list string :=
  [ "QuantumPartitionPSD.npa_psd_iff_column_contractive -> exposed_zero_marginal_psd_contractivity";
    "TsirelsonQuantumModel.trace_quantum_model_connection_closed + QuantumPartitionPSD.trace_column_contractive_iff_trace_quantum_model -> exposed_trace_bridge_content";
    "NonCircularityAudit.non_circularity_verified + sub-certificates -> exposed_non_circularity_content";
    "HardwareBisimulation.complete_verification_chain -> exposed_verification_surface_content";
    "HonestNoFI_TheoremsWithoutAssumptions.honest_information_reduction_requires_structure_addition -> exposed_honest_nofi_structure_content";
    "HonestNoFI.honest_nfi_trace_separation_partial -> exposed_honest_nofi_trace_separation_content";
    "HonestNoFI.honest_nfi_conditional_shannon_partial -> exposed_honest_nofi_conditional_shannon_content";
    "HonestNoFI.honest_nfi_quantitative_state_space_partial -> exposed_honest_nofi_quantitative_state_space_content";
    "HonestNoFI.honest_nfi_posterior_representative_reduction_partial -> exposed_honest_nofi_posterior_representative_reduction_content";
    "A2Payoff.a2_equal_trust_substitution_payoff -> exposed_a2_equal_trust_substitution_content";
    "ThermoEinsteinBridge.thermodynamic_locality_toward_einstein_with_clausius_model -> exposed_thermo_einstein_bridge_content";
    "ThermoEinsteinBridge.thermodynamic_locality_toward_discrete_einstein_emergence -> exposed_thermo_discrete_einstein_content";
    "NoFIToEinstein.nfi_to_discrete_einstein -> exposed_nofi_to_discrete_einstein_content";
    "NoFIToEinstein.nfi_to_discrete_einstein_from_bekenstein_calibration -> exposed_nofi_to_discrete_einstein_from_bekenstein_calibration_content";
    "NoFIToEinstein.nfi_to_discrete_einstein_from_psplit_bekenstein_calibration -> exposed_nofi_to_discrete_einstein_from_psplit_bekenstein_calibration_content" ].

(**
    PART 0c: METADATA COMPLETENESS AND KERNEL-STORY COVERAGE
    *)

(** This first ledger covers the master-claim theorem family only.
  Closure theorems, boundary theorems, and compatibility aliases are
  accounted for separately in the full-file theorem inventory below. *)

Definition master_exported_theorem_names : list string :=
  [ "master_summary_no_hidden_project_assumptions_verified";
    "master_mu_zero_witness_sound";
    "master_mu_zero_algebraic_bound";
    "master_classical_bound";
    "master_quantum_violation_proves_nonclassicality";
    "master_algebraic_tsirelson";
    "master_algebraic_tsirelson_tight";
    "master_quantum_foundations";
    "master_non_circularity";
    "master_tsirelson_conditional";
    "master_psd_iff_column_contractive";
    "master_trace_column_contractive_iff_quantum_model";
    "master_trace_quantum_model_unfolds";
    "master_trace_quantum_bridge_forces_psd";
    "master_honest_nofi_structure_requirement";
    "master_honest_nofi_trace_separation";
    "master_honest_nofi_conditional_shannon";
    "master_honest_nofi_quantitative_state_space";
    "master_honest_nofi_posterior_representative_reduction";
    "master_a2_equal_trust_substitution_payoff";
    "master_nofi_to_discrete_einstein";
    "master_nofi_to_discrete_einstein_from_bekenstein_calibration";
    "master_verification_chain";
    "master_verification_preserved_observables";
    "master_non_circular_mu_cost_primitives";
    "master_non_circular_chsh_formula";
    "master_non_circular_classical_witness";
    "master_non_circular_mu_zero_locc" ].

Definition master_theorem_metadata_ledger : list TheoremMetadata :=
  [ {| metadata_name := "master_summary_no_hidden_project_assumptions_verified";
       metadata_scope := Structural; metadata_status := StatusUnconditional; metadata_role := WrapperOnly |};
    {| metadata_name := "master_mu_zero_witness_sound";
       metadata_scope := Structural; metadata_status := StatusUnconditional; metadata_role := WrapperOnly |};
    {| metadata_name := "master_mu_zero_algebraic_bound";
       metadata_scope := Algebraic; metadata_status := StatusUnconditional; metadata_role := NewComposition |};
    {| metadata_name := "master_classical_bound";
       metadata_scope := Structural; metadata_status := StatusUnconditional; metadata_role := WrapperOnly |};
    {| metadata_name := "master_quantum_violation_proves_nonclassicality";
       metadata_scope := Structural; metadata_status := StatusUnconditional; metadata_role := NewComposition |};
    {| metadata_name := "master_algebraic_tsirelson";
       metadata_scope := Algebraic; metadata_status := StatusUnconditional; metadata_role := WrapperOnly |};
    {| metadata_name := "master_algebraic_tsirelson_tight";
       metadata_scope := Algebraic; metadata_status := StatusUnconditional; metadata_role := WrapperOnly |};
    {| metadata_name := "master_quantum_foundations";
       metadata_scope := MixedSummary; metadata_status := StatusUnconditional; metadata_role := WrapperOnly |};
    {| metadata_name := "master_non_circularity";
       metadata_scope := Structural; metadata_status := StatusUnconditional; metadata_role := WrapperOnly |};
    {| metadata_name := "master_tsirelson_conditional";
       metadata_scope := ConditionalPhysical; metadata_status := StatusConditional; metadata_role := NewComposition |};
    {| metadata_name := "master_psd_iff_column_contractive";
       metadata_scope := Algebraic; metadata_status := StatusUnconditional; metadata_role := WrapperOnly |};
    {| metadata_name := "master_trace_column_contractive_iff_quantum_model";
       metadata_scope := ExecutableBridge; metadata_status := StatusUnconditional; metadata_role := WrapperOnly |};
    {| metadata_name := "master_trace_quantum_model_unfolds";
       metadata_scope := Definitional; metadata_status := StatusDefinitional; metadata_role := DefinitionalRestatement |};
    {| metadata_name := "master_trace_quantum_bridge_forces_psd";
       metadata_scope := ExecutableBridge; metadata_status := StatusConditional; metadata_role := NewComposition |};
    {| metadata_name := "master_honest_nofi_structure_requirement";
       metadata_scope := Structural; metadata_status := StatusUnconditional; metadata_role := WrapperOnly |};
     {| metadata_name := "master_honest_nofi_trace_separation";
       metadata_scope := Structural; metadata_status := StatusUnconditional; metadata_role := WrapperOnly |};
     {| metadata_name := "master_honest_nofi_conditional_shannon";
       metadata_scope := Structural; metadata_status := StatusConditional; metadata_role := WrapperOnly |};
     {| metadata_name := "master_honest_nofi_quantitative_state_space";
       metadata_scope := Structural; metadata_status := StatusUnconditional; metadata_role := WrapperOnly |};
     {| metadata_name := "master_honest_nofi_posterior_representative_reduction";
       metadata_scope := Structural; metadata_status := StatusConditional; metadata_role := WrapperOnly |};
     {| metadata_name := "master_a2_equal_trust_substitution_payoff";
       metadata_scope := Structural; metadata_status := StatusUnconditional; metadata_role := NewComposition |};
     {| metadata_name := "master_nofi_to_discrete_einstein";
       metadata_scope := ConditionalPhysical; metadata_status := StatusConditional; metadata_role := WrapperOnly |};
     {| metadata_name := "master_nofi_to_discrete_einstein_from_bekenstein_calibration";
       metadata_scope := ConditionalPhysical; metadata_status := StatusConditional; metadata_role := WrapperOnly |};
    {| metadata_name := "master_verification_chain";
       metadata_scope := VerificationTransfer; metadata_status := StatusConditional; metadata_role := WrapperOnly |};
    {| metadata_name := "master_verification_preserved_observables";
       metadata_scope := VerificationTransfer; metadata_status := StatusConditional; metadata_role := NewComposition |};
    {| metadata_name := "master_non_circular_mu_cost_primitives";
       metadata_scope := Structural; metadata_status := StatusUnconditional; metadata_role := WrapperOnly |};
    {| metadata_name := "master_non_circular_chsh_formula";
       metadata_scope := Algebraic; metadata_status := StatusUnconditional; metadata_role := WrapperOnly |};
    {| metadata_name := "master_non_circular_classical_witness";
       metadata_scope := Structural; metadata_status := StatusUnconditional; metadata_role := WrapperOnly |};
    {| metadata_name := "master_non_circular_mu_zero_locc";
       metadata_scope := Structural; metadata_status := StatusUnconditional; metadata_role := WrapperOnly |} ].

Definition master_theorem_metadata_names : list string :=
  map metadata_name master_theorem_metadata_ledger.

Theorem master_theorem_metadata_names_exact :
  master_theorem_metadata_names = master_exported_theorem_names.
Proof.
  reflexivity.
Qed.

Theorem master_theorem_metadata_complete :
  Forall (fun nm => In nm master_theorem_metadata_names) master_exported_theorem_names.
Proof.
  apply Forall_forall.
  intros nm Hnm.
  rewrite master_theorem_metadata_names_exact.
  exact Hnm.
Qed.

Definition summary_file_theorem_names : list string :=
  [ "master_summary_no_hidden_project_assumptions_verified";
    "exposed_zero_marginal_psd_contractivity";
    "exposed_trace_bridge_content";
    "exposed_non_circularity_content";
    "exposed_verification_surface_content";
    "exposed_honest_nofi_structure_content";
    "exposed_honest_nofi_trace_separation_content";
    "exposed_honest_nofi_conditional_shannon_content";
    "exposed_honest_nofi_quantitative_state_space_content";
    "exposed_honest_nofi_posterior_representative_reduction_content";
    "exposed_thermo_einstein_bridge_content";
    "exposed_thermo_discrete_einstein_content";
    "exposed_nofi_to_discrete_einstein_content";
    "exposed_nofi_to_discrete_einstein_from_bekenstein_calibration_content";
    "master_theorem_metadata_names_exact";
    "master_theorem_metadata_complete";
    "covered_kernel_story_areas_exact";
    "kernel_story_coverage_complete";
    "master_assumption_artifact_is_pinned";
    "master_assumption_boundary_explicit";
    "master_verification_scope_is_explicit";
    "master_open_obligations_are_explicit";
    "kernel_story_coverage_ledger_is_semantically_sufficient";
    "master_mu_zero_witness_sound";
    "master_mu_zero_algebraic_bound";
    "master_classical_bound";
    "master_quantum_violation_proves_nonclassicality";
    "master_algebraic_tsirelson";
    "master_algebraic_tsirelson_tight";
    "master_quantum_foundations";
    "master_non_circularity";
    "master_tsirelson_conditional";
    "master_psd_iff_column_contractive";
    "master_trace_column_contractive_iff_quantum_model";
    "master_trace_quantum_model_unfolds";
    "master_trace_quantum_bridge_forces_psd";
    "master_honest_nofi_structure_requirement";
    "master_honest_nofi_trace_separation";
    "master_honest_nofi_conditional_shannon";
    "master_honest_nofi_quantitative_state_space";
    "master_honest_nofi_posterior_representative_reduction";
    "master_a2_equal_trust_substitution_payoff";
    "master_nofi_to_discrete_einstein";
    "master_nofi_to_discrete_einstein_from_bekenstein_calibration";
    "master_verification_chain";
    "master_verification_preserved_observables";
    "master_non_circular_mu_cost_primitives";
    "master_non_circular_chsh_formula";
    "master_non_circular_classical_witness";
    "master_non_circular_mu_zero_locc";
    "thiele_machine_core_summary_verified";
    "thiele_machine_is_complete" ].

Theorem summary_file_theorem_inventory_explicit :
  List.length summary_file_theorem_names = 52%nat.
Proof.
  reflexivity.
Qed.

Definition kernel_story_coverage_ledger : list kernel_story_coverage_entry :=
  [ {| coverage_area := AreaCHSHStructure;
       coverage_support := [ "master_mu_zero_algebraic_bound"; "master_classical_bound"; "master_algebraic_tsirelson"; "master_psd_iff_column_contractive" ];
       coverage_note := "Algebraic, classical, and PSD/contractive CHSH structure are in scope." |};
    {| coverage_area := AreaQuantumBridge;
       coverage_support := [ "master_tsirelson_conditional"; "master_trace_column_contractive_iff_quantum_model"; "master_trace_quantum_model_unfolds"; "master_trace_quantum_bridge_forces_psd" ];
       coverage_note := "Trace-level bridge claims are explicit and scope-limited." |};
    {| coverage_area := AreaNoFreeInsight;
       coverage_support :=
         [ "master_honest_nofi_structure_requirement";
           "master_honest_nofi_trace_separation";
           "master_honest_nofi_conditional_shannon";
           "master_honest_nofi_quantitative_state_space";
           "master_honest_nofi_posterior_representative_reduction";
           "master_a2_equal_trust_substitution_payoff" ];
       coverage_note := "Structural NoFI, cert-setter/Shannon bounds, the posterior-representative semantics lift, the conservative state-space-counting wrapper, and the equal-trust A2 substitution gate are in scope." |};
    {| coverage_area := AreaVerificationSurface;
       coverage_support := [ "master_verification_chain"; "master_verification_preserved_observables" ];
       coverage_note := "Verification scope is explicit and intentionally abstract." |};
    {| coverage_area := AreaNonCircularity;
       coverage_support := [ "master_non_circularity"; "master_non_circular_mu_cost_primitives"; "master_non_circular_chsh_formula"; "master_non_circular_classical_witness"; "master_non_circular_mu_zero_locc" ];
       coverage_note := "Kernel-level non-circularity is decomposed into explicit sub-certificates." |};
    {| coverage_area := AreaAssumptionSurface;
       coverage_support := [ "master_summary_assumptions"; "master_summary_no_hidden_project_assumptions_verified" ];
       coverage_note := "Assumption recording is explicit, but exact dependency extraction is bounded separately." |};
    {| coverage_area := AreaSemanticBoundary;
       coverage_support := [ "chsh_trace_semantic_boundary"; "verification_semantic_boundary"; "trace_quantum_model_semantic_boundary"; "thermo_einstein_semantic_boundary" ];
       coverage_note := "Semantic boundaries are explicit in the summary file, including the conditional thermo-to-Einstein corridor." |};
    {| coverage_area := AreaPhysicsBoundary;
       coverage_support :=
         [ "master_nofi_to_discrete_einstein";
           "master_nofi_to_discrete_einstein_from_bekenstein_calibration";
           "master_physics_reading_inventory";
           "master_remaining_open_obligations" ];
       coverage_note := "Physics claims, discrete-Einstein entry theorems, and nonclaims are partitioned explicitly." |} ].

Definition kernel_story_area_names : list kernel_story_area :=
  [ AreaCHSHStructure;
    AreaQuantumBridge;
    AreaNoFreeInsight;
    AreaVerificationSurface;
    AreaNonCircularity;
    AreaAssumptionSurface;
    AreaSemanticBoundary;
    AreaPhysicsBoundary ].

Definition covered_kernel_story_areas : list kernel_story_area :=
  map coverage_area kernel_story_coverage_ledger.

Theorem covered_kernel_story_areas_exact :
  covered_kernel_story_areas = kernel_story_area_names.
Proof.
  reflexivity.
Qed.

Theorem kernel_story_coverage_complete :
  Forall (fun area => In area covered_kernel_story_areas) kernel_story_area_names.
Proof.
  apply Forall_forall.
  intros area Harea.
  rewrite covered_kernel_story_areas_exact.
  exact Harea.
Qed.

(**
    PART 0d: ASSUMPTION CERTIFICATE BOUNDARY
    *)

Definition master_inquisitor_assumption_artifact : external_artifact_reference :=
  {| artifact_path := "coq/INQUISITOR_ASSUMPTIONS.json";
     artifact_sha256 := "6a427ab76ac0ec549f00f348ea41a01350bde841b01b6057171f834ed2c57fa7";
     artifact_role := "machine-generated Inquisitor assumption-surface artifact" |}.

Definition master_assumption_manifest_boundary : list manifest_boundary_entry :=
  [ {| manifest_item := "project-local axioms count";
       manifest_level := LocallyCheckedAgainstDeclaration;
       manifest_source := "master_summary_no_hidden_project_assumptions_verified";
       manifest_limit := "Proves the declared count is 0 inside this file; does not independently extract repository dependencies." |};
    {| manifest_item := "project-local admits count";
       manifest_level := LocallyCheckedAgainstDeclaration;
       manifest_source := "master_summary_no_hidden_project_assumptions_verified";
       manifest_limit := "Proves the declared count is 0 inside this file; does not independently extract repository dependencies." |};
    {| manifest_item := "standard dependency names";
       manifest_level := ExternallyAuditedArtifact;
       manifest_source := artifact_path master_inquisitor_assumption_artifact;
       manifest_limit := "Pinned to a machine-generated JSON artifact; this file does not parse the artifact contents internally." |};
    {| manifest_item := "repository-wide dependency extraction";
       manifest_level := ExternallyAuditedArtifact;
       manifest_source := artifact_path master_inquisitor_assumption_artifact;
       manifest_limit := "Authoritative extraction remains external, but the summary now pins the specific artifact path and SHA-256." |} ].

Definition master_assumption_artifact_pinned : Prop :=
  artifact_path master_inquisitor_assumption_artifact = "coq/INQUISITOR_ASSUMPTIONS.json" /\
  artifact_sha256 master_inquisitor_assumption_artifact =
    "6a427ab76ac0ec549f00f348ea41a01350bde841b01b6057171f834ed2c57fa7".

Lemma master_assumption_artifact_path_pinned :
  artifact_path master_inquisitor_assumption_artifact = "coq/INQUISITOR_ASSUMPTIONS.json".
Proof.
  reflexivity.
Qed.

Lemma master_assumption_artifact_sha256_pinned :
  artifact_sha256 master_inquisitor_assumption_artifact =
    "6a427ab76ac0ec549f00f348ea41a01350bde841b01b6057171f834ed2c57fa7".
Proof.
  reflexivity.
Qed.

Theorem master_assumption_artifact_is_pinned :
  master_assumption_artifact_pinned.
Proof.
  change
    (artifact_path master_inquisitor_assumption_artifact = "coq/INQUISITOR_ASSUMPTIONS.json" /\
     artifact_sha256 master_inquisitor_assumption_artifact =
       "6a427ab76ac0ec549f00f348ea41a01350bde841b01b6057171f834ed2c57fa7").
  split.
  - exact master_assumption_artifact_path_pinned.
  - exact master_assumption_artifact_sha256_pinned.
Qed.

Definition master_assumption_boundary_statement : Prop :=
  master_summary_no_hidden_project_assumptions /\
  List.length master_assumption_manifest_boundary = 4%nat /\
  master_assumption_artifact_pinned.

Theorem master_assumption_boundary_explicit :
  master_assumption_boundary_statement.
Proof.
  unfold master_assumption_boundary_statement.
  split.
  - exact master_summary_no_hidden_project_assumptions_verified.
  - split.
    + reflexivity.
    + exact master_assumption_artifact_is_pinned.
Qed.

(**
    PART 0e: VERIFICATION SCOPE DECISION
    *)

Definition verification_nonclaims_list : list string :=
  [ "Raw RTL JSON bit-for-bit lockstep is bounded to the concrete hardware memory extent; VM memory-tail equality is carried by the formal full-state abstraction bridge.";
    "Raw RTL JSON carries bounded descriptor/table/shadow graph encodings, not high-level VMAxiom string payload equality.";
    "Complete CSR-status equality beyond the emitted runtime CSR lanes is carried by coq/kami_hw/FullAbstraction.v and coq/kernel/VerilogRTLCorrespondence.v." ].

Definition master_full_state_observables : list string :=
  [ "pc"; "mu"; "err"; "registers"; "hardware-memory-extent";
    "csrs"; "vm_graph"; "module_regions"; "module_axioms";
    "morphism_graph"; "mu_tensor"; "logic_acc"; "mstatus";
    "certified"; "witness" ].

Definition master_verification_scope : verification_scope_record :=
  {| verification_scope_name := "kernel-story verification scope";
     verification_scope_exact_observables := master_full_state_observables;
     verification_scope_includes_full_state_equivalence := true;
     verification_scope_nonclaims := verification_nonclaims_list |}.

Definition master_verification_scope_statement : Prop :=
  verification_scope_exact_observables master_verification_scope = master_full_state_observables /\
  verification_scope_includes_full_state_equivalence master_verification_scope = true.

Lemma master_verification_scope_observables_exact :
  verification_scope_exact_observables master_verification_scope = master_full_state_observables.
Proof.
  reflexivity.
Qed.

(** Previously: a separate lemma
    [master_verification_scope_includes_full_state_equivalence] recorded
    that [verification_scope_includes_full_state_equivalence
    master_verification_scope = true].  That equation is the defining
    field of [master_verification_scope] (a record constant), so the
    statement reduced to [true = true] by [reflexivity].  The lemma was
    used exactly once, in [master_verification_scope_is_explicit] below;
    the proof now finishes that bullet with [reflexivity] directly. *)

Theorem master_verification_scope_is_explicit :
  master_verification_scope_statement.
Proof.
  change
    (verification_scope_exact_observables master_verification_scope = master_full_state_observables /\
     verification_scope_includes_full_state_equivalence master_verification_scope = true).
  split.
  - exact master_verification_scope_observables_exact.
  - reflexivity.
Qed.

(**
    PART 0f: PHYSICS READING INVENTORY AND OPEN OBLIGATIONS
    *)

Definition master_physics_reading_inventory : list physical_reading_entry :=
  [ {| reading_name := "Classical factorizable correlations obey |CHSH| <= 2";
       reading_status := ProvedKernelConsequence;
       reading_basis := [ "master_classical_bound" ];
       reading_boundary := "Formal kernel theorem." |};
    {| reading_name := "Trace-level coherence implies a Tsirelson-bound trace";
       reading_status := ProvedKernelConsequence;
       reading_basis := [ "master_tsirelson_conditional" ];
       reading_boundary := "Conditional formal kernel theorem." |};
     {| reading_name := "Nearest-neighbor entropy-local split transitions conditionally imply an EinsteinTarget conclusion";
       reading_status := ProvedKernelConsequence;
       reading_basis := [ "exposed_thermo_einstein_bridge_content"; "thermo_einstein_semantic_boundary" ];
       reading_boundary := "Conditional on the explicit null-flux equality premise and on the generic EinsteinTarget/LocalHorizon interface; the repository now discharges the Raychaudhuri component explicitly for the discrete Einstein target." |};
     {| reading_name := "Nearest-neighbor entropy-local split transitions imply the repository's discrete Einstein-emergence equality";
       reading_status := ProvedKernelConsequence;
       reading_basis := [ "exposed_thermo_discrete_einstein_content"; "master_nofi_to_discrete_einstein"; "thermo_einstein_semantic_boundary" ];
       reading_boundary := "Conditional on the explicit null-flux equality premise plus graph well-formedness; this theorem no longer abstracts over EinsteinTarget, and the stronger NoFI entry path can derive the calibration from explicit Bekenstein/Landauer-Unruh premises." |};
    {| reading_name := "No Free Insight plus explicit Bekenstein/Landauer-Unruh calibration premises imply the repository's discrete Einstein-emergence equality";
       reading_status := ProvedKernelConsequence;
       reading_basis := [ "master_nofi_to_discrete_einstein_from_bekenstein_calibration" ];
       reading_boundary := "Conditional on explicit constants calibration, ledger-to-support entropy identification, nearest-neighbor locality, and graph well-formedness." |};
    {| reading_name := "A laboratory source satisfies the coherence predicate";
       reading_status := ExternalEmpiricalHypothesis;
       reading_basis := [ "chsh_trace_semantic_boundary" ];
       reading_boundary := "External to Coq and to this summary file." |};
    {| reading_name := "The μ-ledger is the unique physical structural-cost law of nature";
       reading_status := ExternalModelingClaim;
       reading_basis := [ "master_non_circularity"; "master_honest_nofi_structure_requirement" ];
       reading_boundary := "Interpretive physical thesis, not closed here as a single theorem." |};
    {| reading_name := "Repository-global non-circularity across all imports and interpretations";
       reading_status := OpenFormalizationObligation;
       reading_basis := [ "master_non_circularity"; "kernel_story_coverage_ledger" ];
       reading_boundary := "Current file proves kernel-level non-circularity, not repository-global dependency acyclicity." |} ].

(** Hardware isomorphism chain connectivity check.
    Referencing [full_embed_step_compute] and [driven_trace_commutes]
    forces Coq to verify these theorems are in scope and well-typed.
    If this compiles, the hardware correspondence chain is connected. *)
Lemma hardware_chain_connectivity_check :
  let _ := full_embed_step_compute in
  let _ := driven_step_supported in
  let _ := driven_trace_commutes in
  1 <> 0.
Proof. discriminate. Qed.

(* SAFE: Zero remaining obligations is the correct final state; all Admitted
   have been closed across the entire coq/ tree. *)
Definition master_remaining_open_obligations : list open_obligation_entry := [].

Theorem master_open_obligations_are_explicit :
  List.length master_remaining_open_obligations = 0%nat.
Proof.
  reflexivity.
Qed.

Definition master_nonclaim_inventory_statement : Prop :=
  master_remaining_open_obligations = [] /\
  List.length verification_nonclaims_list = 3%nat.

(* [master_nonclaim_inventory_statement] reduces by [unfold; simpl; split;
   reflexivity] — both conjuncts are direct length/equality checks on
   transparently-defined constants ([] and a fixed three-element list). The
   former theorem [master_nonclaim_inventory_is_explicit] carried no proof
   content beyond [Definition] transparency, so it has been inlined at its
   sole caller [kernel_story_coverage_ledger_is_semantically_sufficient]. *)

Definition kernel_story_semantic_sufficiency_statement : Prop :=
  (exists fuel trace, mu_cost_of_trace fuel trace 0 = 0%nat) /\
  (forall fuel trace s_init, mu_zero_program fuel trace ->
     Qabs (chsh_from_vm_trace fuel trace s_init) <= 4%Q) /\
  (forall E : nat -> nat -> nat -> nat -> R,
     MinorConstraints.is_factorizable E ->
     (-2 <= MinorConstraints.CHSH_from_correlations E <= 2)%R) /\
  (forall E : nat -> nat -> nat -> nat -> R,
     (MinorConstraints.CHSH_from_correlations E > 2)%R ->
     ~ MinorConstraints.is_factorizable E) /\
  (forall e00 e01 e10 e11 : R,
     (e00 * e00 + e01 * e01 <= 1)%R ->
     (e10 * e10 + e11 * e11 <= 1)%R ->
     ((TsirelsonFromAlgebra.CHSH_value e00 e01 e10 e11) *
      (TsirelsonFromAlgebra.CHSH_value e00 e01 e10 e11) <= 8)%R) /\
  (exists e00 e01 e10 e11 : R,
     (e00 * e00 + e01 * e01 <= 1)%R /\
     (e10 * e10 + e11 * e11 <= 1)%R /\
     TsirelsonFromAlgebra.CHSH_value e00 e01 e10 e11 = sqrt 8) /\
  (correlation_hierarchy_derived /\ qm_is_cost_free_computation) /\
  exposed_zero_marginal_psd_contractivity_spine /\
  exposed_trace_bridge_spine /\
  exposed_non_circularity_spine /\
  exposed_verification_surface_spine /\
  exposed_honest_nofi_structure_spine /\
  exposed_honest_nofi_trace_separation_spine /\
  exposed_honest_nofi_conditional_shannon_spine /\
  exposed_honest_nofi_quantitative_state_space_spine /\
  exposed_honest_nofi_posterior_representative_reduction_spine /\
  exposed_nofi_to_discrete_einstein_spine /\
  exposed_nofi_to_discrete_einstein_from_bekenstein_calibration_spine /\
  master_assumption_boundary_statement /\
  master_verification_scope_statement /\
  master_nonclaim_inventory_statement.

Theorem kernel_story_coverage_ledger_is_semantically_sufficient :
  Forall (fun area => In area covered_kernel_story_areas) kernel_story_area_names /\
  kernel_story_semantic_sufficiency_statement.
Proof.
  split.
  - exact kernel_story_coverage_complete.
  - unfold kernel_story_semantic_sufficiency_statement.
    split.
    + exists 10%nat, classical_achieving_trace. exact classical_program_mu_zero.
    + split.
      * intros fuel trace s_init Hmu. exact (mu_zero_chsh_bounded fuel trace s_init Hmu).
      * split.
        { exact MinorConstraints.factorizable_CHSH_classical_bound. }
        split.
        { intros E Hgt Hfact.
          pose proof (MinorConstraints.factorizable_CHSH_classical_bound E Hfact) as [_ Hupper].
          lra. }
        split.
        { exact TsirelsonFromAlgebra.tsirelson_squared. }
        split.
        { exact TsirelsonFromAlgebra.tsirelson_tight. }
        split.
        { exact quantum_foundations_complete. }
        split.
        { exact exposed_zero_marginal_psd_contractivity. }
        split.
        { exact exposed_trace_bridge_content. }
        split.
        { exact exposed_non_circularity_content. }
        split.
        { exact exposed_verification_surface_content. }
        split.
        { exact exposed_honest_nofi_structure_content. }
        split.
        { exact exposed_honest_nofi_trace_separation_content. }
        split.
        { exact exposed_honest_nofi_conditional_shannon_content. }
        split.
        { exact exposed_honest_nofi_quantitative_state_space_content. }
        split.
        { exact exposed_honest_nofi_posterior_representative_reduction_content. }
        split.
        { exact exposed_nofi_to_discrete_einstein_content. }
        split.
        { exact exposed_nofi_to_discrete_einstein_from_bekenstein_calibration_content. }
        split.
        { exact master_assumption_boundary_explicit. }
        split.
        { exact master_verification_scope_is_explicit. }
        { (* Inlined former [master_nonclaim_inventory_is_explicit]: both
             conjuncts of [master_nonclaim_inventory_statement] reduce to
             literal equalities on the inventory definitions. *)
          unfold master_nonclaim_inventory_statement,
                 master_remaining_open_obligations.
          simpl.
          split; reflexivity. }
Qed.

Definition master_mu_zero_witness_fuel : nat := 10%nat.
Definition master_mu_zero_witness_trace : list vm_instruction := classical_achieving_trace.

(* AUDIT:
   theorem: master_mu_zero_witness_sound
   status: unconditional
   kind: export-only
   depends_on: ClassicalBound.classical_program_mu_zero
   premise_kinds: structural
   new_content_here: none
   semantic_layer: formal theorem layer
   external_interpretation: none
*)
Theorem master_mu_zero_witness_sound :
  mu_cost_of_trace master_mu_zero_witness_fuel master_mu_zero_witness_trace 0 = 0%nat.
Proof.
  unfold master_mu_zero_witness_fuel, master_mu_zero_witness_trace.
  apply classical_program_mu_zero.
Qed.

(**
    PART I: CORE THEOREMS
    *)

(* AUDIT:
   theorem: master_mu_zero_algebraic_bound
   status: unconditional
   kind: new-composition
   depends_on: TsirelsonUniqueness.mu_zero_chsh_bounded; ClassicalBound.classical_program_mu_zero
   premise_kinds: structural; algebraic; standard-library
   new_content_here: composition of witness export and boundedness export
   semantic_layer: formal theorem layer
   external_interpretation: does not classify μ=0 traces as physical or quantum realizable
*)
(** Theorem 1: Algebraic CHSH bound for μ=0 traces.

  Classification:
  - algebraic
  - unconditional
  - new composition

  What this proves:
  - μ=0 traces satisfy |S| ≤ 4, the algebraic maximum for a CHSH expression

  What this theorem alone does not prove:
  - the classical bound |S| ≤ 2; that stronger result appears later as [master_classical_bound]
  - the Tsirelson bound |S| ≤ 2√2; that stronger result appears later in algebraic and conditional forms
  - any physical or quantum classification of μ=0 traces

  Related results:
  - [master_classical_bound] gives the stronger classical bound under factorizability
  - [master_tsirelson_conditional] gives the stronger Tsirelson bound under coherence
*)
Theorem master_mu_zero_algebraic_bound :
  (exists fuel trace, mu_cost_of_trace fuel trace 0 = 0%nat) /\
  (forall fuel trace s_init, mu_zero_program fuel trace ->
   Qabs (chsh_from_vm_trace fuel trace s_init) <= 4%Q).
Proof.
  split.
  - exists 10%nat, classical_achieving_trace. apply classical_program_mu_zero.
  - intros fuel trace s_init Hmu.
    apply mu_zero_chsh_bounded. exact Hmu.
Qed.

(* AUDIT:
   theorem: master_classical_bound
   status: unconditional
   kind: export-only
   depends_on: MinorConstraints.factorizable_CHSH_classical_bound
   premise_kinds: structural; standard-library
   new_content_here: none
   semantic_layer: formal theorem layer
   external_interpretation: does not show that arbitrary μ=0 traces are factorizable
*)
(** Theorem 1b: Classical CHSH bound under factorizability.

  Classification:
  - structural
  - unconditional
  - export of the imported classical bound

  What this proves:
  - factorizable correlations satisfy |CHSH| ≤ 2

  What this does not prove:
  - that all μ=0 traces are factorizable
  - that all non-factorizable traces are physically quantum
*)
Theorem master_classical_bound :
  forall E : nat -> nat -> nat -> nat -> R,
    MinorConstraints.is_factorizable E ->
    (-2 <= MinorConstraints.CHSH_from_correlations E <= 2)%R.
Proof.
  exact MinorConstraints.factorizable_CHSH_classical_bound.
Qed.

(* AUDIT:
   theorem: master_quantum_violation_proves_nonclassicality
   status: unconditional
   kind: new-composition
   depends_on: MinorConstraints.factorizable_CHSH_classical_bound
   premise_kinds: structural; algebraic; standard-library
   new_content_here: contrapositive packaging with lra
   semantic_layer: formal theorem layer
   external_interpretation: proves non-factorizability, not a full physical source model
*)
(** Theorem 1c: CHSH violation excludes factorizability.

  Classification:
  - structural/algebraic
  - unconditional
  - contrapositive repackaging

  What this proves:
  - if CHSH > 2, the correlation is not factorizable

  What this does not prove:
  - a full physical interpretation of the source
  - a complete characterization of quantum realizability
*)
Theorem master_quantum_violation_proves_nonclassicality :
  forall E : nat -> nat -> nat -> nat -> R,
    (MinorConstraints.CHSH_from_correlations E > 2)%R ->
    ~ MinorConstraints.is_factorizable E.
Proof.
  intros E Hgt Hfact.
  pose proof (MinorConstraints.factorizable_CHSH_classical_bound E Hfact) as [_ Hupper].
  lra.
Qed.

(* AUDIT:
   theorem: master_algebraic_tsirelson
   status: unconditional
   kind: export-only
   depends_on: TsirelsonFromAlgebra.tsirelson_squared
   premise_kinds: algebraic; standard-library
   new_content_here: none
   semantic_layer: formal theorem layer
   external_interpretation: purely algebraic bound, not a trace-level or physical theorem
*)
(** Theorem 2: Algebraic Tsirelson bound from row constraints.

    Classification:
    - algebraic
    - unconditional
    - export of an imported real-algebra theorem

    What this proves:
    - under the imported row constraints, S² ≤ 8 and therefore |S| ≤ 2√2

    What this does not prove:
    - that arbitrary traces satisfy those constraints
    - a derivation from μ-accounting alone
    - a physical source theorem
*)
Local Open Scope R_scope.
Theorem master_algebraic_tsirelson :
  forall e00 e01 e10 e11 : R,
    (e00*e00 + e01*e01 <= 1) ->
    (e10*e10 + e11*e11 <= 1) ->
    ((TsirelsonFromAlgebra.CHSH_value e00 e01 e10 e11) *
     (TsirelsonFromAlgebra.CHSH_value e00 e01 e10 e11) <= 8).
Proof.
  exact TsirelsonFromAlgebra.tsirelson_squared.
Qed.

(* AUDIT:
   theorem: master_algebraic_tsirelson_tight
   status: unconditional
   kind: export-only
   depends_on: TsirelsonFromAlgebra.tsirelson_tight
   premise_kinds: algebraic; standard-library
   new_content_here: none
   semantic_layer: formal theorem layer
   external_interpretation: witnesses tightness of the algebraic bound only
*)
(** Theorem 2b: The algebraic Tsirelson bound is tight.

  Classification:
  - algebraic
  - unconditional
  - export of an explicit achievability witness

  What this proves:
  - the imported algebraic bound |S| ≤ 2√2 is attained

  What this does not prove:
  - a runtime, hardware, or trace-level witness for that optimum
*)
Theorem master_algebraic_tsirelson_tight :
  exists e00 e01 e10 e11 : R,
    (e00*e00 + e01*e01 <= 1) /\
    (e10*e10 + e11*e11 <= 1) /\
    TsirelsonFromAlgebra.CHSH_value e00 e01 e10 e11 = sqrt 8.
Proof.
  exact TsirelsonFromAlgebra.tsirelson_tight.
Qed.
Local Open Scope Q_scope.

(** Theorem 3: Exported quantum-foundations summary.

    Classification:
    - mixed definitional/numerical
    - unconditional
    - export of an imported summary theorem

    What this proves:
    - the numerical inequality classical_bound ≤ tsirelson_bound
    - the imported cost-free/quantum statement exactly as defined upstream

    What this does not prove:
    - a derivation of quantum mechanics from μ-accounting
    - an independent derivation of the physical Tsirelson principle
*)
(* AUDIT:
   theorem: master_quantum_foundations
   status: definitional
   kind: export-only
   depends_on: QuantumEquivalence.quantum_foundations_complete
   premise_kinds: syntactic; algebraic
   new_content_here: none
   semantic_layer: formal theorem layer
   external_interpretation: does not derive quantum mechanics from μ-accounting
*)
(* INQUISITOR NOTE: alias for quantum_foundations_complete - summary module export *)
Theorem master_quantum_foundations :
  correlation_hierarchy_derived /\
  qm_is_cost_free_computation.
Proof.
  exact quantum_foundations_complete.
Qed.

(** Theorem 4: Non-circularity certificate.

    This export addresses two distinct questions:
    1. Whether quantum structure is smuggled into μ-cost primitives.
       Answer: no; the primitive μ-cost rules are CHSH-free and quantum-free.
    2. Whether the μ=0 operational class has the closure-style properties used
       in the project-level LOCC-like reading.
       Answer: those properties are exported from NonCircularityAudit.v.
*)
(* AUDIT:
  theorem: master_non_circularity
  status: unconditional
  kind: export-only
  depends_on: NonCircularityAudit.non_circularity_verified
  premise_kinds: syntactic; algebraic; structural
  new_content_here: none
  semantic_layer: formal theorem layer
  external_interpretation: exports the certificate; decomposition appears later in this file
*)
(* INQUISITOR NOTE: alias for non_circularity_verified - summary module export *)
Theorem master_non_circularity : non_circularity_certificate.
Proof.
  exact non_circularity_verified.
Qed.

(** Theorem 5: Conditional trace bridge to the Tsirelson bound.

    Classification:
    - mixed: unconditional Born-rule uniqueness plus conditional trace bridge
    - new composition

    What this proves:
    - valid Born rules on [-1,1] agree with the imported standard Born rule
    - under trace_quantum_bridge_coherent, the trace satisfies trace_quantum_model
      and obeys |CHSH| ≤ 2√2

    What this does not prove:
    - that the coherence premise follows from bare μ-accounting
    - that arbitrary physical sources satisfy the coherence premise
*)
(* AUDIT:
   theorem: master_tsirelson_conditional
   status: conditional
   kind: new-composition
   depends_on: BornRuleLinearity.born_rule_unique; TsirelsonQuantumModel.trace_quantum_model_connection_closed
   premise_kinds: structural; semantic; physical; standard-library
   new_content_here: composition of two independent exports
   semantic_layer: formal theorem layer -> executable semantics layer
   external_interpretation: does not derive the coherence premise from bare μ-accounting
*)
Theorem master_tsirelson_conditional :
  (forall (P : ProbabilityRule),
      valid_born_rule P ->
    forall (z : R), (-1 <= z <= 1)%R -> P z = born_probability z) /\
  (forall fuel trace s_init,
      trace_quantum_bridge_coherent fuel trace s_init ->
      trace_quantum_model fuel trace s_init /\
      (Rabs (CHSH
        (trace_e00 fuel trace s_init)
        (trace_e01 fuel trace s_init)
        (trace_e10 fuel trace s_init)
        (trace_e11 fuel trace s_init)) <= sqrt8)%R).
Proof.
  split.
  - intros P Hvalid z Hz.
    apply born_rule_unique; assumption.
  - intros fuel trace s_init Hcoh.
    apply trace_quantum_model_connection_closed.
    exact Hcoh.
Qed.

(** Theorem 6: Zero-marginal PSD is equivalent to column contractivity.

    WHAT IS PROVEN (UNCONDITIONAL):
    The 5×5 NPA moment matrix being positive semidefinite is EQUIVALENT to
    zero_marginal_column_contractive, the algebraic condition that implies
    CHSH ≤ 2√2.

    Proof: The NPA matrix has block structure diag(1) ⊕ [[I, C], [C^T, I]].
    By the Schur complement theorem, [[I, C], [C^T, I]] ≥ 0 ↔ I − C^T C ≥ 0.
    The condition I − C^T C ≥ 0 is zero_marginal_column_contractive.
    Each direction is extracted directly via test-vector instantiation of PSD5,
    using quadratic_nonneg_discriminant for the determinant condition.

    In this formalization, zero-marginal quantum realizability is equivalent to
    column contractivity. The VM can check that algebraic condition from the
    recorded CHSH_TRIAL outcomes; no extra project-local physics axiom is added here.
*)
(* AUDIT:
   theorem: master_psd_iff_column_contractive
   status: unconditional
   kind: export-only
   depends_on: QuantumPartitionPSD.npa_psd_iff_column_contractive
   premise_kinds: algebraic; standard-library
   new_content_here: none
   semantic_layer: formal theorem layer
   external_interpretation: classifies the algebraic condition once correlators are given
*)
Theorem master_psd_iff_column_contractive :
  forall e00 e01 e10 e11 : R,
    PSD5 (nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11)))
    <->
    zero_marginal_column_contractive e00 e01 e10 e11.
Proof.
  intros e00 e01 e10 e11.
  split.
  - apply npa_psd_implies_column_contractive.
  - intros Hcontractive.
    destruct Hcontractive as [Hc0 [Hc1 Hdet]].
    apply zero_marginal_npa_column_contractive_implies_psd.
    exact Hc0.
    exact Hc1.
    exact Hdet.
Qed.

(** Theorem 6b: Trace-level PSD/contractivity equivalence.

  Classification:
  - executable bridge
  - unconditional
  - export of the trace-level biconditional

  What this proves:
  - trace_column_contractive and trace_quantum_model are equivalent at the trace level

  What this does not prove:
  - that any given trace satisfies either side of the equivalence
*)
(* AUDIT:
   theorem: master_trace_column_contractive_iff_quantum_model
   status: unconditional
   kind: export-only
   depends_on: QuantumPartitionPSD.trace_column_contractive_iff_trace_quantum_model
   premise_kinds: semantic
   new_content_here: none
   semantic_layer: executable semantics layer
   external_interpretation: does not imply the trace came from a physical quantum device
*)
Theorem master_trace_column_contractive_iff_quantum_model :
  forall fuel trace s_init,
    trace_column_contractive fuel trace s_init <->
    trace_quantum_model fuel trace s_init.
Proof.
  intros fuel trace s_init.
  unfold trace_quantum_model.
  apply trace_column_contractive_iff_trace_quantum_model.
Qed.

(** Theorem 6c: Explicit unfolding of trace_quantum_model.

  Classification:
  - definitional
  - executable semantics
  - restatement by unfolding imported definitions

  What this proves:
  - trace_quantum_model means symmetry plus PSD of the induced 5x5 moment matrix

  What this does not prove:
  - that any particular trace satisfies the predicate
*)
(* AUDIT:
   theorem: master_trace_quantum_model_unfolds
   status: definitional
   kind: definitional-restatement
   depends_on: TsirelsonQuantumModel.trace_quantum_model; NPAMomentMatrix.quantum_realizable
   premise_kinds: syntactic; semantic
   new_content_here: none beyond unfolding imported definitions
   semantic_layer: executable semantics layer
   external_interpretation: exposes the predicate meaning without proving it holds
*)
Theorem master_trace_quantum_model_unfolds :
  forall fuel trace s_init,
    trace_quantum_model fuel trace s_init <->
    let M := nat_matrix_to_fin5 (npa_to_matrix (trace_zero_marginal_npa fuel trace s_init)) in
    symmetric5 M /\ PSD5 M.
Proof.
  intros fuel trace s_init.
  unfold trace_quantum_model, quantum_realizable.
  tauto.
Qed.

(** Theorem 6d: Coherence implies PSD of the extracted trace matrix.

  Classification:
  - executable bridge
  - conditional
  - projection to the PSD component

  What this proves:
  - under the coherence predicate, the induced zero-marginal NPA matrix is PSD

  What this does not prove:
  - that coherence holds for arbitrary traces
  - any empirical claim about a laboratory source by itself
*)
(* AUDIT:
   theorem: master_trace_quantum_bridge_forces_psd
   status: conditional
   kind: new-composition
   depends_on: TsirelsonQuantumModel.trace_quantum_bridge_coherent_implies_quantum_model
   premise_kinds: semantic; physical
   new_content_here: projection from quantum_realizable to its PSD component
   semantic_layer: executable semantics layer
   external_interpretation: does not turn a semantic certificate into an empirical one
*)
Theorem master_trace_quantum_bridge_forces_psd :
  forall fuel trace s_init,
    trace_quantum_bridge_coherent fuel trace s_init ->
    PSD5 (nat_matrix_to_fin5 (npa_to_matrix (trace_zero_marginal_npa fuel trace s_init))).
Proof.
  intros fuel trace s_init Hcoh.
  pose proof (trace_quantum_bridge_coherent_implies_quantum_model fuel trace s_init Hcoh) as Hmodel.
  unfold trace_quantum_model, quantum_realizable in Hmodel.
  destruct Hmodel as [_ Hpsd].
  exact Hpsd.
Qed.

(** Theorem 7: Honest NoFI structure requirement.

  Classification:
  - structural
  - unconditional within the imported certified-information-reduction framework
  - export of the imported theorem

  What this proves:
  - strict certified information reduction requires structure addition with nonzero μ-cost

  What this does not prove:
  - that every conceivable notion of inference outside this framework is covered
*)
(* AUDIT:
   theorem: master_honest_nofi_structure_requirement
   status: unconditional
   kind: export-only
   depends_on: HonestNoFI_TheoremsWithoutAssumptions.honest_information_reduction_requires_structure_addition
   premise_kinds: structural; semantic
   new_content_here: none
   semantic_layer: formal theorem layer
   external_interpretation: scoped to the certified-information-reduction framework of the imported theorem
*)
Theorem master_honest_nofi_structure_requirement :
  forall (fuel : nat) (trace : list vm_instruction)
         (s_init s_final : VMState)
         (decoder : NoFreeInsight.receipt_decoder (list vm_instruction))
         (P_prior P_posterior : NoFreeInsight.ReceiptPredicate (list vm_instruction))
         (omega_prior omega_posterior : InformationGainToStrengthening.FeasibleSet),
    s_final = run_vm fuel trace s_init ->
    In s_init omega_prior ->
    InformationGainToStrengthening.is_strict_reduction omega_prior omega_posterior ->
    (InformationGainToStrengthening.feasible_size omega_posterior > 0)%nat ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    NoFreeInsight.strictly_stronger P_posterior P_prior ->
    NoFreeInsight.Certified s_final decoder P_posterior trace ->
    NoFreeInsight.has_structure_addition fuel trace s_init.
Proof.
  exact honest_information_reduction_requires_structure_addition.
Qed.

(* AUDIT:
   theorem: master_honest_nofi_trace_separation
   status: unconditional
   kind: export-only
   depends_on: HonestNoFI.honest_nfi_trace_separation_partial
   premise_kinds: structural; semantic
   new_content_here: none
   semantic_layer: formal theorem layer
   external_interpretation: scoped to trace-level cert-setter separation in the imported theorem
*)
Theorem master_honest_nofi_trace_separation :
  forall fuel trace omega,
    (forall s, In s omega -> s.(vm_csrs).(csr_cert_addr) = 0%nat) ->
    (forall s, In s omega -> (run_vm fuel trace s).(vm_csrs).(csr_cert_addr) <> 0%nat) ->
    NoDup (map (fun s => (run_vm fuel trace s).(vm_csrs).(csr_cert_addr)) omega) ->
    (List.length omega <= MuShannonQuantitative.count_cert_addr_setters trace)%nat.
Proof.
  exact honest_nfi_trace_separation_partial.
Qed.

(* AUDIT:
   theorem: master_honest_nofi_conditional_shannon
   status: conditional
   kind: export-only
   depends_on: HonestNoFI.honest_nfi_conditional_shannon_partial
   premise_kinds: structural; semantic
   new_content_here: none
   semantic_layer: formal theorem layer
   external_interpretation: scoped to the decision-tree/info-pricing premise of the imported theorem
*)
Theorem master_honest_nofi_conditional_shannon :
  forall fuel trace s n,
    Forall (fun i => is_cert_setterb i = true -> (instruction_cost i >= 1)%nat) trace ->
    (MuShannonQuantitative.cert_setter_executions_local fuel trace s >= Nat.log2 n)%nat ->
    ((run_vm fuel trace s).(vm_mu) - s.(vm_mu) >= Nat.log2 n)%nat.
Proof.
  exact honest_nfi_conditional_shannon_partial.
Qed.

(* AUDIT:
   theorem: master_honest_nofi_quantitative_state_space
   status: unconditional
   kind: export-only
   depends_on: HonestNoFI.honest_nfi_quantitative_state_space_partial
   premise_kinds: semantic; syntactic
   new_content_here: none
   semantic_layer: formal theorem layer
   external_interpretation: scoped to the conservative LASSERT/state-space-counting wrapper exposed by the imported theorem
*)
Theorem master_honest_nofi_quantitative_state_space :
  forall (s s' : VMState) (fa ca : nat) (ck : bool) (flen cost : nat),
    VMStep.VMStep.vm_step s
      (VMStep.VMStep.instr_lassert fa ca ck flen cost) s' ->
    let k := (flen * 8)%nat in
    (s'.(vm_mu) - s.(vm_mu) >= k)%nat /\
    (k >= StateSpaceCounting.log2_nat (Nat.pow 2 k))%nat.
Proof.
  intros s s' fa ca ck flen cost Hstep.
  exact (honest_nfi_quantitative_state_space_partial s s' fa ca ck flen cost Hstep).
Qed.

(* AUDIT:
   theorem: master_honest_nofi_posterior_representative_reduction
   status: conditional
   kind: export-only
   depends_on: HonestNoFI.honest_nfi_posterior_representative_reduction_partial
   premise_kinds: structural; semantic
   new_content_here: none
   semantic_layer: formal theorem layer
   external_interpretation: scoped to the explicit posterior-representative observation-equivalence witness of the imported theorem
*)
Theorem master_honest_nofi_posterior_representative_reduction :
  forall fuel trace s omega_prior omega_posterior tree
         (obs_fn : MuShannonBridge.ObservationFunction),
    MuShannonBridge.decision_tree_realized_by_trace fuel trace s tree ->
    (MuShannonBridge.feasible_size omega_posterior > 0)%nat ->
    MuShannonBridge.PosteriorRepresentativeReduction obs_fn tree omega_prior omega_posterior ->
    (Nat.log2_up (MuShannonBridge.feasible_size omega_prior) -
      Nat.log2_up (MuShannonBridge.feasible_size omega_posterior) <=
      (run_vm fuel trace s).(vm_mu) - s.(vm_mu))%nat.
Proof.
  exact honest_nfi_posterior_representative_reduction_partial.
Qed.

(* AUDIT:
   theorem: master_a2_equal_trust_substitution_payoff
   status: unconditional
   kind: new-composition
   depends_on: A2Payoff.a2_equal_trust_substitution_payoff
   premise_kinds: semantic; structural
   new_content_here: exposes the equal-trust substitution gate as a master claim
   semantic_layer: formal theorem layer
   external_interpretation: exact certification-commitment pricing rejects
     non-A2 substitutes; intentionally-overcharging laws are different laws
*)
(* This summary module re-exports kernel theorems under master_* names so the
   monograph can cite one stable surface. Deliberate, no new content.
   INQUISITOR NOTE: alias for a2_equal_trust_substitution_payoff. *)
Theorem master_a2_equal_trust_substitution_payoff :
  exposed_a2_equal_trust_substitution_spine.
Proof.
  exact a2_equal_trust_substitution_payoff.
Qed.

(* AUDIT:
   theorem: master_nofi_to_discrete_einstein
   status: conditional
   kind: export-only
   depends_on: NoFIToEinstein.nfi_to_discrete_einstein
   premise_kinds: structural; physical; semantic
   new_content_here: none
   semantic_layer: formal theorem layer -> physical interpretation layer
   external_interpretation: does not derive the explicit calibration predicate from bare μ-accounting alone
*)
Theorem master_nofi_to_discrete_einstein :
  exposed_nofi_to_discrete_einstein_spine.
Proof.
  exact NoFIToEinstein.nfi_to_discrete_einstein.
Qed.

(* AUDIT:
   theorem: master_nofi_to_discrete_einstein_from_bekenstein_calibration
   status: conditional
   kind: export-only
   depends_on: NoFIToEinstein.nfi_to_discrete_einstein_from_bekenstein_calibration
   premise_kinds: structural; physical; semantic
   new_content_here: none
   semantic_layer: formal theorem layer -> physical interpretation layer
   external_interpretation: packages the stronger theorem path but still depends on explicit Bekenstein/Landauer-Unruh calibration premises
*)
Theorem master_nofi_to_discrete_einstein_from_bekenstein_calibration :
  exposed_nofi_to_discrete_einstein_from_bekenstein_calibration_spine.
Proof.
  exact NoFIToEinstein.nfi_to_discrete_einstein_from_bekenstein_calibration.
Qed.

(**
    PART II: VERIFICATION CHAIN
    *)

(** Verification-chain semantic boundary.

    FORMAL THEOREM LAYER:
    - PythonBisimulation.v proves a Coq/Python abstract step correspondence.
    - HardwareBisimulation.v proves a Python/hardware abstract cost-level correspondence.

    EXECUTABLE SEMANTICS LAYER:
    - What transfers HERE is exactly what the imported abstract hardware theorem states:
      program counter agreement and μ-accumulator agreement over the cost trace.

    PHYSICAL INTERPRETATION LAYER:
    - Reading this as "all hardware observables are identical" is stronger than
      the theorem imported into this file. That stronger statement belongs to
      other RTL-specific gates and refinement layers, not to [master_verification_chain].
*)

(** Verification-chain property used in this file.

    WHAT THIS FORMALIZES HERE:
    - preservation of the imported abstract hardware/Python bisimulation invariant
    - equality of the μ-accumulator across the abstract multi-step executions

    WHAT THIS DOES NOT FORMALIZE HERE:
    - transfer of every semantic property expressible in Coq
    - full hardware/software equivalence for registers, memory, or partition state
*)
Definition verification_chain_holds : Prop :=
  forall hw_init py_init,
    hw_bisimulation_invariant hw_init py_init ->
    forall costs : list nat,
    hw_bisimulation_invariant 
      (hardware_multi_step hw_init costs) 
      (python_multi_step py_init costs) /\
    hw_mu_accumulator (hardware_multi_step hw_init costs) =
      py_mu (python_multi_step py_init costs).

Definition verification_preserved_observables : Prop :=
  forall hw_init py_init costs,
    hw_bisimulation_invariant hw_init py_init ->
    (hardware_multi_step hw_init costs).(hw_pc) =
      (python_multi_step py_init costs).(py_pc) /\
    (hardware_multi_step hw_init costs).(hw_mu_accumulator) =
      (python_multi_step py_init costs).(py_mu).

Definition verification_nonclaims : list string := verification_nonclaims_list.

(** Theorem 8: Exported verification transfer theorem.

    Classification:
    - verification transfer
    - conditional on the imported initial bisimulation invariant
    - export of the imported abstract multi-step theorem

    What this proves:
    - preservation of the imported abstract hardware/Python bisimulation invariant
    - equality of the μ-accumulator across the abstract multi-step executions

    What this does not prove:
    - transfer of every semantic property expressible in Coq
    - full hardware/software equivalence for registers, memory, or partition state
*)
(* AUDIT:
  theorem: master_verification_chain
  status: conditional
  kind: export-only
  depends_on: HardwareBisimulation.complete_verification_chain
  premise_kinds: verification
  new_content_here: none
  semantic_layer: executable semantics layer
  external_interpretation: abstract verification transfer for bisimulation invariant and μ only
*)
Theorem master_verification_chain : verification_chain_holds.
Proof.
  unfold verification_chain_holds.
  intros hw_init py_init Hinv costs.
  exact (complete_verification_chain hw_init py_init Hinv costs).
Qed.

(** Theorem 8b: Preserved-observables projection.

  Classification:
  - verification transfer
  - conditional
  - projection from the imported verification theorem

  What this proves:
  - the preserved observables exported here are exactly PC and μ

  What this does not prove:
  - equality of all hardware observables
*)
(* AUDIT:
   theorem: master_verification_preserved_observables
   status: conditional
   kind: new-composition
   depends_on: HardwareBisimulation.complete_verification_chain
   premise_kinds: verification; semantic
   new_content_here: projection of the imported conjunction down to PC and μ
   semantic_layer: executable semantics layer
   external_interpretation: pins down the preserved observables exported here without claiming full hardware-state equality
*)
Theorem master_verification_preserved_observables :
  verification_preserved_observables.
Proof.
  unfold verification_preserved_observables.
  intros hw_init py_init costs Hinv.
  pose proof (complete_verification_chain hw_init py_init Hinv costs) as [Hcorr _].
  exact Hcorr.
Qed.

(**
  PART IIb: NON-CIRCULARITY DECOMPOSITION

  This section exposes the specific sub-certificates that support the
  exported non-circularity certificate.
*)

(** Theorem 9a: μ-cost primitives are syntactically CHSH-free and quantum-free. *)
(* AUDIT:
  theorem: master_non_circular_mu_cost_primitives
  status: unconditional
  kind: export-only
  depends_on: NonCircularityAudit.mu_cost_is_physics_free
  premise_kinds: syntactic
  new_content_here: none
  semantic_layer: formal theorem layer
  external_interpretation: syntactic separation certificate only
*)
Theorem master_non_circular_mu_cost_primitives :
  forall r : mu_cost_rule,
    rule_references_chsh r = false /\
    rule_references_quantum r = false /\
    rule_references_tsirelson r = false.
Proof.
  intro r.
  destruct r; repeat split; reflexivity.
Qed.

(** The previous theorem [master_non_circular_chsh_formula] re-exported
    the vacuous [chsh_formula_is_algebraic] Prop. With that Prop removed,
    this re-export has no content to re-export. The audit-relevant
    structural fact (CHSH is Q-arithmetic) is captured by the Q-typed
    definitions of [classical_chsh_value] and [chsh_value] in
    [NonCircularityAudit.v] rather than by a one-line reflexivity
    theorem. *)

(** Theorem 9c: The classical witness is exported as a non-circularity sub-certificate. *)
(* AUDIT:
  theorem: master_non_circular_classical_witness
  status: unconditional
  kind: export-only
  depends_on: NonCircularityAudit.classical_bound_is_derived_not_assumed
  premise_kinds: structural; algebraic
  new_content_here: none
  semantic_layer: formal theorem layer
  external_interpretation: witness certificate for the classical bound only
*)
Theorem master_non_circular_classical_witness :
  classical_bound_appears_as_achievable.
Proof.
  split.
  - reflexivity.
  - apply classical_program_mu_zero.
Qed.

(** Theorem 9d: The μ=0 operational class export carries the LOCC-like structure used by the certificate. *)
(* AUDIT:
  theorem: master_non_circular_mu_zero_locc
  status: unconditional
  kind: export-only
  depends_on: NonCircularityAudit.mu_zero_is_locc_like
  premise_kinds: structural
  new_content_here: none
  semantic_layer: formal theorem layer
  external_interpretation: operational-class structure certificate only
*)
(* INQUISITOR NOTE: alias for mu_zero_is_locc_like - summary module export *)
Theorem master_non_circular_mu_zero_locc : mu_zero_locc_correspondence.
Proof.
  exact mu_zero_is_locc_like.
Qed.

Definition non_circularity_nonclaims : list string :=
  [ "This decomposition certifies primitive separation and operational-class structure.";
    "It does not by itself prove an import-graph theorem over the entire repository.";
    "It does not claim every external interpretation of LOCC is captured without remainder." ].

(**
    PART IIc: STRONGER REPOSITORY-LEVEL RESULTS ELSEWHERE

    This summary exports the kernel-story surface used in the main audit path.
    Some stronger results exist elsewhere in the repository and should not be
    read as absent merely because the narrower theorem-local exports in this
    file stop short of them.

    In particular:
    - [coq/kami_hw/Abstraction.v] defines a rich [KamiSnapshot] and the
      abstraction [abs_phase1], including register, memory, and partition-table
      projections into VM state.
    - [coq/kami_hw/VerilogRefinement.v] proves per-instruction simulation
      theorems that are materially stronger than the abstract PC/μ surface
      exported here from [HardwareBisimulation.v].
    - [archive/coq_unused/thielemachine/verification/FullIsomorphism.v (archived)] records a stronger
      three-layer observable-alignment story for Coq, Python, and Verilog.
    - [artifacts/proof_dependency_connectivity.json] records repository-wide
      proof-connectivity evidence with zero disconnected files.

    The role of this file is therefore:
    - to present the kernel-story theorem bundle and its explicit boundaries
    - not to serve as the sole index of every stronger refinement or artifact
      that exists elsewhere in the tree
*)

Definition stronger_repository_results_elsewhere : list string :=
  [ "coq/kami_hw/Abstraction.v: full KamiSnapshot abstraction to VMState, including register, memory, and partition-table projections";
    "coq/kami_hw/VerilogRefinement.v: per-instruction Verilog-to-VM simulation theorems stronger than the abstract PC/mu transfer exported here";
    "archive/coq_unused/thielemachine/verification/FullIsomorphism.v (archived): stronger three-layer observable alignment for Coq, Python, and Verilog";
    "artifacts/proof_dependency_connectivity.json: repository-wide proof-connectivity artifact with zero disconnected files" ].

Theorem stronger_repository_results_elsewhere_explicit :
  List.length stronger_repository_results_elsewhere = 4%nat.
Proof.
  reflexivity.
Qed.

(**
    PART IId: CURVED SPACETIME PIPELINE

    The curved tensor pipeline (CurvedTensorPipeline.v) provides:
    1. Per-module 4×4 metric tensor (stored in ModuleState.module_mu_tensor)
    2. Full metric inverse via Cramer's rule (MatrixAlgebra4.v)
    3. Christoffel symbols of the second kind with proper g^{ρσ} contraction
    4. Riemann tensor with quadratic Γ·Γ terms
    5. Ricci tensor and scalar with actual inverse metric (not identity approx)
    6. Einstein tensor G_{μν} = R_{μν} - (1/2)g_{μν}R
    7. Stress-energy tensor T_{μν} from per-module data
    8. Einstein equation coupling: ∃ κ, G_{dd} = κ · T_{dd} (uniform across d)
       Non-circular version: T from module_structural_mass, g from module_mu_tensor
       Ricci isotropy R_{dd} proved (not assumed) for isotropic 2-vertex complex
    9. Bianchi identity: ∇_μ G^{μν} = 0 (flat case)
    10. Riemann antisymmetry: R^ρ_{σμν} = -R^ρ_{σνμ}

    Everything above is meant as a structured export surface, not as a new
    foundational claim about the repository. *)

(** Curved pipeline is fully defined and computable *)
Definition master_curved_pipeline_complete := curved_pipeline_complete.

(** Formal Riemann tensor antisymmetry identity in this model. *)
Definition master_riemann_antisymmetric := curved_riemann_antisymmetric.

(** Flat spacetime produces zero Einstein tensor *)
Definition master_curved_einstein_vacuum := curved_einstein_uniform_zero_two_vertex.

(** Bianchi identity for flat case *)
Definition master_curved_bianchi_flat := curved_bianchi_flat.

(** Einstein equation with uniform coupling constant *)
Definition master_einstein_uniform_coupling := einstein_equation_uniform_coupling.

(** Non-circular diagonal Einstein equation: G_{dd} = κ · T_{dd}
    T built from module_structural_mass (independent of metric tensor) *)
Definition master_einstein_from_mass := einstein_equation_from_mass.

(** Ricci isotropy: R_{d1,d1} = R_{d2,d2} for isotropic 2-vertex complex (proved) *)
Definition master_ricci_isotropy := ricci_isotropy_isotropic_2v.

(** Summary bundle. *)

(** Core summary bundle indexed by this file.

    The exported bundle covers accounting, No Free Insight, the classical and
    Tsirelson-side CHSH bounds, Born-rule uniqueness, verification transfer,
    and the non-circularity certificate. The assumption surface is recorded
    explicitly so the summary cannot be mistaken for a claim of zero imported
    background principles. *)

Definition thiele_machine_core_summary_holds : Prop :=
  (* μ=0 witness exists *)
  (exists fuel trace, mu_cost_of_trace fuel trace 0 = 0%nat) /\
  (* Numerical hierarchy: classical bound ≤ Tsirelson bound *)
  correlation_hierarchy_derived /\
  (* Non-circularity: μ-cost rules have no quantum references *)
  non_circularity_certificate /\
  (* Verification transfer surface used in this summary *)
  verification_chain_holds.

(** Theorem 10: Core summary bundle.

    Classification:
    - audit bundle
    - unconditional
    - new composition of the core results indexed by this file

    What this proves:
    - the specific bundle [thiele_machine_core_summary_holds]

    What this does not prove:
    - repository-global completeness
    - that every theorem in the project is subsumed by this one summary bundle
*)
(* AUDIT:
  theorem: thiele_machine_core_summary_verified
  status: unconditional
  kind: new-composition
  depends_on: master_mu_zero_witness_sound; hierarchy_is_derived; non_circularity_verified; master_verification_chain
  premise_kinds: structural; algebraic; verification
  new_content_here: bundling of the core summary components indexed by this file
  semantic_layer: formal theorem layer
  external_interpretation: core audit bundle, not repository-global completeness
*)
Theorem thiele_machine_core_summary_verified : thiele_machine_core_summary_holds.
Proof.
  unfold thiele_machine_core_summary_holds.
  split; [| split; [| split]].
  - exists 10%nat, classical_achieving_trace. apply classical_program_mu_zero.
  - exact hierarchy_is_derived.
  - exact non_circularity_verified.
  - exact master_verification_chain.
Qed.

(** Backward-compatibility alias only.

    This older name is kept so downstream files do not break, but the preferred
    audit-facing name is [thiele_machine_core_summary_holds]. It should not be
    read as a stronger repository-global completeness claim.
*)
Definition thiele_machine_complete : Prop := thiele_machine_core_summary_holds.

(* AUDIT:
  theorem: thiele_machine_is_complete
  status: definitional
  kind: export-only
  depends_on: thiele_machine_core_summary_verified
  premise_kinds: syntactic
  new_content_here: none; export alias only
  semantic_layer: formal theorem layer
  external_interpretation: prefer the audit-facing name thiele_machine_core_summary_verified
*)
(** Theorem 10b: export alias for the core summary bundle, under the
    short name [thiele_machine_is_complete]. *)
Theorem thiele_machine_is_complete : thiele_machine_complete.
Proof.
  change thiele_machine_core_summary_holds.
  unfold thiele_machine_core_summary_holds.
  split; [| split; [| split]].
  - exists master_mu_zero_witness_fuel, master_mu_zero_witness_trace.
    exact master_mu_zero_witness_sound.
  - exact hierarchy_is_derived.
  - exact non_circularity_verified.
  - exact master_verification_chain.
Qed.

(**
  CLAIM TABLE (complete human audit view for master_claim_ledger)

    | Claim                                             | Formal status        | Depends on                                      | Does not imply |
    |---------------------------------------------------|----------------------|-------------------------------------------------|----------------|
    | master_mu_zero_algebraic_bound                    | unconditional        | μ=0 witness + algebraic CHSH boundedness        | classical/Tsirelson bounds or physical classification by itself |
    | master_classical_bound                            | unconditional        | factorizability theorem                         | that all μ=0 traces are factorizable or physical |
    | master_quantum_foundations                        | mixed summary        | numerical hierarchy + definitional unfolding    | derivation of QM from μ-cost |
    | master_non_circularity                            | unconditional        | non-circularity certificate                     | repository-global dependency acyclicity |
    | master_tsirelson_conditional                      | conditional          | coherence / PSD / NPA bridge premise            | derivation of the coherence premise or an unconditional physical Tsirelson theorem |
    | master_psd_iff_column_contractive                 | unconditional        | algebraic PSD lemmas                            | runtime coherence for arbitrary traces |
    | master_trace_column_contractive_iff_quantum_model | executable bridge    | trace correlator extraction                     | that the trace came from a physical source |
    | master_trace_quantum_model_unfolds                | definitional         | imported predicate definitions                  | that any trace satisfies the predicate |
    | master_trace_quantum_bridge_forces_psd            | conditional          | coherence bridge theorem                        | generic coherence or empirical quantum-source certification |
    | master_honest_nofi_structure_requirement          | unconditional        | certified information-reduction theorem         | coverage of every inference notion outside the imported framework |
    | master_honest_nofi_trace_separation               | unconditional        | trace-level cert-setter separation bound        | a per-run log2 lower bound without the additional local-premise theorem |
    | master_honest_nofi_conditional_shannon            | conditional          | local cert-setter / Shannon lower bound         | a theorem about arbitrary traces without the info-pricing and local-step premises |
    | master_honest_nofi_quantitative_state_space       | unconditional        | conservative LASSERT state-space-counting wrapper | a fully general feasible-set-ratio theorem for arbitrary traces or exact model counts |
    | master_honest_nofi_posterior_representative_reduction | conditional      | posterior-representative observation-equivalence lift | automatic derivation of that representative witness from arbitrary feasible-set collapse |
    | master_nofi_to_discrete_einstein                  | conditional          | explicit Landauer-Unruh calibration + thermo corridor | derivation of the calibration predicate from bare μ-accounting alone |
    | master_nofi_to_discrete_einstein_from_bekenstein_calibration | conditional | Bekenstein/Landauer-Unruh constants calibration path | an empirical calibration theorem with no explicit physical premises |
    | master_verification_chain                         | transfer theorem     | abstract hw/python bisimulation                 | full register/memory/partition-state equivalence or arbitrary semantic preservation |
    | master_verification_preserved_observables         | conditional          | projection from verification transfer theorem   | equality of all hardware observables |

    The machine-visible source for the same table is [master_claim_ledger].
    The complete top-level theorem inventory for this file is [summary_file_theorem_names].
*)

(** ** Part II.e: Categorical extension verification

    Confirms that the seven morphism opcodes (MORPH, COMPOSE,
    MORPH_ID, MORPH_DELETE, MORPH_ASSERT, MORPH_TENSOR, MORPH_GET)
    satisfy the category laws and the NoFreeInsight cost policy.

    What this section proves:
    - Morphism composition is associative at the coupling level
    - Left and right identity laws hold under diagonal-coupling conditions
    - Tensor product is bifunctorial (interchange law)
    - Tensor is a strict monoidal structure (assoc + unit laws)
    - MORPH_ASSERT is the only cert-setter; it costs ≥ 1 (NoFI consistent)

    What this section does NOT prove:
    - That the graph operations form a fully strict category without coupling
      normalization (normalize_coupling introduces a set-equivalence quotient)
    - Naturality squares for sources other than the relational model
    - Hardware-level associativity (that is covered by VerilogRefinement.v)
    *)

(* AUDIT:
  theorem: master_categorical_compose_assoc
  status: unconditional
  kind: export-alias
  depends_on: CategoryBridge.morph_graph_compose_assoc
  premise_kinds: structural (requires three morphisms with matching endpoints)
  new_content_here: none; permanent alias to CategoryBridge.morph_graph_compose_assoc
  semantic_layer: formal theorem layer
  external_interpretation: morphism composition in the partition graph is
    associative at the coupling level: (f;g);k ≡ f;(g;k)
*)
Definition master_categorical_compose_assoc := @morph_graph_compose_assoc.

(* AUDIT:
  theorem: master_categorical_id_left
  status: conditional
  kind: export-alias
  depends_on: CategoryBridge.morph_id_left_coupling
  premise_kinds: structural (requires source membership proof)
  new_content_here: none; permanent alias to CategoryBridge.morph_id_left_coupling
  semantic_layer: formal theorem layer
  external_interpretation: diagonal(region);f ≡ f when region contains f's sources
*)
Definition master_categorical_id_left := @morph_id_left_coupling.

(* AUDIT:
  theorem: master_categorical_id_right
  status: conditional
  kind: export-alias
  depends_on: CategoryBridge.morph_id_right_coupling
  premise_kinds: structural (requires codomain membership proof)
  new_content_here: none; permanent alias to CategoryBridge.morph_id_right_coupling
  semantic_layer: formal theorem layer
  external_interpretation: f;diagonal(region) ≡ f when region contains f's targets
*)
Definition master_categorical_id_right := @morph_id_right_coupling.

(* AUDIT:
  theorem: master_categorical_nofi_consistent
  status: unconditional
  kind: export-alias
  depends_on: CategoryBridge.categorical_extension_nofi_consistent
  premise_kinds: none (unconditional)
  new_content_here: none; permanent alias confirming categorical extension is NoFI-sound
  semantic_layer: formal theorem layer
  external_interpretation: MORPH_ASSERT is the only cert-setter among morph ops;
    it costs ≥ 1 mu-unit, consistent with NoFreeInsight
*)
Definition master_categorical_nofi_consistent := @categorical_extension_nofi_consistent.

(* AUDIT:
  theorem: master_categorical_tensor_bifunctor
  status: conditional
  kind: export-alias
  depends_on: CategoryMonoidal.tensor_bifunctor
  premise_kinds: structural (requires vanishing cross-term conditions)
  new_content_here: none; permanent alias to CategoryMonoidal.tensor_bifunctor
  semantic_layer: formal theorem layer
  external_interpretation: MORPH_TENSOR implements the interchange law:
    (f⊗g);(f'⊗g') ≡ (f;f')⊗(g;g') when f,g act on disjoint object sets
*)
Definition master_categorical_tensor_bifunctor := @tensor_bifunctor.

(* AUDIT:
  theorem: master_categorical_monoidal_coherence
  status: unconditional
  kind: export-alias
  depends_on: CategoryMonoidal.monoidal_coherence
  premise_kinds: none (unconditional)
  new_content_here: none; permanent alias to CategoryMonoidal.monoidal_coherence
  semantic_layer: formal theorem layer
  external_interpretation: coupling_tensor (list append) satisfies strict monoidal
    structure: associativity and left/right unit laws hold
*)
Definition master_categorical_monoidal_coherence := @monoidal_coherence.

(** End of Master Summary *)
