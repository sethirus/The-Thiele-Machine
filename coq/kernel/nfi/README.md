# kernel/nfi

The No Free Insight chain. Every certification has a price; the price is
substrate-independent; the price grows with the ISA's strength of insight.

This is the load-bearing layer of the Receipt Theorem. The No Free Insight
rows of the top-level README's [Formal Spine](../../../README.md#formal-spine)
point into this directory.

## Files

### Substrate-independent foundation

| File | Purpose |
|---|---|
| `UniversalCertificationCost.v` | **`universal_nfi_any_substrate`**, **`thiele_morphism_exists`**, **`thiele_morphism_unique_on_traces`** |
| `HonestCostTracking.v` | **`honest_cost_tracking_strict_restriction`**, **`free_forgery_violates_A2`**, `dishonest_forge_system` |
| `VerificationCostSeparation.v` | **`thiele_honesty_O_1_witness`** vs **`verification_cost_gap_omega_T`**: a free-world verifier must inspect at least `n` positions, for verifiers that read only the positions they inspect |
| `AbstractNoFI.v` | **`certification_requires_positive_mu`**, **`no_free_certification_certified`** |

### Insight taxonomy and receipts

| File | Purpose |
|---|---|
| `InsightTaxonomy.v` | Structural creation (free) vs. certified insight (cost ≥ 1) |
| `RevelationRequirement.v` | Predicates: `reveals`, `cert_addr_setterb`, etc. |
| `InformationGainToStrengthening.v` | Bridge from probe-style information gain to predicate strengthening |
| `ReceiptCore.v`, `ReceiptIntegrity.v` | Receipt structure and integrity proofs |
| `Certification.v`, `CertCheck.v` | Certification predicates and check semantics |
| `NoFreeInsight.v` | General NFI theorem, parameterized form |
| `HonestNoFI.v` | Three-level NFI scope (structural / quantitative / Landauer) |
| `HonestNoFI_TheoremsWithoutAssumptions.v` | **`structural_entitlement_representation`**: for sound structural shortcuts, the cost is at least `log2_up(feasible_size Omega_prior) - log2_up(feasible_size Omega_posterior)` (a floor that can be 0), under the theorem's eight premises |
| `MuLedgerQuantumBridge.v` | Bridge between μ-ledger and quantum-tier accounting |
| `NecessityAbstract.v` | Abstract necessity of cost-bearing receipts |
| `LandauerDerivation.v` | μ-cost / Landauer bridge (conservative positive-cost indicator) |
| `PartitionRefinementNoFI.v` | Partition refinement is not free |

### Structural advantage chain

| File | Purpose |
|---|---|
| `StructuralAdvantage.v` | Two-program advantage on factored SAT |
| `StructuralAdvantageCertifiedShortcut.v` | MORPH_ASSERT bridge into structure-addition |
| `StructuralAdvantageObservedShortcut.v` | Concrete factorization witness |
| `StructuralAdvantageObservedShortcutResult.v` | Final specialization wrapper |
| `NonAdaptiveLowerBound.v` | **`non_adaptive_factored_sat_4_k_lower_bound`**: at least 4ᵏ probes for non-adaptive deciders correct on the factored family (`nad_correct (2 * k)`) |
| `ThermodynamicStructuralAdvantage.v` | **`byte_inspector_must_read_every_byte`**: log2_up|Ω| - log2_up(N) parsing-vs-CERTIFY gap, for inspectors that read only the bytes they inspect |
| `PrimeAxiom.v` | Infrastructure for prime-related cost lemmas |

### Permanent records and knowledge narrowing

| File | Purpose |
|---|---|
| `PermanentCertification.v` | On a finite machine, a certificate that no step revokes is switched on only by a step that merges states |
| `PermanentRecordPricing.v` | Price of a permanent certificate on a finite machine under the counting premise `compression_priced` |
| `PermanentCertificationEntropy.v` | The permanent-certificate bound stated in Shannon entropy |
| `FiniteCertMachine.v` | A finite, merge-priced eight-state machine that the VM runs |
| `KnowledgeNarrowing.v` | Which narrowing a merge-priced machine pays for: the machine's own spread of states versus an observer's candidate set |
| `KnowledgeNarrowingIncremental.v` | What an observer learns during a run, measured against knowledge after the empty trace |
| `KnowledgeNarrowingMinimal.v` | Free learning in a run and the smallest machine that does it (`free_incremental_narrowing_with_three`, `no_free_incremental_narrowing_below_three`) |
| `ShadowPricing.v` | The exact price of certification cannot be read off the shadow (the observation before and after a step) |
| `EventGenericAudit.v` | Event-generic theorems applied at non-certification events (`audit_` definitions); applications that still expose a pricing, distribution, physical, or injectivity premise are reported as partial |

### Commitment pricing and cost frameworks

| File | Purpose |
|---|---|
| `A2LoadBearing.v` | A separation theorem, statable without A2, whose proof invokes A2 (through `no_free_certification_certified_mu`) |
| `CommitmentPredicateAdequacy.v` | Substitution gate for A2: in trusted local-predicate pricing systems, a predicate yields a universal certification-cost floor iff it covers every uncertified-to-certified transition |
| `CommitmentCostDecomposition.v` | A2 as the exact incremental component inside a cost model `total_cost = background_cost + unit(local_charge)` |
| `CommitmentVsErasure.v` | Equal-trust separation between commitment cost and erasure cost: a trusted erasure law can certify at zero cost when no erasure occurs, a trusted A2 law cannot |
| `A2Payoff.v` | Equal-trust substitution-test payoff theorem: the trace floor `cost >= number of certification commitments` holds iff the priced predicate contains the cert-flip predicate |
| `CostSemanticsComparison.v` | Writer identities and a lower-bound potential argument, placing the certification law among existing cost frameworks |
| `CostFrameworks.v` | The certification law against four cost frameworks: graded monads, cost semantics, amortized resource analysis (`a2_and_aara_iff_exact`), linear resources (`flips_le_cost`) |
| `PricingPhysicsTarget.v` | Statement vocabulary for the pricing-and-physics results: no price beyond merges, logical payment, no intrinsic joule scale, Landauer calibration (definitions) |
| `PricingPhysicsAudit.v` | Proved outcomes for those statements (`no_forced_price_beyond_merges`, `permanent_write_has_logical_payment`, `mu_has_no_intrinsic_joule_value`, `calibrated_mu_landauer_energy`, `permanence_heat_floor_uses_landauer`) |

### Structural undecidability and orthogonality

| File | Purpose |
|---|---|
| `StructuralUndecidability.v` | Substrate-level limitative result: an A2-respecting substrate with a non-trivial structural-shortcut predicate has an undecidable membership problem; the VM-scoped corollary carries encoding and recursion-theorem premises |
| `VMSubstrateEncoded.v` | Discharges the Goedel-encoding premises of the VM-scoped theorem by storing the program's Goedel number in `vm_logic_acc`; the VM's internal recursion-theorem premise remains |
| `StructuralAxisOrthogonality.v` | The structural-shortcut predicate's detection channel is not a function of the Turing configuration `forget s` |
| `StructuralAxisRelativization.v` | The same holds relative to any classical oracle; the two axes are mutually independent (`axes_mutually_independent`), and structural membership is decidable from the full `VMState` |
| `UniversalShortcutLifting.v` | Any trace that fires the supra-cert channel from a clean initial state without latching `vm_err` yields a `SoundStructuralShortcut` |
| `SimpleMorphShortcut.v` | A minimal `SoundStructuralShortcut` inhabitant: the three-instruction trace PNEW, MORPH_ID, MORPH_ASSERT |

### Initiality and measurement

| File | Purpose |
|---|---|
| `ThieleInitiality.v` | Trace-fold initiality and conditional state-map uniqueness |
| `MuRunIncompleteness.v` | `mu` is not a complete invariant of a run: reachable one-instruction witnesses share the classical shadow and `mu` and differ in certification or in the graph |
| `HonestMeasurement.v` | `HonestMeasurementSystem`: `CertificationSystem` extended with a measurement function and the obligation A3 as a record field (not a global axiom) |
| `MeasurementExtraction.v` | The deterministic Bell theorem (`cr_no_signalling_implies_no_perfect_rac`) and the relational Bell/PR-box uniqueness theorem (`rac_no_signalling_relation_is_prbox`) |

## Load-bearing exports cited from the README

`universal_nfi_any_substrate`, `thiele_morphism_exists`, `thiele_morphism_unique_on_traces`,
`certification_requires_positive_mu`, `no_free_certification_certified`,
`honest_cost_tracking_strict_restriction`, `free_forgery_violates_A2`,
`thiele_honesty_O_1_witness`, `verification_cost_gap_omega_T`,
`structural_entitlement_representation`, `non_adaptive_factored_sat_4_k_lower_bound`,
`byte_inspector_must_read_every_byte`.

## Imports

`foundation/`, `mu_calculus/`.
