# kernel/nfi

The No Free Insight chain. Every certification has a price; the price is
substrate-independent; the price grows with the ISA's strength of insight.

This is the load-bearing layer of the Receipt Theorem. The README's "Layer 1"
that absorbs the toy-counter rebuttal lives here.

## Files

### Substrate-independent foundation

| File | Purpose |
|---|---|
| `UniversalCertificationCost.v` | **`universal_nfi_any_substrate`** (claim 4), **`thiele_morphism_exists`** (claim 5), **`thiele_morphism_unique_on_traces`** |
| `HonestCostTracking.v` | **`honest_cost_tracking_strict_restriction`**, **`free_forgery_violates_A2`**, `dishonest_forge_system` |
| `VerificationCostSeparation.v` | **`thiele_honesty_O_1_witness`** vs **`verification_cost_gap_omega_T`** — Ω(T) free-world honesty verification |
| `AbstractNoFI.v` | **`certification_requires_positive_mu`** (claim 3), **`no_free_certification_certified`** |

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
| `HonestNoFI_TheoremsWithoutAssumptions.v` | **`structural_entitlement_representation`** — Δμ ≥ 1 forced by feasible-set narrowing |
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
| `NonAdaptiveLowerBound.v` | **`non_adaptive_factored_sat_4_k_lower_bound`** — 4ᵏ probes for non-adaptive blind solvers |
| `ThermodynamicStructuralAdvantage.v` | **`byte_inspector_must_read_every_byte`** — Ω(N) parsing-vs-CERTIFY gap |
| `PrimeAxiom.v` | Infrastructure for prime-related cost lemmas |

## Load-bearing exports cited from the README

`universal_nfi_any_substrate`, `thiele_morphism_exists`, `thiele_morphism_unique_on_traces`,
`certification_requires_positive_mu`, `no_free_certification_certified`,
`honest_cost_tracking_strict_restriction`, `free_forgery_violates_A2`,
`thiele_honesty_O_1_witness`, `verification_cost_gap_omega_T`,
`structural_entitlement_representation`, `non_adaptive_factored_sat_4_k_lower_bound`,
`byte_inspector_must_read_every_byte`.

## Imports

`foundation/`, `mu_calculus/`.
