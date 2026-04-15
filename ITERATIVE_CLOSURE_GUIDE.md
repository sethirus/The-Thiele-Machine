# Iterative Closure Guide — All Remaining Open Items

Working document. Each item has a status, location, description, blocking
conditions, and concrete next steps. Update status fields as work proceeds.

**Last verified:** 2026-04-15 (round 2). Build clean, 931 tests pass,
Inquisitor OK, zero Admitted proofs, zero project-local Axioms,
zero stale comments.

**Status legend**
- `[ ]` Not started
- `[~]` In progress
- `[x]` Closed (proven / connected / classified-and-documented)
- `[—]` Will-not-close (genuine scope boundary, documented with falsification)

---

## Gate Commands

```bash
make -C coq -j4                                    # Coq build
python -m pytest tests/ -q                          # 931 tests
python scripts/inquisitor.py                        # Inquisitor
python scripts/generate_master_summary_artifacts.py # Artifact regen
grep -Prn '^\s*Admitted\s*\.' coq/                  # Must return empty
```

---

# TIER 1 — Closeable Proof Work

Items that can be proved in bare Coq without external libraries.

## T1-1. DiscreteTopology.v triangle edge count `[x]`

- **File:** `coq/kernel/DiscreteTopology.v`
- **Resolution:** Stale comment. `triangle_has_3_edges` (Qed) already
  proves this from `region_edges_internal_length_3`. Removed orphaned
  comment.

## T1-2. PhysicalConstants.v vacuous predicates `[x]`

- **File:** `coq/thiele_manifold/PhysicalConstants.v`
- **Resolution:** Replaced `True` placeholders with abstract Section
  Variables `decodes_to` and `produces_own_payload`. Predicates now carry
  meaningful structure while preserving the external-instantiation design.

## T1-3. PhysicsIsomorphism.v vacuous Prop fields `[x]`

- **File:** `coq/thiele_manifold/PhysicsIsomorphism.v`
- **Resolution:** All three model records now carry meaningful Props:
  - `phys_reversible`: involution/inverse proofs (lattice gas:
    `physics_step_involutive`, wave: `wave_step_inverse`, dissipative: `False`)
  - `phys_locality` / `phys_finiteness`: length-preservation proofs
    (`physics_step_length`, `dissipative_step_length`, `wave_step_length`)
  - Added `physics_step_length` to DiscreteModel.v and
    `dissipative_step_length` to DissipativeModel.v
  - Nine verification lemmas (lattice_gas_local, _finite, _reversible;
    dissipative_local, _finite; wave_local, _finite, _reversible) all Qed.

---

# TIER 2 — Connectable Bridges

Items where both sides exist but are not yet linked.

## T2-1. HardwareShadowBridge.v trace-level commutation `[x]`

- **File:** `coq/kami_hw/ShadowDeviceTrace.v`, `ShadowEmbedStep.v`
- **Resolution:** Already proved at two levels:
  - Shadow trace: `rtl_shadow_trace_compat_extended` covers 30/47 opcodes
    unconditionally. 4 more (CHSH_TRIAL, TENSOR_SET/GET, LJOIN) have
    conditional shadow lemmas. Total: 34/47 at shadow level.
  - Full-state trace: `driven_trace_commutes` covers 41/47 opcodes
    under `WFDrivenPrecondition` through `abs_full_snapshot`.
  - Remaining 6 opcodes (LASSERT, MORPH_ID, COMPOSE, MORPH_TENSOR,
    TENSOR_SET, TENSOR_GET) have irreducible architectural
    mismatches at full-state level (mu gap, coupling labels).
  - Updated HardwareShadowBridge.v header to reflect true coverage.

## T2-2. FullEmbedStep.v representation isomorphism `[x]`

- **File:** `coq/kami_hw/GraphReconstructionBridge.v`
- **Resolution:** Already proved for 4/7 MORPH opcodes via `driven_step_wf`
  (MORPH, MORPH_DELETE, MORPH_ASSERT, MORPH_GET — all Qed under WF
  preconditions). Remaining 3 (MORPH_ID, COMPOSE, MORPH_TENSOR) have
  field-by-field equality only due to coupling label representation choices.
  Updated FullEmbedStep.v Category C comment to reflect true state.

---

# TIER 3 — External Library Boundaries

Items that require libraries not currently in the Coq dependency set
(Coquelicot, MathComp, probability monads). Cannot be closed without
adding new dependencies.

## T3-1. CHSHStatisticalBridge.v Hoeffding concentration `[x]`

- **File:** `coq/kernel/CHSHStatisticalBridge.v`
- **Was:** Section Variable `hoeffding_chsh_concentration` concluding `True`.
- **Resolution:** DELETED. The variable was dead code — concluded `True`,
  was never applied in any theorem, and the W2 chain (Bell inequality,
  trial counting, violation detection) is complete without it.
  Also deleted the companion `hoeffding_n_min` variable and the
  entire `HoeffdingHypothesis` Section.  Updated header and summary
  comments.

## T3-2. MuShannonBridge.v expectation-level bound `[—]`

- **File:** `coq/kernel/MuShannonBridge.v:293-297`
- **What:** Policy-based Shannon bound is proven. Expectation-level
  (whole-decision-tree) semantics require branching/probabilistic
  formalization.
- **Blocking:** Requires probabilistic/branching semantics library.
- **Status:** Accurately documented as scope boundary. Single-trace claim is
  explicitly rejected as false in the file.
- **To close:** Formalize decision-tree branching semantics with probability
  weights, prove expected-value bound.
- **Severity:** Medium. Policy bound stands on its own.

## T3-3. LocalInfoLoss.v finite→infinite state bridge `[x]`

- **File:** `coq/kernel/LocalInfoLoss.v`
- **Was:** Comment said FiniteInformation instantiation "requires restricting
  to bounded subgraphs (a separate formalization)."
- **Resolution:** BYPASSED. `causality_implies_conservation` (Qed) proves
  cost-bounds-info-loss for VMState DIRECTLY using per-instruction
  module-count analysis, without going through `FiniteInformation`.
  The bridge to FiniteInformation is unnecessary.
  Updated the file comment to document this.

---

# TIER 4 — Physics Scope Boundaries

Genuine physics axioms / research problems. These are classified with
falsification conditions but are not provable from the existing mathematical
framework alone.

## T4-1. QuantitativeNoFI.v open witness functions `[—]`

- **File:** `coq/kernel/QuantitativeNoFI.v:441-443`
- **Items:**
  - W1 (cert string length) — connect cert cost to cert size
  - W4 (Shannon) — formal connection to information theory
  - W5 (Kolmogorov) — requires oracle axiom (fundamentally non-computable)
- **Status:** Framework proven; W2 (CHSH) instantiated. W1/W4/W5 are
  research-level instantiations.
- **To close W1:** Define `cert_length : cert -> nat`, prove cost ≥ f(length).
- **To close W4:** Depends on T3-2 (Shannon expectation bound).
- **To close W5:** Axiomatize Kolmogorov oracle, prove cost ≥ g(K(cert)).
- **Severity:** Low (framework works without them).

## T4-2. MetricFromMuCosts.v / RiemannTensor4D.v 4D formalization `[—]`

- **Files:** `coq/kernel/MetricFromMuCosts.v:303-327`,
  `coq/kernel/RiemannTensor4D.v:198-213`
- **What:** Full 4D tensor calculus (Christoffel symbols, Riemann tensor
  symmetries, Bianchi identities, metric inverse, Einstein field equations).
  2D discrete pipeline is complete.
- **Blocking:** Substantial mathematical infrastructure: tensor algebra,
  Levi-Civita connection, curvature decomposition.
- **Status:** Definitions exist in `RiemannTensor4D.v`. Key properties
  (antisymmetry, Bianchi, metric inverse) are stated as open.
- **To close:** Multi-week formalization project. Could use MathComp algebra.
- **Severity:** Medium (2D pipeline complete and self-contained).

## T4-3. Named physics hypotheses `[—]`

- **Files and hypotheses:**
  - `H_universal` (Bloch z encoding) — `BornRuleLinearity.v`
    - **Partial closure:** `bloch_z_encoded_minus_one` and
      `bloch_z_encoded_plus_one` construct concrete VMState witnesses for
      z ∈ {-1, 1}, proving the encoding is satisfiable at the two Bloch
      sphere poles. Full universality (∀ z ∈ [-1,1]) remains a physics axiom.
  - `H_grounded` (P(z) = outcome) — `BornRuleLinearity.v`
  - `H_clausius_mass` (heat → mass > 0) — `ThermoEinsteinBridge.v`
  - `H_convex` (Hardy Axiom 5) — `BornRuleLinearity.v`
  - `lorentzian_coupling_positive` (κ > 0) — `DiscreteRaychaudhuri.v`
    - **Discharged:** `lorentzian_coupling_positive_from_mass_gradient`
      in `LorentzianTensorPipeline.v` (Qed) under mass-gradient hypothesis.
- **Status:** All classified in `FULL_CLOSURE_PLAN.md` Phase C with
  falsification conditions. These are physical axioms, not proof gaps.
- **To close:** Would require formalizing Born-rule derivation from
  operational axioms (Hardy/Chiribella), thermodynamic mass-energy
  equivalence, and Lorentzian sign conventions from first principles.
- **Severity:** These ARE the physics. Discharging them = solving physics.

---

# TIER 5 — Stale Comments (Cosmetic)

## T5-1. MuCostDerivation.v "ADMITTED" label `[x]`

- **File:** `coq/kernel/MuCostDerivation.v:446`
- **Was:** Summary said `log2_subtraction_valid` is "ADMITTED (provable)"
- **Fix:** Updated to "ALL PROVEN (zero Admitted)" — the lemma has a
  complete proof (Qed) by `Nat.log2_le_mono` + case analysis.

## T5-2. Certification.v "deferred" proof claim `[x]`

- **File:** `coq/kernel/Certification.v:248-250`
- **Was:** Comment said "Full tactic proof deferred" for
  `chsh_trials_non_forgeable`, but the proof immediately follows and
  terminates with Qed.
- **Fix:** Updated to "Proven (Qed). Proof by induction on receipts..."

---

# Summary Matrix

| ID | Item | Tier | Status | Blocking |
|----|------|------|--------|----------|
| T1-1 | DiscreteTopology triangle edges | 1 | `[x]` | — |
| T1-2 | PhysicalConstants predicates | 1 | `[x]` | — |
| T1-3 | PhysicsIsomorphism Prop fields | 1 | `[x]` | — |
| T2-1 | HW trace-level commutation | 2 | `[x]` | — |
| T2-2 | MORPH representation iso | 2 | `[x]` | — |
| T3-1 | Hoeffding concentration | 3 | `[x]` | — (deleted dead code) |
| T3-2 | Shannon expectation bound | 3 | `[—]` | Branching semantics |
| T3-3 | Finite→infinite info bridge | 3 | `[x]` | — (bypassed) |
| T4-1 | W1/W4/W5 witnesses | 4 | `[—]` | Research / oracle axiom |
| T4-2 | 4D tensor calculus | 4 | `[—]` | Major formalization |
| T4-3 | Physics hypotheses (5) | 4 | `[—]` | Physical axioms (capstone proved) |
| T5-1 | MuCostDerivation stale label | 5 | `[x]` | — |
| T5-2 | Certification stale label | 5 | `[x]` | — |
