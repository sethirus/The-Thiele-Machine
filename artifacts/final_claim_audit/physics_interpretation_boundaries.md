# Physics Interpretation Boundaries

**Purpose**: Comprehensive audit of every physics-adjacent file in `coq/kernel/`.
For each file: what is *proven* (machine-checked Coq) vs. what is *interpretation* (physical meaning assigned to math).

The core gap that cannot be closed: Coq checks that a mathematical proof is valid. It cannot check that a definition correctly models physical reality. Every physics claim has this structure:

> **PROVEN**: [math theorem about VMState/VMStep/PartitionGraph]
> **ASSERTED** (by interpretation): [this corresponds to physical phenomenon X]

The interpretation step is always a human judgment, not a machine-checked fact.

---

## Classification Legend

- **PURE MATH** — theorem is entirely about VM objects; physical language is in comments only
- **NAMED HYPOTHESIS** — physical interpretation is stated as an explicit named predicate or variable; can be replaced or discharged independently
- **ANALOGY** — the file explicitly says the result has the *structure* of a physical law, not that it *is* that law
- **NEGATIVE RESULT** — the file proves what is *not* derivable (honest limitation)

---

## File-by-File Audit

### 1. `KernelPhysics.v`
**Status**: PURE MATH
**What is proven**: Observational equivalence (`obs_equiv`) is an equivalence relation; μ is conserved (`mu_conservation_kernel`); observational no-signaling (`observational_no_signaling`) — operations on module A don't change observations on module B.
**Physical interpretation**: These theorems are *labeled* as "gauge symmetry", "conservation law", "locality" — but the mathematical content is statements about `vm_step` and `VMState` fields. The physical label is interpretive.
**Interpretation gap**: Whether `obs_equiv` corresponds to physical measurement equivalence requires identifying the VM model with a physical system.

---

### 2. `PhysicsClosure.v`
**Status**: PURE MATH (combines KernelPhysics + SpacetimeEmergence)
**What is proven**: Conjunction of `observational_no_signaling` + `mu_conservation_kernel` + `exec_trace_no_signaling_outside_cone`.
**Physical interpretation**: Labeled as "three pillars of relativistic physics (locality, conservation, causality)."
**Interpretation gap**: Same as KernelPhysics.v. The math is about VM state; the physics label is interpretive.

---

### 3. `SpacetimeEmergence.v`
**Status**: PURE MATH
**What is proven**: `reaches` (reachability on VM states) is transitive; `exec_trace_no_signaling_outside_cone` — information cannot propagate outside the causal cone of an instruction trace; `vm_step_preserves_wf`; `vm_step_next_id_monotone`.
**Physical interpretation**: `reaches` is described as "the discrete analogue of the causal order in general relativity." No-signaling = relativistic locality.
**Interpretation gap**: Causal cones here are defined by instruction dependency (syntax), not spacetime geometry. The analogy is structural, not a derivation.

---

### 4. `LorentzNotForced.v`
**Status**: NEGATIVE RESULT — honest limitation statement
**What is proven**: There exist cone-preserving maps (identity, stutter) that are NOT Lorentz boosts. Lorentz invariance is NOT derivable from kernel primitives alone.
**Physical interpretation**: "Lorentz invariance is an EMERGENT property of spacetime, not a fundamental computational constraint." The file explicitly disclaims the Lorentz derivation.
**Interpretation gap**: None added — this file *reduces* overclaiming. The theorem proves the kernel does *not* force Lorentz.

---

### 5. `EinsteinEmergence.v`
**Status**: ANALOGY — explicitly stated
**What is proven**: Gauss-Bonnet identity `ΔK(m) = 5π × Δχ` for VM graph topology changes induced by PNEW.
**Physical interpretation**: "This has the same STRUCTURE as Einstein's equation (G_μν ∝ T_μν): curvature change is proportional to a source term. However, this is a 2D topological identity (Gauss-Bonnet), not the 4D Einstein field equation. The coupling constant is 5π (from triangulation geometry), not 8πG/c⁴. The connection to physical gravity is an analogy."
**Interpretation gap**: The file itself explicitly names this as an analogy. The coupling constant 5π is geometric; Newton's G is not derivable here.

---

### 6. `EinsteinEquations4D.v`
**Status**: ANALOGY
**What is proven**: Formal statements connecting discrete curvature (Euler characteristic changes) to a "stress-energy" source term defined in terms of VM state.
**Physical interpretation**: Labeled as "4D Einstein equations" but operating on discrete simplicial complexes derived from `vm_graph`, not a Riemannian manifold.
**Interpretation gap**: The "stress-energy tensor" is defined as a function of VM state fields — this is a named mapping, not a physical identification. The 4D label is aspirational; the proof is in terms of discrete graphs.

---

### 7. `ThermoEinsteinBridge.v`
**Status**: NAMED HYPOTHESIS
**What is proven**: Given `entropy_area_control` (from EntanglementEntropy.v) and `clausius_entropy_from_area` (from ClausiusFromEntropyArea.v), a Jacobson-style bridge hypothesis maps entropy-area control to discrete Einstein dynamics.
**Physical interpretation**: The Jacobson derivation (gravity from thermodynamics) is a named hypothesis in this file — not derived from first principles.
**Interpretation gap**: The file is explicit: "This file stays honest: it composes proven entropy locality with an explicit thermodynamic-to-gravity hypothesis, rather than claiming that Jacobson is already fully derived."  The hypothesis is named; the gap is acknowledged.

---

### 8. `RaychaudhuriFluxBridge.v`
**Status**: NAMED HYPOTHESIS
**What is proven**: Defines `NullCongruence` (expansion + shear scalars), `raychaudhuri_focusing`, `null_energy_flux` as functions of VMState and `SplitMorphism`. Proves algebraic relations between these objects.
**Physical interpretation**: These definitions *model* Raychaudhuri focusing on null congruences. The identification of `null_energy_flux` with physical null energy flux requires calibrating the VM cost unit to physical energy (Landauer energy).
**Interpretation gap**: The `null_energy_flux` function takes VM state + a morphism as input. Whether this function equals the physical null energy flux at a horizon requires `mu_energy_unit_is_landauer` (see BekensteinCalibration.v).

---

### 9. `BekensteinCalibration.v`
**Status**: NAMED HYPOTHESIS
**What is proven**: Pure algebra: Bekenstein bound saturation + Landauer entropy → energy per bit = T_Unruh × k_B × ln 2. This derivation is fully mechanical.
**Physical interpretation**: The connection from algebraic derivation to VM μ-cost requires `mu_energy_unit_is_landauer` — an *explicit named hypothesis* that vm_mu increments equal physical Landauer energy at the operating temperature.
**Interpretation gap**: `mu_energy_unit_is_landauer` is stated in the file as a named, falsifiable hypothesis: "Run hardware traces, measure energy per vm_mu increment, compare against k_B × T_hardware × ln 2." The gap is explicit and calibration-verifiable.

---

### 10. `DiscreteRaychaudhuri.v`
**Status**: PURE MATH
**What is proven**: Discrete version of the Raychaudhuri equation for the VM's simplicial complex graph — expansion scalar decreases when shear exceeds expansion (focusing theorem in discrete setting).
**Physical interpretation**: Labeled as "Raychaudhuri equation" — the math is about curvature functions on `vm_graph` simplicial complexes, not null geodesic congruences in a Lorentzian manifold.
**Interpretation gap**: The discrete Raychaudhuri result is structurally analogous to the continuous one but operates on a fundamentally different domain.

---

### 11. `MuGravity.v`
**Status**: ANALOGY / NAMED HYPOTHESIS
**What is proven**: μ-cost induces a curvature functional on the partition graph; locality constraint (PSPLIT nearest-neighbor) implies curvature is bounded by μ-cost.
**Physical interpretation**: "μ-gravity" — the analogy that μ-cost plays the role of gravitational action.
**Interpretation gap**: The "gravitational" interpretation requires identifying μ-cost with physical action, which is not formally derivable from VM semantics alone.

---

### 12. `LorentzianTensorPipeline.v`
**Status**: ANALOGY
**What is proven**: Lorentzian metric tensor operations (signature (+,-,-,-)) defined over 4D simplicial complexes derived from VM graph with time direction from DerivedTime.v.
**Physical interpretation**: Formally constructing a Lorentzian metric from VM graph structure. Whether this metric has physical meaning requires establishing that the VM graph discretizes a physical spacetime.
**Interpretation gap**: The time direction is derived from μ-ordering (DerivedTime.v), which is a mathematical choice, not a physical identification.

---

### 13. `NoFIToEinstein.v`
**Status**: CHAIN WITH NAMED HYPOTHESIS
**What is proven**: The chain: No Free Insight → locality → entanglement entropy ≤ area → Clausius → Raychaudhuri flux → discrete Einstein equation. Zero Admitted. Each step has a Coq proof.
**Physical interpretation**: This is the strongest physics claim in the repository. The chain has ONE named hypothesis that is NOT proven: `mu_landauer_unruh_calibrated` — that μ-cost increment × horizon area = Clausius heat dQ = T·dS.
**Interpretation gap**: `mu_landauer_unruh_calibrated` is explicitly stated as a hypothesis with experimental basis (Landauer 1961, Bérut et al. 2012). The rest of the chain follows mathematically. The file is honest about this one named join.

---

## Summary Table

| File | Status | Named hypothesis/gap |
|------|--------|----------------------|
| KernelPhysics.v | PURE MATH | physical labels interpretive |
| PhysicsClosure.v | PURE MATH | combines KernelPhysics + SpacetimeEmergence |
| SpacetimeEmergence.v | PURE MATH | causal cone = syntax, not geometry |
| LorentzNotForced.v | NEGATIVE RESULT | explicitly disclaims Lorentz |
| EinsteinEmergence.v | ANALOGY | explicitly says "analogy, not 4D Einstein" |
| EinsteinEquations4D.v | ANALOGY | discrete graphs ≠ Riemannian manifold |
| ThermoEinsteinBridge.v | NAMED HYPOTHESIS | Jacobson bridge is named hypothesis |
| RaychaudhuriFluxBridge.v | NAMED HYPOTHESIS | requires mu_energy_unit_is_landauer |
| BekensteinCalibration.v | NAMED HYPOTHESIS | `mu_energy_unit_is_landauer` named, falsifiable |
| DiscreteRaychaudhuri.v | PURE MATH | discrete domain ≠ null geodesics |
| MuGravity.v | ANALOGY | μ-gravity is structural analogy |
| LorentzianTensorPipeline.v | ANALOGY | metric construction, not physical identification |
| NoFIToEinstein.v | CHAIN + NAMED HYP | one named join: `mu_landauer_unruh_calibrated` |

---

## What This Means

**The math is proven.** Every Coq file listed here compiles with zero Admitted, zero global Axioms.

**The physics requires interpretation.** Each file assigns physical meaning to mathematical objects (VMState, vm_graph, vm_mu). This assignment is a human judgment.

**The gaps are named.** The key interpretation steps (`mu_energy_unit_is_landauer`, Jacobson bridge hypothesis, BSC compilation trust) are explicit named objects in the Coq source, not silent assumptions. They appear in the assumption list of any theorem that uses them.

**The falsifiable content.** BekensteinCalibration.v identifies the one empirically testable claim: measure energy per vm_mu increment on hardware and compare to k_B × T_hardware × ln 2. If it fails, `mu_energy_unit_is_landauer` is falsified and the chain to Einstein equations breaks.

---

*Generated 2026-03-27. Authoritative source: `coq/kernel/` compilation + inline file documentation.*
