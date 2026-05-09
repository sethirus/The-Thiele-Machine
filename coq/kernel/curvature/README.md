# kernel/curvature

Discrete curvature, Einstein equations on simplicial complexes, the μ-gravity
mapping, and the Lorentzian/Euclidean signature bookkeeping. The largest
subdirectory (30 files).

**Scope honesty:** these files prove discrete identities about the partition
graph and a metric reading derived from μ-tensor data. They do not derive
physical general relativity. The named bridge premise
`mu_landauer_unruh_calibrated` (in [`PhysicalSubstrate.v`](PhysicalSubstrate.v))
is what hooks numerical units to a physical reading; see README §"What is and
isn't forced".

## Files

### Foundational simplicial / matrix infrastructure

| File | Purpose |
|---|---|
| `MatrixAlgebra4.v` | 4×4 matrix algebra primitives |
| `FourDSimplicialComplex.v` | 4-simplex / clique-style cell bookkeeping |
| `DiscreteSimplicialGeometry.v` | `combinatorially_orthogonal` predicate; closes off-diagonal Ricci section variable |
| `DiscreteTopology.v` | F = 2I + B, B = 3χ identities; well-formed-triangulated invariants |
| `PhysicalSubstrate.v` | Typeclass for (k_B, ℏ, c) with `mu_landauer_unruh_calibrated` bridge premise |
| `KernelPhysics.v` | Causal-cone semantics; structural physics primitives |

### Metric / connection

| File | Purpose |
|---|---|
| `MetricFromMuCosts.v` | μ-tensor as discrete metric |
| `MetricForcing.v` | In isotropic two-vertex setup, Levi-Civita-style structure is forced |
| `RiemannTensor4D.v` | Riemann tensor on 4D simplicial complex |
| `SymmetricDerivative4D.v` | Affine metric-scaled symmetric derivative (1844 lines) |
| `LocalMorphismSemantics.v` | Split-morphism support semantics; nearest-neighbor boundary locality |

### Einstein equations

| File | Purpose |
|---|---|
| `EinsteinEquations4D.v` | Local-curvature / Bianchi identities in the simplicial setting (159 nodes) |
| `EinsteinEquationsFull.v` | Full-tensor EFE = diagonal EFE + off-diagonal Ricci = 0 |
| `AffineEFEClosure.v` | Closes off-diagonal Ricci gap via affine metric-scaled symmetric operator |
| `CurvedTensorPipeline.v` | Curved (non-vacuum) diagonal EFE pipeline |
| `EinsteinEmergence.v` | **`einstein_emerges`** — discrete Gauss-Bonnet identity ΔK = 5π·Δχ |
| `NoFIToEinstein.v` | NFI → EFE bridge under Bekenstein calibration |

### Lorentzian signature

| File | Purpose |
|---|---|
| `LorentzNotForced.v` | Negative result: kernel does NOT derive Lorentz invariance |
| `LorentzianTensorPipeline.v` | Discharges `lorentzian_coupling_positive` from mass-gradient sign |
| `DiscreteRaychaudhuri.v` | Discrete Raychaudhuri equation; `lorentzian_coupling_positive` premise |
| `RaychaudhuriFluxBridge.v` | Flux-side bridge for Raychaudhuri argument |

### μ-gravity mapping

| File | Purpose |
|---|---|
| `MuGravity.v` | μ-cost density → discrete curvature mapping (173 nodes) |
| `StressEnergyDynamics.v` | High stress-energy → high PNEW frequency |
| `PNEWTopologyChange.v` | PNEW + topological change bookkeeping |
| `TopologyCurvatureBridge.v` | Bridge between Euler-characteristic change and curvature |
| `SpacetimeEmergence.v` | Causal cone, locality, μ-conservation as emergent kernel facts |
| `JacobsonBridgeComponents.v` | Named bridge premises for the Jacobson construction |
| `DiscreteGaussBonnet.v` | Discrete Gauss-Bonnet identity ΔK = 5π·Δχ |
| `KernelNoether.v` | Z-indexed shifts of the μ-ledger (analogy file; **flagged for removal**) |
| `PhysicsClosure.v` | **`Physics_Closure`** — locality + μ-conservation + causality from `vm_step` alone |

## Load-bearing exports cited from the README

- `Physics_Closure`
- `einstein_emerges` — discrete Gauss-Bonnet identity
- `mu_landauer_unruh_calibrated` — the named bridge premise (axiom-not-axiom: explicit hypothesis)
- `nfi_to_discrete_einstein_from_pnew_bekenstein_calibration`,
  `nfi_to_discrete_einstein_from_psplit_bekenstein_calibration`

## Imports

`foundation/`, `mu_calculus/`, `nfi/`, `thermodynamic/`.

## Removal candidate

[`KernelNoether.v`](KernelNoether.v) is in the COQ_NECESSITY_AUDIT removal
list (analogy file, no consumers). Decision pending.
