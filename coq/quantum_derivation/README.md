# Quantum Mechanics Derivation

**Mission:** Derive quantum mechanics as a representation theorem for the Partition Ledger Axioms (PLA).

## Axiom Kernel

See [AXIOM_KERNEL.md](AXIOM_KERNEL.md) for the formal specification of:
- **A1-A4**: Core Ledger Axioms (Variables, Cardinality, Refinement, μ-Monotonicity)
- **I1-I3**: Representation Invariants (Refinement Invariance, Continuity, Constant Discovery)

## Structure

### Phase 1: Resource Composition
- `CompositePartitions.v` - Disjoint partition composition, dim multiplicativity
- `TensorNecessity.v` - Direct sum fails; tensor forced

### Phase 2: State Manifold
- `TwoDimensionalNecessity.v` - 2D (S¹) required for continuous superposition
- `ComplexNecessity.v` - Complex amplitudes forced by partition constraints

### Phase 3: Valuation Invariance
- `BornRuleUnique.v` - P = |ψ|² is unique under refinement invariance

### Phase 4: Operational Irreversibility  
- `ObservationIrreversibility.v` - μ-monotonicity forces irreversible revelation
- `CollapseDetermination.v` - Unique post-measurement state
- `ProjectionFromPartitions.v` - Projection postulate as ledger update

### Phase 5: Discovery Dynamics
- `SchrodingerFromPartitions.v` - Constant discovery rate → unitary evolution

## Compilation

Each file compiles independently:
```bash
cd /workspaces/The-Thiele-Machine/coq
coqc -Q thielemachine/coqproofs ThieleMachine \
     -Q quantum_derivation QuantumDerivation \
     quantum_derivation/<file>.v
```

## Verification Status

| File | Admits | Axioms | Status |
|:---|:---:|:---:|:---:|
| `CompositePartitions.v` | 0 | A1, A2 | ✅ |
| `TensorNecessity.v` | 0 | A1, A2 | ✅ |
| `TwoDimensionalNecessity.v` | 0 | A3, I2 | ✅ |
| `BornRuleUnique.v` | 0 | I1, A3 | ✅ |
| `ObservationIrreversibility.v` | 0 | A4 | ✅ |
| `CollapseDetermination.v` | 0 | A4, A3 | ✅ |
| `ProjectionFromPartitions.v` | 0 | A4 | ✅ |
| `SchrodingerFromPartitions.v` | 0 | I3 | ✅ |
| `ComplexNecessity.v` | 0 | — | ✅ |

**Result:** All files COMPLETE with 0 admits. Invariants I1-I3 declared in [AXIOM_KERNEL.md](AXIOM_KERNEL.md).
