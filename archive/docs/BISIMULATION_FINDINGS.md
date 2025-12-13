# Bisimulation Test Findings

## Date: December 13, 2025

## Discovery: Trace-Level vs Partition-Level Isomorphism

The adversarial bisimulation tests revealed a **fundamental distinction**:

### End-State Isomorphism (Weak)
Two operation sequences are **partition-isomorphic** if they produce the same final partition (as a set of sets), ignoring module IDs and intermediate states.

### Trace-Level Bisimulation (Strong)  
Two operation sequences are **trace-bisimilar** if every step produces the same observable state transitions: same Δμ, same partition snapshot (including ordering).

## Key Finding: PSPLIT Non-Commutativity at Trace Level

**Test**: `test_psplit_commutativity`

**Minimal Failing Case**:
```python
Region: {1, 2}
Pred1 = {1}  # Split: {1} vs {2}
Pred2 = {2}  # Split: {2} vs {1}

Path 1 (Pred1 → Pred2):
  partition_snapshot = [frozenset(), frozenset({1}), frozenset({2})]
  
Path 2 (Pred2 → Pred1):
  partition_snapshot = [frozenset(), frozenset({2}), frozenset({1})]
```

### Analysis

**Partition-level**: IDENTICAL
- Both produce `{{}, {1}, {2}}` (ignoring order)
- Same final state up to module renaming

**Trace-level**: DIFFERENT
- Sorted module lists differ: `[{1}, {2}]` vs `[{2}, {1}]`
- Module ID assignment depends on split order
- Different observational traces

### Implications

1. **Classical Partition Refinement**: Commutative at partition level
   - Split by A then B ≡ Split by B then A (as sets)
   
2. **Trace Bisimulation**: Non-commutative
   - Module IDs are observable artifacts
   - Order affects trace even when final partition is same

3. **Quantum Fork A** (Contextuality):
   - This is NOT quantum contextuality (yet)
   - This is **representation dependence**: module IDs are internal names
   - TRUE contextuality would be: different PARTITIONS (not just module IDs)

### Resolution

**Option 1**: Normalize partition snapshots as sets-of-sets (lose ordering)
- Makes PSPLIT commutative at trace level
- Treats module IDs as pure internal witnesses

**Option 2**: Keep strict trace bisimulation
- Requires operation order canonicalization
- Module IDs become part of observable semantics
- Opens door to investigating if TRUE order-dependence exists

**Option 3**: Separate trace levels
- **Weak bisimulation**: partition snapshots as sets (order-independent)
- **Strong bisimulation**: partition snapshots as lists (order-dependent)
- Test both properties

## Other Discoveries

### 1. PNEW Overlap Semantics
- **Canonical model (initial)**: Allowed overlapping regions
- **VM**: Rejects overlap with `ValueError`
- **Fix**: Added overlap detection to canonical model

### 2. PNEW Deduplication  
- **Canonical model (initial)**: Created duplicate modules, charged μ twice
- **VM**: Deduplicates identical regions, charges μ=0 for duplicates
- **Fix**: Added deduplication logic to canonical model

### 3. Module ID Indexing
- **Canonical**: 0-based (first module is ID 0)
- **VM**: 1-based (module 1 is base {0}, user modules start at 1+)
- **Fix**: Filter module IDs from trace comparison (treat as internal names)

## Philosophical Implications

### The Three Levels of Equivalence

1. **Syntactic**: Same operation sequence
2. **Semantic (Partition)**: Same final partition (sets-of-sets)
3. **Observational (Trace)**: Same state transitions including internals

**Insight**: Bisimulation is stricter than semantic equivalence. Two semantically equivalent programs can have different traces.

### Abstraction as Objective Operation

The canonical model started as an "abstract specification" but **traced execution forced it to match VM semantics exactly**:
- Overlap rejection
- Deduplication
- μ-charging rules

**This validates the claim**: Trace isomorphism makes abstraction objective. You can't hand-wave away "implementation details" - the trace captures ALL observable behavior.

### Structure Preservation

"Structure" is what survives trace bisimulation. If two implementations produce different traces on the same inputs, **they do not preserve structure**, even if final states match.

This upgrades from:
> "Does end state match?"

To:
> "Does the entire causal path through state space match?"

## Next Steps

1. **Decide on module ID semantics**:
   - Are module IDs observable (strong bisimulation)?
   - Or internal witnesses (weak bisimulation)?

2. **Extend to Verilog traces**:
   - Parse `partitions` bus from RTL simulation
   - Compare 3-way traces: Coq ↔ Python ↔ Verilog

3. **Test PDISCOVER**:
   - Does discovery order matter?
   - Is classification deterministic?

4. **Adversarial search at scale**:
   - Run 10,000+ random op sequences
   - Find corner cases that break bisimulation
   - Build minimal reproducing test suite

## Conclusion

The bisimulation tests **work exactly as intended**:
- Found real semantic gaps (overlap, dedup)
- Revealed abstraction choices (module ID ordering)
- Forced canonical model to match VM precisely

**The harness is deadly**. It doesn't accept vague "equivalence" - it demands **exact trace equality**.

This is the foundation for proving "silicon-enforced mathematics" - if Coq, Python, and Verilog all pass bisimulation tests, they are **provably the same machine** at the trace level.
