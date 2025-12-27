# Roadmap: Deriving Tsirelson from μ-Accounting

**Current Status**: We have consistent formalization, NOT derivation  
**Goal**: Prove 2√2 emerges from μ-accounting without asserting it

## What We Have Now (Post-Hoc Formalization)

```coq
(* ASSERTED, not derived *)
Definition tsirelson_bound_int : nat := 2828427.

(* DEFINED using the assertion *)
Definition certifiable_with_mu_zero (ac : AbstractCorrelation) : Prop :=
  ac.(chsh_value_bound) <= tsirelson_bound_int.
```

**Problem**: 2√2 appears as input, not output. We defined the boundary, then proved consistency.

## What's Needed for True Derivation

### Step 1: VM Trace → CHSH Calculator

Define CHSH value mechanically from VM execution:

```coq
(* Extract Alice/Bob outputs from VM trace *)
Fixpoint extract_chsh_trials (trace : Trace) (s : VMState) : list Trial := ...

(* Compute CHSH from trials *)
Definition chsh_from_vm_trace (trace : Trace) (s : VMState) : Q :=
  chsh_classical (extract_chsh_trials trace s).
```

**Key**: NO reference to 2828427 or "Tsirelson" anywhere in these definitions.

### Step 2: μ-Cost Without Physics Input

Define what μ=0 programs can do WITHOUT asserting a CHSH bound:

```coq
(* A program is μ-preserving if final μ equals initial μ *)
Definition mu_preserving (trace : Trace) (s_init s_final : VMState) : Prop :=
  s_final.(vm_mu) = s_init.(vm_mu).

(* μ=0 certifiable means: achievable by a μ-preserving trace *)
Definition mu_zero_achievable (chsh_val : Q) : Prop :=
  exists (trace : Trace) (s_init s_final : VMState),
    s_init.(vm_mu) = 0 /\
    mu_preserving trace s_init s_final /\
    chsh_from_vm_trace trace s_final = chsh_val.
```

**Key**: This defines μ=0 operationally, without reference to quantum mechanics.

### Step 3: The Supremum Theorem (THE CORE)

Prove that 2√2 is the supremum:

```coq
Theorem tsirelson_is_mu_zero_supremum :
  (* Any μ=0-achievable CHSH is bounded by 2√2 *)
  (forall chsh_val, mu_zero_achievable chsh_val -> chsh_val <= (5657 # 2000)) /\
  (* 2√2 is attainable (tight bound) *)
  mu_zero_achievable (5657 # 2000).
```

**Proof Strategy**:
- Lower bound: Construct explicit μ=0 program achieving 2√2 (partition entanglement)
- Upper bound: Prove any μ=0 program cannot exceed 2√2 (requires partition constraint analysis)

### Step 4: Connect to RevelationRequirement

Strengthen the revelation theorem:

```coq
Theorem chsh_above_tsirelson_requires_mu :
  forall (trace : Trace) (s_init s_final : VMState),
    s_init.(vm_mu) = 0 ->
    chsh_from_vm_trace trace s_final > (5657 # 2000) ->
    s_final.(vm_mu) > 0.
```

**This would close the loop**: CHSH > 2√2 → μ increase (not just "uses revelation").

## Technical Challenges

### Challenge 1: CHSH Extraction from VM State

**Issue**: VM state is `(graph, registers, memory)`. CHSH is a correlation function.

**Need**: 
- Define "CHSH experiment protocol" as a specific trace structure
- Extract Alice/Bob outputs from memory/registers after trace execution
- Handle measurement basis encoding

**Approach**: Use `instr_chsh_trial` opcode as the measurement event, extract results from CSRs.

### Challenge 2: Partition Constraints → CHSH Upper Bound

**Issue**: Why does μ=0 (no partition manipulation) limit CHSH to 2√2?

**Physics intuition**: 
- μ=0 means only local operations + classical communication (LOCC)
- LOCC is contained in quantum polytope
- Quantum polytope max CHSH = 2√2 (Tsirelson's theorem)

**Formalization needed**:
```coq
Lemma mu_zero_implies_locc_structure :
  forall trace s_init s_final,
    s_init.(vm_mu) = 0 ->
    mu_preserving trace s_init s_final ->
    (* partition graph unchanged OR only combined/split without new correlations *)
    graph_structure_locc s_init.(vm_graph) s_final.(vm_graph).

Theorem locc_structure_bounds_chsh :
  forall g chsh_val,
    graph_structure_locc empty_graph g ->
    chsh_from_graph g <= (5657 # 2000).
```

This is the **hard part**: connecting partition topology to correlation bounds.

### Challenge 3: Attainability Construction

Need explicit witness program:

```coq
Definition tsirelson_achieving_program : Trace := [
  (* 1. Create entangled partition *)
  instr_pnew 0 0;  
  instr_psplit 0 0 1 1;
  instr_emit 0 [partition for Alice] 0;
  instr_emit 1 [partition for Bob] 0;
  
  (* 2. Run CHSH measurements *)
  instr_chsh_trial 0 1 0 0;  (* x=0, y=0 *)
  instr_chsh_trial 0 1 0 1;  (* x=0, y=1 *)
  instr_chsh_trial 0 1 1 0;  (* x=1, y=0 *)
  instr_chsh_trial 0 1 1 1   (* x=1, y=1 *)
].

Theorem tsirelson_program_achieves_bound :
  exists s_final,
    mu_preserving tsirelson_achieving_program init_state s_final /\
    chsh_from_vm_trace tsirelson_achieving_program s_final = (5657 # 2000).
```

**Requires**: Concrete partition entanglement model in `vm_graph`.

## Current Blockers

1. **No CHSH calculator from VM traces**: `chsh_from_vm_trace` doesn't exist
2. **No partition → correlation model**: `vm_graph` doesn't encode which partitions are entangled
3. **No μ-cost tracking for partition ops**: `vm_mu` increments not tied to partition structure changes
4. **RevelationRequirement is too weak**: Only proves "uses some structural op", not "increases μ"

## Honest Assessment

**To make the "derived from accounting" claim defensible:**

We would need ~6-12 months of additional work:
- Extend `VMState.PartitionGraph` with entanglement/correlation structure
- Define `vm_mu` increments explicitly for each partition operation
- Prove `vm_mu` conservation for LOCC operations
- Build CHSH calculator from VM state
- Construct explicit 2√2-achieving program
- Prove upper bound via partition constraint analysis

**Current state**: We have clean **syntax** (VM opcodes, μ-ledger) but not the **semantic bridge** connecting partition operations to correlation bounds.

## Recommended Path Forward

**Option A: Full Derivation** (ambitious, 6-12 months)
- Implement all steps above
- Build from first principles
- Strong scientific claim

**Option B: Honest Formalization** (current state + documentation)
- Document clearly: "consistent boundary theory, not derivation"
- Focus on what's proven: internal consistency, completeness
- Weaker but defensible claim

**Option C: Hybrid** (3-6 months)
- Keep current proofs as "boundary theory"
- Add separate module: `TsirelsonConstruction.v`
- Show explicit 2√2-achieving program (attainability)
- Document upper bound as "consistent with known physics result"

## Current Recommendation

**Option B with C's attainability proof** (~1 month):
- Accept that upper bound derivation is hard
- Prove attainability with explicit construction
- Document honestly what's proven vs. assumed

This would support the claim: "We CAN achieve 2√2 with μ=0, and we've proven this is consistent with a boundary there, but we haven't proven no μ=0 program exceeds it."

More honest, still valuable, scientifically defensible.
