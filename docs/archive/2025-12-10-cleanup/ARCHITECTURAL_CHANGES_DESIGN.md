# Architectural Changes Design Document

**Date:** 2025-12-08
**Purpose:** Complete the remaining 3 admits in ThieleSpaceland.v (achieving 100% proof completion)
**Status:** Design Phase

## Executive Summary

This document specifies the architectural changes required to complete the final 3 admits in ThieleSpaceland.v:

1. **Add `program` field to CoreSemantics.State** → Enables `step_deterministic` proof
2. **Add `add_module_preserves` lemma** → Enables `module_independence` proof
3. **Enrich Receipt structure** → Enables `receipt_sound` proof

These changes are **design-level decisions** that require careful coordination across all three layers (Coq, Python, Verilog).

## Current Status

### Proof Completion
- **Completed:** 8/11 proofs (67%)
- **Remaining:** 3 admits (all architectural blockers)
- **Files affected:** CoreSemantics.v, ThieleSpaceland.v, and downstream consumers

### The 3 Remaining Admits

#### 1. step_deterministic (ThieleSpaceland.v:140)
**Problem:** Cannot prove determinism because State doesn't contain the program
**Current state structure:**
```coq
Record State := {
  partition : Partition;
  mu_ledger : MuLedger;
  pc : nat;
  halted : bool;
  result : option nat;
}.
```

**Issue:** The `step` function takes program as parameter: `step (s : State) (prog : Program)`
This means two states with same partition/pc/etc could execute different instructions.

#### 2. module_independence (ThieleSpaceland.v:190)
**Problem:** Missing lemma that PNEW preserves existing modules
**Current code:**
```coq
- (* PNEW: Creates new module, but preserves existing modules *)
  (* This requires understanding how add_module works *)
  (* For now, admit - requires proof about add_module *)
  admit.
```

**Need:** `add_module_preserves` lemma proving that adding a new module doesn't affect existing modules.

#### 3. receipt_sound (ThieleSpaceland.v:506)
**Problem:** Receipt structure too simple to be fully surjective
**Current Receipt:**
```coq
Record Receipt : Type := {
  initial_partition : Partition;
  label_sequence : list Label;
  final_partition : Partition;
  total_mu : Z;
}.
```

**Issue:** Cannot reconstruct full execution trace from this receipt.

---

## Change 1: Add Program to State

### Design Decision

**Add `program : Program` field to State record.**

This makes the State truly self-contained and enables deterministic execution proofs.

### Implementation

#### CoreSemantics.v Changes

**BEFORE (lines 98-104):**
```coq
Record State := {
  partition : Partition;
  mu_ledger : MuLedger;
  pc : nat;
  halted : bool;
  result : option nat;
}.
```

**AFTER:**
```coq
Record State := {
  partition : Partition;
  mu_ledger : MuLedger;
  pc : nat;
  halted : bool;
  result : option nat;
  program : Program;  (* NEW: Program stored in state *)
}.
```

#### Step Function Changes

**BEFORE (line 191):**
```coq
Definition step (s : State) (prog : Program) : option State :=
```

**AFTER:**
```coq
Definition step (s : State) : option State :=
  let prog := s.(program) in
  (* rest of function unchanged *)
```

**Key change:** Remove `prog` parameter, use `s.(program)` instead.

#### Initial State Changes

**BEFORE (lines 107-112):**
```coq
Definition initial_state (vars : Region) : State :=
  {| partition := trivial_partition vars;
     mu_ledger := zero_mu;
     pc := 0;
     halted := false;
     result := None |}.
```

**AFTER:**
```coq
Definition initial_state (vars : Region) (prog : Program) : State :=
  {| partition := trivial_partition vars;
     mu_ledger := zero_mu;
     pc := 0;
     halted := false;
     result := None;
     program := prog |}.
```

### Impact Analysis

#### Files That Will Break

All files that construct State records or call `step` will need updates:

1. **CoreSemantics.v itself**
   - All State constructors in step function (lines 195-280)
   - Must add `program := s.(program)` to each record construction

2. **ThieleSpaceland.v**
   - Line 53: `step` definition signature changes
   - All proofs using `step` must be updated

3. **Simulation.v** (29,668 lines)
   - Extensive use of State and step
   - High risk of breakage

4. **BridgeDefinitions.v** (40,113 lines)
   - Bridges Coq to CPU state
   - May need CPU state changes too

5. **All proof files**
   - Any file importing CoreSemantics
   - Need to check compilation

### Migration Strategy

**Phase 1: CoreSemantics.v**
1. Update State record definition
2. Update step function signature and body
3. Update initial_state signature
4. Add `program := s.(program)` to all State constructions
5. Compile and fix errors

**Phase 2: ThieleSpaceland.v**
1. Update `step` wrapper definition
2. Update all proof scripts using `step`
3. Complete `step_deterministic` proof
4. Compile and verify

**Phase 3: Downstream Files**
1. Update Simulation.v
2. Update BridgeDefinitions.v
3. Update all other dependent files
4. Full compilation test

### Proof Completion: step_deterministic

Once program is in State, the proof becomes straightforward:

```coq
Lemma step_deterministic : forall s l1 s1' l2 s2',
  step s l1 s1' -> step s l2 s2' -> l1 = l2 /\ s1' = s2'.
Proof.
  intros s l1 s1' l2 s2' Hstep1 Hstep2.
  unfold step in *.
  destruct Hstep1 as [i1 [Hnth1 [Hlbl1 Hstep1]]].
  destruct Hstep2 as [i2 [Hnth2 [Hlbl2 Hstep2]]].
  (* Both steps use s.(program), so same program *)
  (* pc is the same, so nth_error returns same instruction *)
  rewrite Hnth2 in Hnth1.
  injection Hnth1 as Heq. subst i2.
  (* Same instruction → same label and same result *)
  split.
  - (* l1 = l2 *) congruence.
  - (* s1' = s2' *) congruence.
Qed.
```

---

## Change 2: Add module_preserves Lemma

### Design Decision

**Prove that `add_module` preserves existing modules.**

This is a structural lemma about list append operations.

### Implementation

Add to CoreSemantics.v (after line 167):

```coq
(** Helper: Add a module to partition *)
Definition add_module (p : Partition) (r : Region) : Partition :=
  {| modules := p.(modules) ++ [(p.(next_module_id), r)];
     next_module_id := S p.(next_module_id) |}.

(** Lemma: add_module preserves existing modules *)
Lemma add_module_preserves : forall p r mid,
  mid < p.(next_module_id) ->
  find_module (add_module p r) mid = find_module p mid.
Proof.
  intros p r mid Hlt.
  unfold add_module, find_module. simpl.
  (* Proof strategy: show that appending doesn't affect existing lookups *)
  (* Key insight: new module has ID = next_module_id > mid *)
  (* So find_module_in_list will find mid before reaching the new entry *)
  induction (modules p) as [| [id reg] rest IH].
  - (* Base case: empty modules list *)
    simpl.
    destruct (Nat.eqb mid (next_module_id p)) eqn:Heq.
    + (* mid = next_module_id, contradiction *)
      apply Nat.eqb_eq in Heq. lia.
    + (* mid <> next_module_id, both return None *)
      reflexivity.
  - (* Inductive case: (id, reg) :: rest *)
    simpl.
    destruct (Nat.eqb id mid) eqn:Heq.
    + (* Found it, return immediately *)
      reflexivity.
    + (* Not found, continue searching *)
      apply IH.
Qed.

(** Corollary: PNEW instruction preserves existing modules *)
Lemma pnew_preserves_modules : forall s r mid,
  mid < (next_module_id (partition s)) ->
  find_module (partition s) mid =
  find_module (partition (pnew_step s r)) mid.
Proof.
  intros s r mid Hlt.
  unfold pnew_step. simpl.
  symmetry.
  apply add_module_preserves.
  exact Hlt.
Qed.
```

### Proof Completion: module_independence

With `add_module_preserves`, the PNEW case in module_independence becomes:

```coq
- (* PNEW: Creates new module, but preserves existing modules *)
  unfold CoreSemantics.step in Hstep.
  destruct (halted s) eqn:Hhalted; try discriminate.
  rewrite Hnth in Hstep.
  destruct i as [r].  (* PNEW r *)
  injection Hstep as Heq_s'. subst s'.
  simpl.
  unfold module_of. simpl.
  (* Use add_module_preserves lemma *)
  apply add_module_preserves.
  (* Need to show m' < next_module_id *)
  (* This follows from m' being an existing module *)
  admit.  (* Needs module validity invariant *)
```

**Note:** May need an additional invariant that existing modules have IDs < next_module_id.

---

## Change 3: Enrich Receipt Structure

### Design Decision

**Add intermediate states to Receipt to enable full trace reconstruction.**

This makes receipts truly cryptographic and verifiable.

### Current Receipt (Coq)

```coq
Record Receipt : Type := {
  initial_partition : Partition;
  label_sequence : list Label;
  final_partition : Partition;
  total_mu : Z;
}.
```

**Problem:** No intermediate states → can't verify execution step-by-step.

### Proposed Enhanced Receipt (Coq)

```coq
(** Single execution step witness *)
Record StepWitness : Type := {
  pre_state : State;
  instruction : Instruction;
  label : Label;
  post_state : State;
  step_mu : Z;  (* μ-cost of this single step *)
}.

(** Enhanced Receipt with full execution trace *)
Record Receipt : Type := {
  initial_state : State;
  step_witnesses : list StepWitness;  (* Full step-by-step trace *)
  final_state : State;
  total_mu : Z;
}.

(** Validity predicate for receipts *)
Definition valid_receipt (r : Receipt) : Prop :=
  (* Initial state matches first witness *)
  (match r.(step_witnesses) with
   | [] => r.(initial_state) = r.(final_state)
   | w :: _ => r.(initial_state) = w.(pre_state)
   end) /\
  (* Each step is valid *)
  (forall i, i < length r.(step_witnesses) ->
    exists w, nth_error r.(step_witnesses) i = Some w /\
              step w.(pre_state) w.(label) w.(post_state)) /\
  (* Steps chain correctly *)
  (forall i, i < length r.(step_witnesses) - 1 ->
    exists w1 w2,
      nth_error r.(step_witnesses) i = Some w1 /\
      nth_error r.(step_witnesses) (S i) = Some w2 /\
      w1.(post_state) = w2.(pre_state)) /\
  (* Final state matches last witness *)
  (match List.last r.(step_witnesses) with
   | None => r.(initial_state) = r.(final_state)
   | Some w => r.(final_state) = w.(post_state)
   end) /\
  (* Total μ is sum of step costs *)
  r.(total_mu) = fold_left (fun acc w => acc + w.(step_mu))
                            r.(step_witnesses) 0.
```

### Python Receipt Alignment

The Python VM already has richer receipts (thielecpu/receipts.py):

```python
@dataclass
class StepReceipt:
    step: int
    instruction: InstructionWitness
    pre_state: Dict[str, Any]
    post_state: Dict[str, Any]
    observation: StepObservation
    pre_state_hash: str
    post_state_hash: str
    signature: str  # Ed25519 signature
```

**Strategy:** Make Coq Receipt isomorphic to Python's cryptographic receipts.

### Proof Completion: receipt_sound

With enhanced receipts:

```coq
Lemma receipt_sound : forall (r : Receipt),
  verify_receipt r = true ->
  exists t, make_receipt t = r.
Proof.
  intros r Hverify.
  (* Construct trace from step witnesses *)
  exists (witnesses_to_trace r.(step_witnesses)).
  unfold make_receipt.
  (* Show that make_receipt ∘ witnesses_to_trace is identity on valid receipts *)
  apply receipt_reconstruction_theorem.
  exact Hverify.
Qed.
```

---

## Cross-Layer Alignment Strategy

### Principle

**All three layers (Coq, Python, Verilog) must maintain structural isomorphism.**

### State Structure Alignment

| Field | Coq CoreSemantics | Python state.py | Verilog thiele_cpu.v |
|-------|-------------------|-----------------|----------------------|
| program | `program : Program` | `self.program : List[Instruction]` | N/A (ROM) |
| partition | `partition : Partition` | `self.partition : Partition` | `partition_*` regs |
| mu_ledger | `mu_ledger : MuLedger` | `self.mu_ledger : MuLedger` | `mu_accumulator` |
| pc | `pc : nat` | `self.pc : int` | `pc` register |
| halted | `halted : bool` | `self.halted : bool` | `halted` flag |
| result | `result : option nat` | `self.result : Optional[int]` | `result` register |

### Receipt Structure Alignment

| Component | Coq | Python | Verilog |
|-----------|-----|--------|---------|
| Step witness | `StepWitness` | `StepReceipt` | CSR exports |
| Cryptographic hash | Logical equality | SHA-256 | N/A |
| Signature | Logical proof | Ed25519 | N/A |

**Note:** Verilog doesn't generate receipts directly; Python VM creates receipts from hardware execution traces.

### Implementation Order

1. **Coq first** - Define enhanced structures formally
2. **Python second** - Align VM with new Coq definitions
3. **Verilog last** - Ensure hardware exports match receipt requirements
4. **Tests** - Update cross-layer isomorphism tests

---

## Risk Assessment

### High Risk

1. **Simulation.v breakage** - 29,668 lines, heavily uses State
   - Mitigation: Systematic find-replace with program field

2. **BridgeDefinitions.v complexity** - 40,113 lines
   - Mitigation: Modular bridge files reduce blast radius

### Medium Risk

3. **Proof script fragility** - Many proofs reference State fields
   - Mitigation: Keep field order consistent

4. **Python/Verilog desync** - Changes might break existing tests
   - Mitigation: Update tests in parallel with Coq changes

### Low Risk

5. **Receipt redesign** - Receipt is relatively isolated
   - Mitigation: Add new receipt type alongside old one initially

---

## Testing Strategy

### Phase 1: Coq Compilation
```bash
cd coq/thielemachine/coqproofs
coqc CoreSemantics.v
coqc ThieleSpaceland.v
```

### Phase 2: Full Proof Tree
```bash
make -C coq/thielemachine/coqproofs all
```

### Phase 3: Cross-Layer Tests
```bash
pytest tests/test_hardware_isomorphism.py -v
pytest tests/test_receipts.py -v
pytest tests/test_refinement.py -v
```

### Phase 4: Full Test Suite
```bash
pytest tests/ -v  # All 1173+ tests
```

---

## Success Criteria

### Must Have
- ✅ All 3 admits in ThieleSpaceland.v completed with `Qed`
- ✅ All Coq files compile without errors
- ✅ All existing tests pass (1173+)
- ✅ Cross-layer isomorphism tests pass

### Should Have
- ✅ Enhanced receipts implemented in Python VM
- ✅ Documentation updated
- ✅ New tests for enhanced receipts

### Nice to Have
- ✅ Verilog CSR exports aligned with new receipt structure
- ✅ Performance benchmarks show no regression

---

## Timeline Estimate

| Task | Estimated Time | Priority |
|------|----------------|----------|
| Change 1: Add program to State | 4-6 hours | P0 |
| Change 2: add_module_preserves lemma | 2-4 hours | P0 |
| Change 3: Enhance Receipt | 6-8 hours | P1 |
| Update downstream files | 8-12 hours | P0 |
| Testing and debugging | 4-6 hours | P0 |
| **TOTAL** | **24-36 hours** | |

**Note:** This is a focused engineering sprint requiring deep concentration.

---

## Conclusion

These architectural changes will:

1. **Achieve 100% proof completion** for ThieleSpaceland.v
2. **Strengthen formal guarantees** with determinism and module independence
3. **Enable cryptographic verification** with enhanced receipts
4. **Maintain cross-layer alignment** across Coq, Python, Verilog

The changes are **invasive but necessary** - they address fundamental design decisions that cannot be worked around.

**Recommendation:** Proceed with systematic implementation, starting with Change 1 (program in State) as it unblocks the most critical proof (step_deterministic).
