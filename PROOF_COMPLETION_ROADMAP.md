# Roadmap for Completing Admitted Proofs in Simulation.v

## Executive Summary

This document provides a detailed roadmap for completing the 3 remaining `Admitted` lemmas in the Thiele Machine universal interpreter formalization. These proofs require symbolic execution through CPU instruction sequences and are estimated to take 35-60 hours total.

**Current Status:**
- ✅ 0 Axioms (eliminated 20+)
- ✅ 0 Parameters (eliminated 4)
- ✅ All core definitions concrete
- ✅ Many lemmas proved
- ⚠️ 3 Admitted lemmas remain

**Files Involved:**
- `coq/thielemachine/coqproofs/ThieleUniversalBridge.v`: 2 admitted lemmas
- `coq/thielemachine/coqproofs/Simulation.v`: 1 admitted lemma

---

## Proof 1: `transition_Fetch_to_FindRule`

**Location:** `ThieleUniversalBridge.v`, line ~185-204

**Statement:**
```coq
Lemma transition_Fetch_to_FindRule (tm : TM) (conf : TMConfig) (cpu0 : CPU.State) :
  inv_core cpu0 tm conf ->
  IS_FetchSymbol (CPU.read_reg CPU.REG_PC cpu0) ->
  exists cpu_find, run_n cpu0 3 = cpu_find /\ 
                   IS_FindRule_Start (CPU.read_reg CPU.REG_PC cpu_find).
```

**What It Proves:**
Starting from PC=0 (FetchSymbol state), after exactly 3 CPU steps, we reach PC=3 (FindRule_Start state).

**Estimated Effort:** 10-15 hours

### Prerequisites

Before starting, ensure you understand:
1. CPU.step semantics from `CPU.v`
2. Instruction encoding in `UTM_Program.program_instrs`
3. The `run_n` recursive definition
4. Register operations (read_reg, set_reg)

### Proof Strategy

#### Phase 1: Unfold and Setup (1-2 hours)

1. **Unfold definitions:**
   ```coq
   unfold run_n, IS_FetchSymbol, IS_FindRule_Start in *.
   unfold inv_core in Hinv.
   ```

2. **Extract initial state:**
   ```coq
   destruct Hinv as [Hq [Hhead Hpc]].
   rewrite Hfetch in Hpc.
   (* Now we know PC = 0 *)
   ```

3. **Set up the goal:**
   ```coq
   exists (run1 (run1 (run1 cpu0))).
   split.
   - reflexivity.
   - (* Need to prove PC = 3 after 3 steps *)
   ```

#### Phase 2: Step 1 - From PC=0 to PC=1 (2-3 hours)

1. **Decode instruction at PC=0:**
   ```coq
   set (cpu1 := run1 cpu0).
   unfold run1, CPU.step.
   unfold decode_instr.
   (* Need to show: decode_instr_from_mem (mem cpu0) (4*0) = LoadConst REG_TEMP1 TAPE_START_ADDR *)
   ```

2. **Use program_instrs properties:**
   ```coq
   assert (Hprog0: nth 0 UTM_Program.program_instrs default_instr = 
                   LoadConst REG_TEMP1 TAPE_START_ADDR).
   { (* Prove from UTM_Program lemmas *) }
   ```

3. **Show memory contains program:**
   ```coq
   assert (Hmem: firstn (length program_instrs) (mem cpu0) = program_instrs).
   { (* From setup_state properties *) }
   ```

4. **Execute LoadConst:**
   ```coq
   simpl. (* Simplify CPU.step with LoadConst *)
   unfold CPU.exec_LoadConst.
   (* Show PC advances: read_reg REG_PC cpu1 = 1 *)
   ```

#### Phase 3: Step 2 - From PC=1 to PC=2 (2-3 hours)

Similar structure to Phase 2:

1. **Decode instruction at PC=1:**
   ```coq
   set (cpu2 := run1 cpu1).
   unfold run1, CPU.step.
   (* Show instruction at PC=1 *)
   ```

2. **Use program properties for PC=1:**
   ```coq
   assert (Hprog1: nth 1 UTM_Program.program_instrs default_instr = ...).
   ```

3. **Execute and show PC=2:**
   ```coq
   simpl.
   (* Prove PC advances to 2 *)
   ```

#### Phase 4: Step 3 - From PC=2 to PC=3 (2-3 hours)

Similar structure:

1. **Decode instruction at PC=2**
2. **Execute**
3. **Show PC=3**

#### Phase 5: Cleanup and Assembly (2-3 hours)

1. **Combine all steps:**
   ```coq
   unfold cpu1, cpu2 in *.
   rewrite step1_result.
   rewrite step2_result.
   rewrite step3_result.
   reflexivity.
   ```

2. **Handle edge cases:**
   - Memory bounds
   - Register count (always 10)
   - Cost tracking (not relevant for this proof)

### Key Lemmas to Develop

You'll likely need these helper lemmas:

```coq
Lemma program_at_pc : forall pc,
  pc < length program_instrs ->
  nth (4 * pc) (pad_to RULES_START_ADDR program_instrs) 0 = 
  encode_instr (nth pc program_instrs default_instr).

Lemma run1_pc_increment : forall cpu,
  (* Under certain conditions *)
  read_reg REG_PC (run1 cpu) = S (read_reg REG_PC cpu).

Lemma run1_preserves_inv : forall cpu tm conf,
  inv_core cpu tm conf ->
  (* Appropriate conditions *)
  inv_core (run1 cpu) tm conf.
```

### Testing Strategy

Test incrementally:

```coq
(* Test step 1 alone *)
Lemma test_step1: 
  forall cpu0, 
    read_reg REG_PC cpu0 = 0 ->
    read_reg REG_PC (run1 cpu0) = 1.

(* Test steps 1-2 *)
Lemma test_step2:
  forall cpu0,
    read_reg REG_PC cpu0 = 0 ->
    read_reg REG_PC (run1 (run1 cpu0)) = 2.

(* Then complete *)
```

---

## Proof 2: `transition_FindRule_to_ApplyRule`

**Location:** `ThieleUniversalBridge.v`, line ~206-228

**Statement:**
```coq
Lemma transition_FindRule_to_ApplyRule 
  (tm : TM) (conf : TMConfig) (cpu_find : CPU.State) 
  (q' write : nat) (move : Z) :
  let '(q, tape, head) := conf in
  let sym := nth head tape (tm_blank tm) in
  inv_core cpu_find tm conf ->
  find_rule_start_inv tm conf cpu_find ->
  find_rule (tm_rules tm) q sym = Some (q', write, move) ->
  exists k cpu_apply, run_n cpu_find k = cpu_apply.
```

**What It Proves:**
Starting at PC=3 (FindRule_Start), when a matching rule exists, the CPU executes the rule-search loop and eventually reaches the ApplyRule state.

**Estimated Effort:** 15-25 hours (most complex proof)

### Prerequisites

1. **Loop structure understanding:**
   - Entry: PC=3
   - Loop body: Check current rule
   - Exit condition: Rule matches
   - Exit target: ApplyRule state

2. **Memory layout:**
   - Rules encoded at RULES_START_ADDR
   - Each rule: (q_old, sym_old, q_new, write, move)
   - Rules packed consecutively

3. **Register usage:**
   - REG_Q: Current state
   - REG_SYM: Current symbol
   - REG_ADDR: Address pointer into rule table
   - REG_TEMP1, REG_TEMP2: Comparison results

### Proof Strategy

#### Phase 1: Loop Invariant Design (3-5 hours)

Define the loop invariant:

```coq
Definition FindRule_Loop_Inv (tm : TM) (conf : TMConfig) 
                             (cpu : CPU.State) (i : nat) : Prop :=
  (* i = number of rules checked so far *)
  read_reg REG_PC cpu = 3 ∨ read_reg REG_PC cpu = 5 ∨ (* loop PCs *) /\
  read_reg REG_Q cpu = fst (fst conf) /\
  read_reg REG_SYM cpu = nth (snd conf) (snd (fst conf)) (tm_blank tm) /\
  read_reg REG_ADDR cpu = RULES_START_ADDR + i * RULE_SIZE /\
  (* All rules checked so far didn't match *)
  forall j, j < i -> 
    nth j (tm_rules tm) default_rule <> (fst (fst conf), nth (snd conf) ...).
```

#### Phase 2: Loop Induction Setup (2-3 hours)

```coq
Proof.
  intros q tape head sym Hinv_core Hstart_inv Hfind.
  
  (* Find index of matching rule *)
  pose proof (find_rule_index tm.(tm_rules) q sym Hfind) as [idx [Hidx Hrule]].
  
  (* Prove by induction on idx *)
  exists (compute_steps idx). (* Number of steps depends on idx *)
  exists (loop_result idx).
  
  (* Use strong induction on loop iterations *)
  apply (loop_induction idx).
```

#### Phase 3: Loop Body Proof (4-6 hours)

For each iteration i < idx:

```coq
Lemma loop_iteration_not_match : forall i,
  i < idx ->
  FindRule_Loop_Inv tm conf (run_n cpu_find (steps i)) i ->
  nth i (tm_rules tm) <> (q, sym) ->
  FindRule_Loop_Inv tm conf (run_n cpu_find (steps (S i))) (S i).
Proof.
  (* Execute loop body for non-matching rule *)
  (* 1. Load rule from memory *)
  (* 2. Compare with (q, sym) *)
  (* 3. Branch: no match, continue *)
  (* 4. Increment address pointer *)
  (* 5. Jump back to loop head *)
Qed.
```

#### Phase 4: Loop Exit Proof (3-5 hours)

```coq
Lemma loop_exit_match : forall cpu_at_idx,
  FindRule_Loop_Inv tm conf cpu_at_idx idx ->
  nth idx (tm_rules tm) = (q, sym, q', write, move) ->
  exists cpu_apply,
    run_n cpu_at_idx EXIT_STEPS = cpu_apply /\
    read_reg REG_PC cpu_apply = APPLY_RULE_PC.
Proof.
  (* Execute matching iteration *)
  (* 1. Load rule from memory *)
  (* 2. Compare: MATCH *)
  (* 3. Branch to ApplyRule *)
  (* 4. Exit loop *)
Qed.
```

#### Phase 5: Step Count Calculation (2-3 hours)

```coq
Definition steps_to_idx (i : nat) : nat :=
  (* Each non-matching iteration: ~10-15 instructions *)
  (* Depends on exact program structure *)
  i * ITER_STEPS + ENTRY_OVERHEAD.

Lemma step_count_correct : forall i,
  run_n cpu_find (steps_to_idx i) = loop_state i.
```

#### Phase 6: Assembly (1-2 hours)

Combine all pieces:

```coq
(* Main proof continues *)
rewrite <- (loop_composition idx).
apply loop_exit_match.
- (* Show invariant at idx *)
- (* Show rule matches at idx *)
Qed.
```

### Key Challenges

1. **Variable iteration count:** Number of steps depends on where matching rule is in table
2. **Memory reasoning:** Must track rule encodings in memory
3. **Branch reasoning:** Conditional jumps based on comparison results
4. **Register preservation:** Some registers preserved across iterations

### Helper Lemmas Needed

```coq
Lemma find_rule_index : forall rules q sym q' w m,
  find_rule rules q sym = Some (q', w, m) ->
  exists i, 
    i < length rules /\
    nth i rules default = (q, sym, q', w, m).

Lemma rule_encoding_correct : forall rule addr,
  (* Rule at address addr is correctly encoded *)
  ...

Lemma comparison_semantics : forall cpu a b,
  (* How Cmp instruction works *)
  ...

Lemma branch_semantics : forall cpu cond,
  (* How conditional branches work *)
  ...
```

---

## Proof 3: `utm_interpreter_no_rule_found_halts`

**Location:** `Simulation.v`, line ~3700-3723

**Statement:**
```coq
Lemma utm_interpreter_no_rule_found_halts :
  forall tm conf cpu_find,
    let '((q, tape), head) := conf in
    let sym := nth head tape tm.(tm_blank) in
    find_rule tm.(tm_rules) q sym = None ->
    ThieleUniversal.inv_core cpu_find tm conf ->
    ThieleUniversal.find_rule_start_inv tm conf cpu_find ->
    rules_fit tm ->
    decode_state tm (cpu_state_to_thiele_state tm (ThieleUniversal.run_n cpu_find 10)) = conf.
```

**What It Proves:**
When no rule matches, the CPU executes through all rules (finding none match), reaches the halt state at PC=11, and the TM configuration remains unchanged.

**Estimated Effort:** 10-20 hours

### Prerequisites

Same as Proof 2, plus:
1. Understanding of halt detection
2. Configuration preservation properties

### Proof Strategy

#### Phase 1: Loop Exhaustion (4-6 hours)

Similar to Proof 2, but all iterations fail:

```coq
Proof.
  intros tm ((q, tape), head) cpu_find sym Hno_rule Hinv Hstart Hfit.
  
  (* Prove we check ALL rules *)
  pose proof (check_all_rules tm cpu_find) as Hall.
  
  (* Induction on number of rules *)
  induction (tm_rules tm) as [|rule rules IH].
  - (* Base: empty rules, immediate halt *)
  - (* Step: check one rule, doesn't match, continue *)
Qed.
```

#### Phase 2: Halt State Proof (2-4 hours)

```coq
Lemma no_match_leads_to_halt : forall tm cpu_find,
  find_rule_start_inv tm conf cpu_find ->
  (forall rule, In rule (tm_rules tm) -> 
    rule <> (q, sym, _, _, _)) ->
  exists cpu_halt,
    run_n cpu_find (exhaustion_steps tm) = cpu_halt /\
    read_reg REG_PC cpu_halt = 11. (* Halt PC *)
```

#### Phase 3: Configuration Preservation (3-5 hours)

Prove configuration unchanged:

```coq
Lemma config_preserved_no_match : forall tm conf cpu_start cpu_halt,
  inv_core cpu_start tm conf ->
  run_n cpu_start k = cpu_halt ->
  (* No matching rule executed *)
  cpu_state_to_tm_config cpu_halt = conf.
Proof.
  (* Key insight: no writes to memory/registers that encode config *)
  (* Registers REG_Q, REG_HEAD remain unchanged *)
  (* Tape in memory unchanged *)
Qed.
```

#### Phase 4: Decode/Encode Round-Trip (1-2 hours)

```coq
(* Use existing lemmas *)
rewrite decode_encode_roundtrip.
apply config_preserved_no_match.
```

### Key Lemmas Needed

```coq
Lemma exhaustion_steps_exact : forall tm,
  rules_fit tm ->
  exhaustion_steps tm = 10.

Lemma find_rule_none_means_all_checked : forall tm q sym,
  find_rule (tm_rules tm) q sym = None ->
  forall rule, In rule (tm_rules tm) ->
    fst (fst rule) <> q \/ snd (fst rule) <> sym.

Lemma halt_pc_stable : forall cpu,
  read_reg REG_PC cpu = 11 ->
  run_n cpu k = cpu. (* Halted state is stable *)
```

---

## Common Infrastructure

### Shared Helper Lemmas (Apply to All Proofs)

These should be proved first (5-8 hours total):

```coq
(* Memory access *)
Lemma mem_unchanged_at : forall cpu cpu' addr,
  (* Under certain conditions, memory at addr unchanged *)
  nth addr (mem cpu) 0 = nth addr (mem cpu') 0.

(* Register access *)
Lemma reg_unchanged : forall cpu cpu' r,
  (* Under certain conditions, register r unchanged *)
  read_reg r cpu = read_reg r cpu'.

(* Instruction decoding *)
Lemma decode_deterministic : forall mem pc,
  (* Decoding is deterministic *)
  decode_instr_from_mem mem pc = unique_result.

(* PC progression *)
Lemma pc_bounds : forall cpu,
  inv_min cpu tm conf ->
  0 <= read_reg REG_PC cpu < PROGRAM_LENGTH.

(* Step composition *)
Lemma run_n_add : forall cpu m n,
  run_n cpu (m + n) = run_n (run_n cpu m) n.

(* Step decomposition *)
Lemma run_n_S : forall cpu n,
  run_n cpu (S n) = run1 (run_n cpu n).
```

### Automation Tactics

Develop custom tactics to reduce repetition:

```coq
(* Symbolic execution tactic *)
Ltac symbolic_step :=
  unfold run1, CPU.step;
  unfold decode_instr, decode_instr_from_mem;
  simpl;
  (* Case analysis on instruction *)
  destruct_instruction;
  simpl;
  (* Simplify register/memory operations *)
  autorewrite with cpu_ops.

(* Invariant maintenance *)
Ltac maintain_inv :=
  split; [| split]; (* For 3-part conjunctions *)
  try reflexivity;
  try (simpl; lia);
  try (unfold read_reg; simpl; reflexivity).

(* Memory lookup *)
Ltac resolve_mem_lookup :=
  rewrite program_at_pc;
  try rewrite pad_to_nth;
  simpl;
  reflexivity.
```

---

## Development Workflow

### Recommended Order

1. **Week 1 (15-20 hours):**
   - Develop common infrastructure lemmas
   - Develop automation tactics
   - Complete Proof 1 (`transition_Fetch_to_FindRule`)
   - Test thoroughly

2. **Week 2 (15-20 hours):**
   - Start Proof 2 (`transition_FindRule_to_ApplyRule`)
   - Develop loop invariant
   - Prove 2-3 loop iterations manually
   - Generalize to full proof

3. **Week 3 (10-15 hours):**
   - Complete Proof 3 (`utm_interpreter_no_rule_found_halts`)
   - Reuse infrastructure from Proof 2
   - Integration testing
   - Documentation

### Testing Strategy

For each proof:

1. **Unit tests:** Test individual steps
2. **Integration tests:** Test multi-step sequences
3. **Edge cases:** Boundary conditions
4. **Regression:** Ensure previous proofs still work

Example test structure:

```coq
Section Tests.
  Variable tm : TM.
  Variable conf : TMConfig.
  
  (* Positive test: things that should work *)
  Lemma test_single_step_positive : ...
  
  (* Negative test: things that shouldn't *)
  Lemma test_single_step_bounds : ...
  
  (* Stress test: many steps *)
  Lemma test_many_steps : ...
End Tests.
```

### Documentation Requirements

For each completed proof, document:

1. **Proof summary:** High-level strategy
2. **Key insights:** Non-obvious observations
3. **Lemmas developed:** Reusable components
4. **Time spent:** Actual vs. estimated
5. **Challenges encountered:** For future reference

---

## Resource Requirements

### Skills Needed

- **Coq proficiency:** Intermediate to advanced
- **Symbolic execution:** Understanding of forward symbolic execution
- **CPU semantics:** Familiarity with low-level execution models
- **Loop reasoning:** Induction, invariants, variants
- **Patience:** Symbolic execution proofs are tedious

### Tools Recommended

1. **CoqIDE or VSCoq:** For interactive development
2. **coq-elpi or Ltac2:** For more powerful automation
3. **Proof General:** Classic Emacs integration
4. **Documentation:** Keep detailed notes

### External Resources

- Coq Art book: Chapters on induction and recursion
- Software Foundations: Volume on Program Logic
- Papers on verified compilers: Similar symbolic execution challenges
- CompCert: Example of large-scale CPU formalization

---

## Success Criteria

The proofs are complete when:

1. ✅ All 3 lemmas have `Qed.` instead of `Admitted.`
2. ✅ File compiles without errors
3. ✅ No new axioms introduced
4. ✅ All helper lemmas proved
5. ✅ Documentation updated
6. ✅ Tests pass

---

## Risk Mitigation

### Potential Blockers

1. **Complexity explosion:** Too many cases in symbolic execution
   - **Mitigation:** Develop strong automation early
   
2. **Missing CPU semantics:** Incomplete CPU.step definition
   - **Mitigation:** Verify CPU.v is complete first
   
3. **Program structure assumptions:** Assumptions about program_instrs
   - **Mitigation:** Validate with program authors
   
4. **Performance:** Coq proof checking too slow
   - **Mitigation:** Use `Qed.` selectively, `Defined.` for transparent proofs

### Fallback Options

If a proof proves too difficult:

1. **Simplify goal:** Prove weaker version
2. **Add assumptions:** Document what's assumed
3. **Alternative approach:** Different proof strategy
4. **Seek help:** Coq community, proof assistants forum

---

## Conclusion

This roadmap provides a structured approach to completing the final 3 admitted proofs. The work is substantial but well-scoped. By following this roadmap methodically, the proofs can be completed within the estimated 35-60 hour timeframe.

**Key Success Factors:**
- Start with infrastructure
- Test incrementally
- Automate repetitively
- Document thoroughly
- Stay patient

**Expected Outcome:**
A fully verified universal Turing machine interpreter with zero axioms, zero parameters, and zero admitted lemmas - a significant achievement in formal verification.

---

## Appendix: Quick Reference

### File Structure
```
coq/thielemachine/coqproofs/
├── ThieleUniversalBridge.v   (Proofs 1 & 2)
├── Simulation.v               (Proof 3)
├── CPU.v                      (CPU semantics)
├── UTM_Program.v             (Program definition)
└── [supporting files]
```

### Proof Status Tracking
```
[ ] Proof 1: transition_Fetch_to_FindRule
    [ ] Infrastructure (2-3h)
    [ ] Step 1 (2-3h)
    [ ] Step 2 (2-3h)
    [ ] Step 3 (2-3h)
    [ ] Cleanup (2-3h)
    
[ ] Proof 2: transition_FindRule_to_ApplyRule
    [ ] Loop invariant (3-5h)
    [ ] Induction setup (2-3h)
    [ ] Loop body (4-6h)
    [ ] Loop exit (3-5h)
    [ ] Step count (2-3h)
    [ ] Assembly (1-2h)
    
[ ] Proof 3: utm_interpreter_no_rule_found_halts
    [ ] Loop exhaustion (4-6h)
    [ ] Halt state (2-4h)
    [ ] Config preservation (3-5h)
    [ ] Round-trip (1-2h)
```

### Contact Points

For questions or assistance:
- **Coq Discourse:** https://coq.discourse.group/
- **Coq Zulip:** https://coq.zulipchat.com/
- **StackOverflow:** Tag `coq`
- **Repository Issues:** Open issues with `proof-help` label
