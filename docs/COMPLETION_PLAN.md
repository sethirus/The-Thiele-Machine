# Thiele Machine Completion Plan: Software-Only Proof of Claims

**Date Created:** October 11, 2025  
**Last Updated:** October 11, 2025  
**Agent Executor:** AI Coding Assistant  
**Objective:** Exhaust all software-only avenues to prove or disprove Thiele Machine claims (P=NP, RSA breaking, exponential separation). Iterate until axioms are mechanized, experiments scaled, and algorithms built. If gaps persist, document exact blockers.

This plan is derived from a comprehensive review of the repository. It prioritizes tasks by feasibility, impact, and dependencies. All tasks are software-only (Python, Coq, no hardware). Execute in order; iterate on failures with targeted fixes (up to 3 attempts per task). Validate each task with tests/compilation.

**Instructions:** Follow milestones in order. For each todo, perform the action, validate, then check it off (e.g., change [ ] to [x]). If a todo fails, iterate up to 3 times with fixes. Update this doc with progress notes. Loop back to earlier milestones if dependencies fail.

---

## Milestone 1: Axiom Mechanization
**Goal:** Mechanize all 8 axioms in Coq (from `coq/AXIOM_INVENTORY.md`). Eliminate soundness assumptions.  
**Dependencies:** Coq toolchain installed.  
**Validation:** `./coq/verify_subsumption.sh` compiles without `Admitted`.  
**Iteration:** If axiom proof fails, research Coq tactics, consult literature, or weaken axiom.

### Todos:
- [ ] **Audit Current Axioms**  
  - Read `coq/AXIOM_INVENTORY.md`.  
  - Prioritize: `check_step_sound`, `mu_lower_bound`, `check_step_complete`.  
  - Action: Create unit tests in `tests/` for each axiom.  
  - Validation: Tests pass; no runtime errors.  

- [ ] **Prove `check_step_sound`**  
  - File: `coq/thielemachine/coqproofs/ThieleMachine.v`.  
  - Action: Mechanize lemma; use Z3 for logic checks.  
  - Validation: Coq compiles; lemma proven.  
  - Iteration: If stuck, add intermediate lemmas; consult Coq docs.  

- [ ] **Prove `mu_lower_bound`**  
  - File: `coq/thielemachine/coqproofs/ThieleMachine.v`.  
  - Action: Link μ-bit accounting to receipts.  
  - Validation: Lemma holds; receipts verify.  
  - Iteration: Cross-check with Python VM (`thielecpu/vm.py`).  

- [ ] **Prove `check_step_complete`**  
  - File: `coq/thielemachine/coqproofs/ThieleMachine.v`.  
  - Action: Ensure completeness for receipt acceptance.  
  - Validation: Canonical receipts accepted.  
  - Iteration: Generate test receipts.  

- [ ] **Prove `decode_encode_id`**  
  - File: `coq/thielemachine/coqproofs/Simulation.v`.  
  - Action: Mechanize round-trip property.  
  - Validation: Identity holds on test encodings.  
  - Iteration: Use property-based testing.  

- [ ] **Prove `utm_simulation_steps`**  
  - File: `coq/thielemachine/coqproofs/Simulation.v`.  
  - Action: Bound simulation steps.  
  - Validation: Cost model proven.  
  - Iteration: Formalize interpreter.  

- [ ] **Prove `state_eqb_refl`**  
  - File: `coq/thielemachine/coqproofs/ThieleMachine.v`.  
  - Action: Prove equality reflexivity.  
  - Validation: Property tests pass.  
  - Iteration: Small mechanized proof.  

- [ ] **Prove Universal Axioms**  
  - Files: `coq/thieleuniversal/coqproofs/ThieleUniversal.v`.  
  - Action: Prove `pc_29_implies_registers_from_rule_table` and `find_rule_from_memory_components`.  
  - Validation: Universal reconstruction works.  
  - Iteration: Test with runtime traces.  

- [ ] **Full Coq Build**  
  - Action: Run `./coq/verify_subsumption.sh`.  
  - Validation: Exit code 0; no errors.  
  - Iteration: Fix any compilation issues.  

**Milestone Complete:** All axioms proven. Proceed to scaling.

---

## Milestone 2: Empirical Scaling
**Goal:** Scale `generate_tseitin_data.py` to n=10000+; demonstrate exponential blind blowup vs. polynomial sighted.  
**Dependencies:** Milestone 1 complete; HPC access if needed (simulate with budgets).  
**Validation:** Blind time >> sighted; receipts show gap.  
**Iteration:** Increase budgets/n; if no gap, test UNSAT instances.

### Todos:
- [ ] **Modify Script for n=1000**  
  - File: `scripts/generate_tseitin_data.py`.  
  - Action: Change `NS_TO_RUN = [1000]`; adjust budgets.  
  - Validation: Run script; blind time increases.  

- [ ] **Scale to n=10000**  
  - Action: Set `NS_TO_RUN = [10000]`; use multiprocessing.  
  - Validation: Blind diverges/times out; sighted fast.  
  - Iteration: If timeout, increase budgets; document limits.  

- [ ] **Test UNSAT Instances**  
  - Action: Modify `generate_tseitin_expander` to force contradictions.  
  - Validation: Blind fails; sighted detects UNSAT instantly.  
  - Iteration: Ensure GF(2) solver handles inconsistencies.  

- [ ] **Analyze Results**  
  - Action: Plot timings; compute exponents.  
  - Validation: Exponential fit for blind.  
  - Iteration: Use `experiments/run_analysis.py` for stats.  

- [ ] **Generate Receipts for Large n**  
  - Action: Ensure receipts are signed and verified.  
  - Validation: `python scripts/challenge.py verify receipts` passes.  

**Milestone Complete:** Gap proven at scale. Proceed to algorithms.

---

## Milestone 3: Algorithm Expansion
**Goal:** Build Thiele-native algorithms (factoring, SAT) to demonstrate generality.  
**Dependencies:** Milestones 1-2.  
**Validation:** Algorithms solve NP instances polynomially.  
**Iteration:** Extend to harder problems; if fails, refine partition logic.

### Todos:
- [ ] **Extend Factoring**  
  - File: `thiele_native_factor.py`.  
  - Action: Factor 100-bit numbers with Z3 partitions.  
  - Validation: Correct factors; μ-bits low.  

- [ ] **Build Thiele SAT Solver**  
  - Action: Implement in `thielecpu/vm.py`; use partitions for Tseitin.  
  - Validation: Solves instances faster than blind.  
  - Iteration: Integrate with `generate_tseitin_data.py`.  

- [ ] **Test on NP Problems**  
  - Action: Apply to TSP/knapsack via partitions.  
  - Validation: Polynomial time.  
  - Iteration: Benchmark vs. classical solvers.  

- [ ] **Integrate with VM**  
  - File: `thielecpu/vm.py`.  
  - Action: Add new opcodes for algorithms.  
  - Validation: VM executes correctly.  

- [ ] **Receipt Generation for Algorithms**  
  - Action: Generate signed receipts for algorithm runs.  
  - Validation: Verified with `scripts/challenge.py`.  

**Milestone Complete:** Algorithms work. Proceed to validation.

---

## Milestone 4: Final Validation & Report
**Goal:** Compile evidence; report if claims proven.  
**Dependencies:** All milestones.  
**Validation:** Comprehensive audit.  
**Iteration:** If incomplete, loop to gaps.

### Todos:
- [ ] **Run Full Suite**  
  - Action: Execute all scripts; verify receipts.  
  - Validation: All pass.  

- [ ] **Generate Report**  
  - Action: Update `RESULTS.md`; document proofs.  
  - Validation: Claims assessed.  

- [ ] **Assess Completion**  
  - Action: If proven, mark success; else, list blockers.  
  - Validation: Honest conclusion.  

- [ ] **Update Manifests**  
  - Action: Refresh SHA-256 hashes in `artifacts/MANIFEST.sha256`.  
  - Validation: Matches new outputs.  

- [ ] **Final Coq Check**  
  - Action: Re-run `./coq/verify_subsumption.sh`.  
  - Validation: All mechanized.  

**Milestone Complete:** Project finalized.

---

## Iteration Protocol
- **On Failure:** Retry task up to 3 times with fixes (e.g., debug Coq, increase budgets).  
- **Loop Back:** If milestone blocked (e.g., axiom unprovable), refine plan and restart.  
- **Exhaustion:** After 3 loops, conclude software limits reached.  
- **Logging:** Update this doc with progress notes; commit changes.

**Final Note:** This plan exhausts software proof. If claims unproven, recommend HPC/collaboration.</content>
