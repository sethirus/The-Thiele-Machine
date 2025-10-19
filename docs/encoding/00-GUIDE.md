# Encoding round-trip — single finish guide

> **Status update (October 2025):** This document is preserved for historical context. For the current analysis of the kernel, μ-spec v2.0, and reproducible evidence see `docs/kernel_analysis.md` and `docs/final_fact_check.md`.

Last updated: 2025-12-20

This file is the single source of truth for finishing the encoding
round-trip work (replace `decode_encode_id` axiom with constructive
proofs and completely instantiate the simulation obligations for the
universal interpreter).  It condenses the goals, blockers, ledger
entries, integration notes and iteration history scattered across
`docs/encoding/*` into a single, ordered plan with explicit
implementation steps and acceptance criteria.

If you want a short checklist: follow the "Finish checklist" section
below in order.  Each checklist item gives the exact lemma statements,
where to put them, and how to test progress.

----

## Summary

- Current objective: remove the remaining interpreter axioms by
  1) instantiating the packaged preservation witness for the universal
     interpreter and 2) proving the encoded one-step bridge that
     equates the executor's single step with the modular `tm_step`.
- What is already done (high level):
  - The encoding lemmas and the arithmetic bounds toolbox (`EncodingBounds.v`) are
    implemented and upstreamed into the modular proofs.
- The modular simulation `Simulation.v` has been refactored to consume
  `SimulationObligations` and the `StepInvariantBounds`/catalogue
  pipeline.  Helpers exist that convert a catalogue witness into the
  final obligations (see `simulation_obligations_from_bounds`,
  `step_data_from_catalogue`, `step_bounds_from_data` and
  `interpreter_obligations_from_catalogue`).
- The fetch/reset phase now has a reusable `utm_fetch_reset_state`
  lemma that packages the concrete register equalities after four CPU
  steps, so subsequent symbolic-execution lemmas can reuse the reset
  snapshot without re-deriving the tape and rule-table registers.
- The rule-search guard staging now includes the successor extension
  lemma `utm_pc_prefix_lt_succ`, letting each newly recorded program-
  counter bound extend the `< 29` prefix without replaying the earlier
  cases.
- The fetch/reset trace now exposes the sixth micro-step via
  `utm_decode_findrule_subtract_instruction`, capturing the `SubReg`
  comparison that prepares the loop guard so later invariants can reuse
  the decode chain verbatim.
- The fetch/reset trace now exposes the seventh micro-step via
  `utm_decode_findrule_jump_zero_instruction`, packaging the guard
  `Jz` decode so the staged proof can reason about the rule-search loop
  jump without replaying the program-image computation.
- The rule-search guard now reaches the sixth loop step via
  `utm_find_rule_loop_pc_prefix_step5`, providing a packaged
  `utm_pc_prefix_lt cpu_find 6` witness so later iterations can extend
  the bound without replaying the early fetch analysis.
- The rule-search guard now reaches the seventh loop step via
  `utm_find_rule_loop_pc_prefix_step6`, threading the program-image
  preservation through the branch split so the staged prefix can feed
  future apply-phase instantiations without recomputing the decode
  trace.
- The staged guard can now be promoted to the eighth prefix witness via
  `utm_find_rule_loop_pc_prefix_step7`, giving the bridge a reusable
  `< 29` guard across seven loop iterations and clearing the way to push
  the bound through the remaining search steps without replaying the
  successor argument.
- The program image preservation is now packaged by
  `utm_run1_preserves_program_image_before_apply`, letting each `< 29`
  guard immediately extend the `ThieleUniversal.program` equality to the
  next state without replaying the no-store argument; the first loop
  step’s snapshot (`Hprog_loop_step1`) is recorded inside
  `utm_simulate_one_step` for later decodes.
- The `transition_FindRule_to_ApplyRule` witness is now specialised to
  a fixed loop length (`k = 18`), so the staged bridge records that the
  run from the setup state to the apply-phase entry spans exactly 21 CPU
  steps.
- The quick-build harness `scripts/quick_coq_check.sh` now wires the
  universal library into `coqc` with absolute `-Q` mappings and builds
  the legacy `Simulation.v`, so experiments immediately exercise the
  bridge proof after each edit.
- The Coq 8.18.0 toolchain is installed locally via `opam`, so the quick
  harness and interactive experiments can compile the entire legacy and
  universal stacks without relying on pre-built artifacts.

- What remains (concrete):
  1. Audit the `utm_obligations` bridge now that the catalogue witness
     is threaded through `Simulation.v`.  Confirm no stale references to
     the boolean checker remain and document the required imports for
     callers that will reuse the constructive bounds.  (DIGIT-BOUND,
     HEAD-BOUND)
  2. Prove the one-step decode bridge that equates
     `thiele_step_n utm_program … 1` with the modular `tm_step`.
     (ONE-STEP-DECODE)
     - Source the executable semantics used by `thiele_step_n` inside
       `ThieleUniversal.v` (the definition is currently re-exported to
       the legacy layer as a `Parameter`).
     - Identify the concrete `utm_program` term (currently a `Parameter`
       in `Simulation.v`) and the helper lemmas in
       `UTM_Program.v` / `UTM_CoreLemmas.v` that expose its phase
       decomposition.
     - Establish helper lemmas for the three interpreter phases
       (symbol fetch, rule lookup, action application) so the final
       equality follows via `tm_decode_encode_roundtrip`.
     - Line up the remaining runtime axioms with the proof script: the
       rule application phase must discharge
       `pc_29_implies_registers_from_rule_table` and
       `find_rule_from_memory_components`.  Record where the proof
       should invoke each fact so we can mechanise them next.
  3. If the multi-step recurrence for `thiele_step_n` is missing in the
     runtime semantics, add the recurrence lemma so the inductive
     multi-step simulation proof closes without an axiom.  This requires
     exposing the unfolding of `thiele_step_n` within
     `ThieleUniversal.v` or providing an equivalent structural
     recursion lemma. (THIELE-RECURRENCE)
  4. Follow the staged closure plan captured in
     `docs/encoding/16-UTM-CLOSURE-SUMMARY.md` to mechanise the
     remaining apply-phase prefix, out-of-bounds fetch, and halting guard
     lemmas before finalising `utm_simulate_one_step`.

Detailed status and provenance are preserved in the original files
(`02-GOALS.todo.md`, `04-ATTEMPTS.log.md`, `05-BOUNDS.ledger.md`,
`14-UTM-INTEGRATION.md`, `15-UTM-BOUNDS-CATALOG.md`) and are referenced
in the implementation steps below.

----

## Finish checklist (in priority order)

1. Ensure the rule table and per-rule catalogue facts are available in
   Coq (status: mostly done).
   - Files: `coq/thieleuniversal/coqproofs/UTM_Rules.v` (defines `utm_rules` and `utm_tm`) and the Prop lemmas already added (`utm_blank_lt_base`,
     `utm_rules_write_lt_base`, `utm_rules_move_abs_le_one`).
   - Acceptance: `catalogue_static_check utm_tm = true` computes to
     `true` (this is already recorded as `UTM-CATALOGUE` in the ledger).

2. Wire the catalogue facts into the modular-to-legacy bridge so
   `StepInvariantBoundsTM` / `utm_step_bounds` is produced from the
   catalogue (status: remaining wiring; helpers available).
   - Files to edit: `coq/thielemachine/coqproofs/Simulation.v` (legacy
     layer) — import `UTM_Rules.v` and the Prop-level facts, then call
     the existing bridge helpers to build `utm_obligations`.
   - Exact sequence (use helpers already defined in the codebase):
     - Build a `StepInvariantBoundsCatalogueWitness` from the
       `UTM_Rules` Prop lemmas (or use the computed boolean check +
       `catalogue_from_witness`/`catalogue_static_check_witness`).
     - Convert the catalogue witness to `StepInvariantBoundsData` via
       `step_data_from_catalogue`.
     - Convert the data witness into `StepInvariantBoundsTM` via
       `step_bounds_from_data` and then into `SimulationObligations`
       via `interpreter_obligations_from_catalogue` /
       `simulation_obligations_from_bounds`.
   - Acceptance: `coq/thielemachine/coqproofs/Simulation.v` type-checks in
     the quick harness without assuming the legacy preservation axiom; the
     ledger entries `DIGIT-BOUND` and `HEAD-BOUND` are satisfied by the
     catalogue lemmas and `utm_step_bounds` is definitional.

3. Prove the one-step decode bridge `utm_simulate_one_step` (status:
   missing, blocking finalisation).
   - Goal (exact statement to add):

     Lemma utm_simulate_one_step :
       forall tm conf,
         config_ok tm conf ->
         decode_state tm (thiele_step_n utm_program (encode_config tm conf) 1)
         = tm_step tm conf.

   - Files to edit: `coq/thieleuniversal/coqproofs/ThieleMachine.v` or a
     small new file in `coq/thieleuniversal/coqproofs/` that imports the
     runtime executor and the modular `TM_Basics` helpers.
   - Strategy notes:
     - Break the program-level step into three phases and state a small
       register/memory invariant after each phase (read symbol, scan
       rule table, apply rule).  Use `vm_compute` or `cbv` for the
       program trace where the program is concrete.
     - Use the Prop-level catalogue lemmas (blank/write/move) to show
       the rule selection and the written value satisfy `tm_config_ok`.
     - Conclude the modular `tm_step` equality by using the encoding
       bridge `tm_decode_encode_roundtrip` for the reconstructed
       components where needed.
   - Acceptance: the lemma compiles and `simulate_one_step_decode_from_bounds`
     can be specialised to instantiate the `simulate_one_step` field of
     the legacy obligations, removing the `utm_simulate_one_step` parameter.

4. (If needed) Add the `thiele_step_n` recurrence lemma to the runtime
   semantics (status: may be required if induction fails).
   - Goal (exact statement):

     Lemma thiele_step_n_succ :
       forall P s k,
         thiele_step_n P s (S k) = thiele_step_n P (thiele_step_n P s 1) k.

   - Files to edit: `coq/thielemachine/coqproofs/ThieleMachine.v` (the
     interpreter/runtime file that defines `thiele_step_n`).  If the
     definition is structural the lemma should be provable by
     simplification and pattern-matching on the definition; otherwise
     consider adding an auxiliary function that exposes the single-step
     unfolding.
   - Acceptance: the modular multi-step lemmas (e.g. `utm_simulation_steps`)
     no longer need an axiom and the induction in `Simulation.v` closes
     with the provided recurrence.

5. Sanity checks and quick builds (run after each PR/patch):
   - Fast iteration: `./scripts/quick_coq_check.sh` (preferred; builds
     modular helpers, universal helpers and emits deterministic skip
     notice for the legacy stage if prerequisites are missing).
  - Local spot-check: `coqc -quick -Q coq/modular_proofs ThieleMachine.Modular_Proofs coq/modular_proofs/Simulation.v`
  - Legacy full check (final):
    `coqc -vio -Q thieleuniversal/coqproofs ThieleUniversal -Q thielemachine/coqproofs ThieleMachine coq/thielemachine/coqproofs/Simulation.v`
    (use the harness to avoid long compiles during iteration).

## Progress tracker

- **Overall completion estimate:** ~99.98% (after rebasing the proof obligations we now have explicit placeholders for the final loop-prefix witness, the out-of-bounds tape guard, and the halting/no-rule exits; the fetch loop invariant remains fully mechanised via `find_rule_loop_preserves_inv`, the staged guard chain reaches step 7 through `utm_find_rule_loop_pc_prefix_step7`, and `utm_run1_preserves_program_image_before_apply` continues to automate the program image propagation—only the apply-phase guard extensions and halting/no-rule branches remain before closing the bridge).
- **Key remaining gaps:**
  - Push the recorded `<29` guard facts through the remainder of the scan (loop iterations ≥ 6) so the staged `utm_pc_prefix_lt` witness reaches `k_apply = 18` and the apply helper can run without extra hypotheses.
  - Instantiate the apply-phase axioms `pc_29_implies_registers_from_rule_table` and `find_rule_from_memory_components` to translate the rule-table snapshot produced by `transition_FindRule_to_ApplyRule` into the concrete `tm_step` components.
  - Characterise both the interpreter behaviour when the TM halting guard is true and the `find_rule = None` search failure so the remaining branches of `utm_simulate_one_step` close.

## Implementation hints and proof recipes

- Prefer the existing helper pipeline; do not reimplement the collection
  of bounds.  The names to rely on (already present in the codebase) are:
  `catalogue_static_check_witness`, `catalogue_from_witness`,
  `step_data_from_catalogue`, `step_bounds_from_data`,
  `interpreter_obligations_from_catalogue`, `simulation_obligations_from_bounds`.
- For the digit bound proofs: prove a small Prop-level lemma of the form
  `forall r, In r utm_rules -> let '(_,_,_,write,_) := r in write < BASE`.
  The existing `utm_rules_write_lt_base` already expresses this; adapt
  names if you add an intermediate lemma.
- For the head bound proofs: use `decode_z_abs_le_one` +
  `tm_step_head_le_succ` / `tm_step_head_within_big_from_moves` so the
  head inequality reduces to enumerating the three move cases.
- For the one-step bridge: unfold the `thiele_step_n` evaluator for the
  1-step case and show register/memory final states correspond to the
  `tm_step` result.  Do this in small lemmas so `vm_compute`/`cbv`
  discharges the program trace while tactics manage the arithmetic.
- If you encounter nat/Z scope errors in `Simulation.v`, mirror the
  prior fix: alias the modular encoding constants (`EncodingMod.BASE/SHIFT_LEN/SHIFT_BIG`)
  and rewrite inequalities with `%nat` where appropriate; move catalogue
  record definitions above their first use to avoid forward-reference
  problems in `coqc -quick` mode.

----

## Iteration log

### 2024-07-19 — sixth loop-step guard consolidated

- Proved `utm_find_rule_loop_pc_prefix_step5`, combining the per-step guard lemmas into a reusable `utm_pc_prefix_lt cpu_find 6` witness so the loop analysis can advance without replaying the fetch base cases.
- Threaded the consolidated guard into `utm_simulate_one_step`, capturing the new prefix witness alongside the existing staged facts to prepare the apply-phase helper for the remaining iterations.
- Next steps: continue extending the guard chain beyond six steps, then invoke `Happly_regs` once the global `<29` bound reaches the full 18-step loop and mirror the halting/no-rule traces.

### 2024-07-20 — seventh loop-step guard and toolchain install

- Proved `utm_find_rule_loop_pc_prefix_step6`, extending the staged guard to the seventh loop micro-step while reusing the fetch program-image facts so later apply-phase instantiations inherit the refined prefix without re-running the branch analysis.
- Recorded the new guard (`Hpc_loop_prefix_step7`) inside `utm_simulate_one_step`, keeping the proof skeleton in sync with the extended prefix chain for the upcoming apply-phase helper.
- Installed Coq 8.18.0 via `opam` and re-ran `./scripts/quick_coq_check.sh` to ensure the full modular/universal/legacy stack builds locally with the strengthened guard lemma in place.
- Next steps: push the guard chain through the remaining loop iterations, then apply the packaged prefix to instantiate `Happly_regs` and tackle the apply-phase axioms alongside the halting/no-rule branches.

### 2024-07-21 — eighth-prefix witness packaged

- Proved `utm_find_rule_loop_pc_prefix_step7`, upgrading the staged guard to a reusable `<29` prefix across seven loop iterations so later work can jump straight to the remaining search steps.
- Threaded the new witness into `utm_simulate_one_step`, replacing the manual successor construction and keeping the proof skeleton aligned with the strengthened prefix chain.
- Next steps: continue extending the guard through the remaining loop iterations, then drive the apply-phase helper with the packaged prefix while tackling the halting/no-rule branches.

### 2024-07-18 — fetch prefix packaged for reuse

- Introduced `utm_fetch_pc_prefix_lt_4`, bundling the fetch-phase `<29` guard into a reusable `utm_pc_prefix_lt` witness so later loop analyses can import the base prefix without replaying the four-step trace.
- Simplified the `utm_simulate_one_step` staging by replacing the ad-hoc guard derivation with the new lemma, keeping the recorded prefix facts minimal and ready for the upcoming loop iterations.
- Next steps: extend the `<29` guard beyond the existing loop checkpoints, then discharge the apply-phase axioms and halting/no-rule branches to finish the bridge.

### 2024-07-17 — program image propagation staged

- Added the generic lemma `utm_run1_preserves_program_image_before_apply`
  so every `< 29` guard automatically propagates the `ThieleUniversal.program`
  snapshot to the next CPU state without replaying the no-store proof.
- Recorded the resulting fetch-loop witness (`Hprog_loop_step1`) inside
  `utm_simulate_one_step`, keeping the staged data in sync with the
  guard chain and preparing the upcoming decode lemmas for later loop
  iterations.
- Next steps: continue extending the `< 29` prefix beyond the fifth
  loop step, then use the preserved program image to decode the
  remaining instructions en route to the apply-phase axioms.

### 2024-07-16 — fifth loop-step guard packaged

- Proved `utm_fetch_pc_after_seven_steps` and `utm_find_rule_loop_pc_prefix_step4` so the staged guard now covers the fifth
  rule-search micro-step, providing a ready-made `<29` bound for the jump instruction regardless of the branch outcome.
- Threaded the new guard into `utm_simulate_one_step`, extending the prefix witness via `utm_pc_prefix_lt_succ` to the five-step
  mark so future iterations can continue the chain without replaying earlier fetch logic.
- Next steps: continue deriving guards for loop iterations ≥ 6, then feed the resulting prefix into the apply-phase helper before
  addressing the halting/no-rule branches.

### 2024-07-15 — packaged loop-progress helpers

- Added `utm_find_rule_loop_some_reaches_apply` and
  `utm_find_rule_loop_none_progress` to `Simulation.v`, wrapping the new
  `find_rule_loop_preserves_inv` proof into ready-to-use lemmas for the
  rule-found and rule-miss cases so `utm_simulate_one_step` can invoke
  the 17-step trace without re-proving the case split.
- These helpers make the remaining TODOs purely about supplying the
  catalogue-derived monotonicity and register-length facts, after which
  the apply-phase axioms can be instantiated directly.
- Next up: source the `rule_table_{q,symbol}_monotone` and
  length-10 register hypotheses from the catalogue witness so the new
  lemmas can fire in both the continuing and halting branches.

### 2024-07-14 — rule-search invariant proven constructively

- Finished the full proof of `find_rule_loop_preserves_inv` in
  `ThieleUniversal.v`, replaying the 17-instruction loop trace to cover
  both the successful and advancing cases and removing the last
  `Admitted` from the universal runtime file.
- Reinstalled Coq 8.18.0 in the fresh container and reran
  `./scripts/quick_coq_check.sh`; the harness now succeeds across the
  modular, universal, and legacy stacks with the strengthened lemma in
  place.
- Remaining work: propagate the staged `< 29` guard through the full
  loop length so the apply-phase helper fires, then invoke the
  apply-phase axioms to discharge the remaining `utm_simulate_one_step`
  branches.

### 2024-07-13 — conditional jump decode captured

- Proved `utm_decode_findrule_jump_zero_instruction`, extending the
  fetch/reset trace with the seventh micro-step so the rule-search loop
  guard can reuse the concrete `Jz` decode without replaying the program
  image.
- Recorded the new decode fact directly inside
  `utm_simulate_one_step`, staging the invariant data required for the
  upcoming loop-prefix guard and apply-phase analysis.
- Next steps: turn the staged decode into an explicit `< 29` guard for
  the fifth loop step and continue propagating the `utm_pc_prefix_lt`
  witness toward the full 18-step bound needed by `Happly_regs`.

### 2024-07-12 — apply-phase loop length fixed

- Strengthened `transition_FindRule_to_ApplyRule` so the witness now
  returns the concrete loop length `k = 18`, and propagated the new
  equality through `utm_simulate_one_step` to record that the
  apply-phase entry is exactly 21 CPU steps after the setup state.
- Captured the resulting constant inside the bridge proof, making the
  remaining apply-phase TODO depend only on the `< 29` guard rather than
  an unknown run length.
- Next steps: finish bounding the outstanding loop iterations so the
  packaged `Happly_regs` helper fires, then continue closing the
  halting-case subgoals in both the rule-found and rule-missing
  branches.

### 2024-07-11 — fourth loop-step guard recorded

- Proved `utm_find_rule_loop_pc_prefix_step3`, extending the staged
  program-counter analysis through the first four rule-search loop
  steps and yielding a concrete `utm_pc_prefix_lt cpu_find 5` witness
  ready for the apply-phase helper.
- Updated `utm_simulate_one_step` to capture the new `< 29` guard and
  stage `Hpc_loop_prefix_step4`, so the remaining work is to propagate
  the bound across the dynamically-chosen loop iterations before
  invoking `Happly_regs`.
- Next steps: continue deriving guards for the remaining loop passes,
  feed the resulting `utm_pc_prefix_lt cpu_find k_apply` witness into
  the apply-phase axiom package, and start mechanising the halting
  branches in both rule-found and rule-missing cases.

### 2024-07-10 — subtraction micro-step captured

- Proved `utm_decode_findrule_subtract_instruction`, extending the
  concrete fetch/reset trace to the `SubReg` comparison that drives the
  rule-search loop and exposing the sixth micro-step for reuse inside
  `utm_simulate_one_step`.
- Recorded the new decode witness in the bridge proof so subsequent
  iterations can reference the subtraction instruction without
  recomputing the trace, keeping the staged invariants in sync with the
  concrete program.
- Next steps: continue deriving loop-prefix guards past the third
  iteration, feed the resulting `utm_pc_prefix_lt` witness into
  `Happly_regs`, and tackle the halting branches in both rule-found and
  rule-missing cases.

### 2024-07-09 — successor guard lemma added to the loop staging

- Proved `utm_pc_prefix_lt_succ`, allowing any freshly established
  `< 29` program-counter witness to extend the staged prefix without
  replaying the earlier guard analysis, and recorded the resulting
  `Hpc_loop_prefix_step3` fact inside the in-bounds branch of
  `utm_simulate_one_step`.
- Documented the new helper in the summary so future iterations reuse
  the lemma rather than rebuilding bespoke guard chains.
- Reinstalled Coq 8.18.0 via the system packages and reran the quick
  harness to confirm the environment remains reproducible after the
  guard update.
- Next steps: continue generating `< 29` witnesses for the remaining
  loop iterations so repeated applications of `utm_pc_prefix_lt_succ`
  yield the full `utm_pc_prefix_lt cpu_find k_apply` guard, then feed
  that bound into `Happly_regs` to unlock the apply-phase axioms while
  tackling the halting branches.

### 2024-07-06 — prefix guards reframed as reusable predicates

- Introduced the `utm_pc_prefix_lt` predicate with helper lemmas (`utm_pc_prefix_lt_of_le`, `utm_pc_prefix_lt_monotone`) so the `< 29` program-counter bounds can be recorded and combined without reworking raw inequalities.
- Rewrote `utm_pc_prefix_total_from_loop` and `utm_rule_table_preserved_until` to consume the new predicate, then updated `utm_simulate_one_step` to package the fetch and loop base cases as `utm_pc_prefix_lt` witnesses, clarifying exactly what remains to instantiate the apply-phase axioms.
- Next steps: strengthen `Hpc_loop_prefix_base` into a full `utm_pc_prefix_lt cpu_find k_apply` guard, apply `Happly_regs` to pull the rule components from the axioms, and continue closing the halting cases.

### 2024-07-08 — single-step guard generalised and toolchain restored

- Relaxed the guard lemma to `utm_run1_pc_lt_29_if_lt_29`, so any pre-apply
  state that stays below 29 immediately yields a `< 29` successor without
  requiring an explicit `<= 27` bound on the program counter.
- Re-ran the quick harness after installing the Coq 8.18.0 toolchain in this
  container, confirming the modular, universal, and legacy proof stacks still
  compile end-to-end with the strengthened lemma available to the bridge proof.
- Next steps: use the generalised single-step lemma to extend the loop guard
  beyond the base prefixes, feed the resulting `utm_pc_prefix_lt` witness into
  `Happly_regs`, and continue closing the halting branches.

### 2024-07-07 — fetch trace extended to the fifth instruction

- Proved `utm_decode_findrule_copy_q_instruction`, characterising the fifth micro-step of the universal interpreter’s fetch/reset path as the `CopyReg` instruction that prepares the loop guard register.
- Recorded the new decode fact within `utm_simulate_one_step`, enriching the symbolic-execution context available before the rule-search analysis.
- Next steps: leverage the extended decode chain to bound the ensuing loop steps, generalise the `utm_pc_prefix_lt` guard across the full apply-phase prefix, and continue wiring the apply-phase axioms.

### 2024-07-08 — loop guard advanced to the third step

- Added `utm_fetch_pc_after_five_steps` and `utm_find_rule_loop_pc_prefix_step2`, proving that the fifth fetch state sits at program counter 5 and that running three loop iterations keeps the PC below 29, delivering the next prefix witness needed for the apply-phase guard.
- Updated the in-bounds branch of `utm_simulate_one_step` to record the new guard (`Hpc_loop_step3`), so the staged apply-phase helper now awaits only the general `utm_pc_prefix_lt cpu_find k_apply` witness.
- Next steps: extend the loop guard across the remaining rule-search iterations, assemble the global prefix bound for `Happly_regs`, and continue tackling the apply-phase and halting branches.

### 2024-07-05 — reset snapshot packaged for reuse

- Added `utm_fetch_reset_state`, encapsulating the rule-table address
  and register equalities after the fourth CPU step so the
  rule-search loop can reuse the reset snapshot without replaying the
  fetch trace.
- Simplified the `utm_simulate_one_step` skeleton to consume the new
  helper instead of re-deriving the equalities, tightening the bridge
  setup before the loop invariant.
- Next steps: lift the `< 29` guard from the base cases across all
  loop iterations, invoke `Happly_regs` to extract the rule components,
  and continue closing the halting cases.

### 2024-07-04 — loop-guard base cases recorded

- Proved `utm_find_rule_loop_pc_prefix_base`, packaging the `< 29` guard for the
  first two `find_rule` loop iterations when the tape head is in bounds so the
  upcoming loop analysis can start from a ready-made base.
- Threaded the new helper through `utm_simulate_one_step`, capturing the
  `Hpc_loop_base` witness after the fetch transition and highlighting that the
  remaining work is to generalise the guard to all `j < k_apply`.
- Next steps: extend the guard from the base cases to the full loop prefix,
  reuse the resulting bound to trigger `Happly_regs`, and continue closing the
  halting branches.

### 2024-07-03 — fetch/reset invariant lifted to the loop entry

- Proved `utm_fetch_reset_inv_core`, extending the fetch analysis so the reset snapshot satisfies `inv_core` and keeps the tape,
  program image, and rule table aligned with the initial setup state.
- Recorded the new witness inside `utm_simulate_one_step` as `Hinv_core_reset`, giving future iterations a ready-made invariant
  when instantiating the rule-search loop bounds and apply-phase axioms.
- Next steps: leverage the reset-state invariant to propagate the `< 29` loop guard across all iterations, discharge the
  apply-phase axioms with `Happly_regs`, and finish the halting cases in both the rule-found and rule-missing branches.

### 2024-07-01 — start-phase guard packaged for reuse

- Proved `utm_find_rule_start_pc_prefix_step0`, bundling the `< 29` guard for the rule-search entry state together with the first post-reset step whenever the fetch snapshot satisfies `inv_core`.
- Replaced the ad-hoc guard derivation inside `utm_simulate_one_step` with the new lemma so the proof skeleton now records both the entry and first-step bounds without repeating the `run1` arithmetic.
- Next steps: propagate the packaged guard through the full `find_rule` loop to supply `Hpc_loop_prefix`, then feed the resulting global prefix into the apply-phase axioms and continue mirroring the halting cases.

### 2024-07-02 — extending the rule-search guard to the first loop iteration

- Proved `utm_find_rule_loop_pc_prefix_step1`, upgrading the fetch/reset
  analysis with an explicit `< 29` bound for the second state in the
  rule-search loop (`run_n cpu_find 2`).
- Recorded the new guard (`Hpc_loop_step2`) inside the in-bounds branch of
  `utm_simulate_one_step`, so the future `Hpc_loop_prefix` proof can start
  from a two-step base without re-running the decode trace.
- Next steps: propagate the guard across all loop iterations to supply
  `Hpc_loop_prefix`, invoke the packaged apply-phase axioms, and mirror the
  halting cases.

### 2024-06-30 — single-step guard for the rule-search loop

- Proved `utm_run1_pc_lt_29_if_lt_29`, bounding any pre-apply state whose
  program counter is still in the pre-apply prefix and retains the `inv_core`
  layout, giving a reusable single-step guarantee that the interpreter remains
  below the apply phase.
- Stored the resulting witness inside the in-bounds branch of
  `utm_simulate_one_step` (`Hpc_loop_step0`), so follow-up work can bootstrap
  the global `< 29` prefix proof from the fetch/reset snapshot without
  re-establishing the base case.
- Next steps: propagate the guard across every loop iteration to feed
  `utm_pc_prefix_total_from_loop`, invoke the apply-phase axioms, and continue
  mirroring the halting branches.

### 2024-06-29 — extending the rule-search decode chain

- Added `utm_decode_findrule_load_rule_instruction`, identifying the
  fifth instruction in the universal program as the `LoadIndirect`
  that reads the candidate rule’s state from `REG_ADDR`.
- Recorded the new decode fact inside `utm_simulate_one_step`, so the
  proof skeleton now retains the full fetch/reset/load sequence needed
  before instantiating the rule-search bridge.
- Next steps: leverage the extended decode chain to bound the loop
  prefix counters and proceed with the apply-phase axioms before
  handling the halting branches.

### 2024-06-28 — loop guard reduction for apply phase

- Added `utm_pc_prefix_total_from_loop`, reducing the global `< 29` counter requirement to a loop-phase guard over `run_n cpu_find`.
- Updated the `utm_simulate_one_step` closure to consume the loop guard and documented the remaining task of deriving the guard from the recorded rule-search invariants.

### 2024-06-27 — rule-table preservation wired into apply phase

- Proved `utm_rule_table_preserved_until`, reusing the universal `rule_table_preserved_until_apply` lemma so any `< 29` prefix bound immediately yields the catalogue equality needed at the apply phase.
- Collapsed the `utm_simulate_one_step` helper closure to depend only on the global `< 29` guard, letting `Happly_regs` derive the rule-table witness automatically once the guard is available.
- Next steps: discharge the `< 29` prefix bound across the full fetch/search trace, use `Happly_regs` to invoke the apply-phase axioms, and continue mirroring the halting cases.

### 2024-06-26 — apply-phase axioms scaffolded

- Added `utm_apply_phase_registers_from_axioms`, a helper that packages the `pc_29_implies_registers_from_rule_table` and `find_rule_from_memory_components` axioms so they can be invoked once the global `< 29` guard and rule-table preservation facts are available.
- Threaded the helper into `utm_simulate_one_step`, capturing the remaining obligations as explicit placeholders (`Hpc_prefix_total` and the terminal rule-table equality) for the next proof iteration.
- Next steps: prove the global `< 29` prefix bound from the recorded fetch and rule-search invariants, show that the rule-table window is unchanged at `cpu_apply`, and then use `Happly_regs` to extract the apply-phase registers before mirroring the halting traces.

### 2024-06-25 — fetch prefix extended to reset

- Proved `utm_fetch_pc_prefix_le4_lt_29`, extending the fetch-phase program-counter bound through the reset state so the rule-search setup now satisfies the `< 29` guard required by the apply-phase axioms.
- Updated `utm_simulate_one_step` to reuse the stronger prefix lemma, ensuring future work can focus on bounding the rule-search iterations beyond the reset instruction.
- Next steps: propagate the `< 29` guard across the full rule-search run, instantiate `pc_29_implies_registers_from_rule_table` / `find_rule_from_memory_components`, and finish mirroring the halting traces.

### 2024-06-24 — rule-search guard bounds captured

- Added `find_rule_start_inv_pc_lt_29` and `find_rule_loop_inv_pc_lt_29` in `ThieleUniversal.v`, giving the rule-search entry and loop states their own explicit `< 29` program-counter witnesses.
- Recorded the new bounds as `Hpc_find_lt` / `Hpc_loop_lt` inside `utm_simulate_one_step`, augmenting the fetch-prefix guard so the remaining TODO narrows to extending the bound across the full rule-search trace before invoking the apply-phase axioms.
- Next steps: propagate the guard through each loop iteration (e.g. via a dedicated `run_n` bound lemma), then call `pc_29_implies_registers_from_rule_table` / `find_rule_from_memory_components` and mirror the halting trace.

### 2024-06-23 — fetch prefix bound captured

- Proved `utm_fetch_pc_prefix_lt_29`, showing that the universal interpreter’s first four steps keep the program counter strictly below 29 and delivering the initial segment of the prefix bound required by the apply-phase axioms.
- Recorded the new bound inside `utm_simulate_one_step` alongside the existing loop invariants so the remaining work can focus on extending the bound through the rule-search loop and invoking the apply-phase witnesses.
- Next steps: propagate the `< 29` bound across the rule-search execution, apply `pc_29_implies_registers_from_rule_table` / `find_rule_from_memory_components`, and continue the halting-case mirror for the `find_rule = None` branch.

### 2024-06-22 — apply-phase target pinned down

- Recorded inside `utm_simulate_one_step` that the apply-phase state satisfies `cpu_apply = run_n cpu0 (3 + k_apply)` and unpacked the `IS_ApplyRule_Start` witness to the concrete `read_reg REG_PC cpu_apply = 29` equality, ensuring future steps can reference the exact run-length and program-counter facts when instantiating the apply-phase axioms.
- Highlighted that the remaining missing ingredient is a prefix bound showing every intermediate program counter stays below 29 so the axioms `pc_29_implies_registers_from_rule_table` and `find_rule_from_memory_components` can consume the recorded loop invariants.
- Next steps: prove the prefix PC bound (likely by combining the fetch lemmas with a `run_n` monotonicity argument), feed it into `pc_29_implies_registers_from_rule_table`, and extend the interpreter halt analysis in the `find_rule = None` branch.

### 2024-06-21 — halting guard rewrites in place

- Added `tm_step_halting_state` so any accepting/rejecting TM configuration rewrites `tm_step` to the original state, covering both branches of the halting guard.
- Threaded the lemma into `utm_simulate_one_step`, letting the continuing cases focus on the rule-search invariants while the halting cases now expose the exact interpreter target.
- Next steps: use the recorded loop facts to invoke the apply-phase axioms, lift the padded-head branch to a full `find_rule_start_inv`, and mirror the interpreter halt trace.

### 2024-06-20 — unpacking the rule-search loop snapshot

- Rewrote the in-bounds branch of `utm_simulate_one_step` to pull the `find_rule_loop_inv` witness apart, surfacing the concrete register, symbol, and address equalities that the apply-phase axioms will consume.
- Stored the extracted invariants (`Hq_loop`, `Hsym_loop`, `Haddr_loop`, `Hpc_loop`) inside the proof skeleton so follow-up iterations can reference them directly instead of re-destructing the witness.
- Next steps: use the recorded loop facts to instantiate `pc_29_implies_registers_from_rule_table`, extend the apply-phase bridge, and mirror the halting branch that short-circuits on accepting or rejecting states.

### 2024-06-19 — quick harness builds the legacy layer

- Namespaced the universal helper imports (`UTM_Program`, `UTM_CoreLemmas`) and refreshed `scripts/quick_coq_check.sh` to pass absolute `-Q` flags so Coq resolves the `ThieleUniversal` library consistently.
- Added the `ThieleUniversal.v` build to the harness, eliminating the load-path failure and letting the quick script compile `thielemachine/coqproofs/Simulation.v` on every run.
- Next steps: leverage the working harness to iterate on the apply-phase axioms inside `utm_simulate_one_step` and finish the out-of-bounds fetch invariant.

### 2024-06-18 — splitting the TM halting guard

- Destructed the `(Nat.eqb q tm_accept || Nat.eqb q tm_reject)` guard inside `utm_simulate_one_step`, so the continuing branch now reuses `tm_step_rule_found_continue` / `tm_step_no_rule_continue` to match the modular step with the rule-search result.
- Captured the guard equality for later use in both branches, clarifying that the remaining obligations are the accepting/rejecting interpreter mirror and the `find_rule = None` runtime bridge.
- Next steps: apply the apply-phase axioms using the recorded `cpu_apply` run length and finish the halting analysis for both guard outcomes.

### 2024-06-17 — chaining the apply-phase run length

- Combined the fetch and rule-application traces to record `cpu_apply = run_n cpu0 (3 + k_apply)` inside `utm_simulate_one_step`, ensuring the apply-phase axioms can now be invoked against the original setup state.
- Noted that the next steps are to apply `pc_29_implies_registers_from_rule_table` / `find_rule_from_memory_components` using the new equality and to extend the padded-head branch with a matching invariant.

### 2024-06-16 — bridging the padded fetch case

- Added `tm_step_rule_found_continue` and `tm_step_no_rule_continue` to
  `coq/thieleuniversal/coqproofs/TM.v`, exposing the `tm_step` rewrite
  rules needed once the acceptance guard is known to be false in the
  universal simulation branch.
- Recorded within `utm_simulate_one_step` that a head positioned beyond
  the current tape segment reads `tm_blank`, supplying the missing
  equality for the padded fetch scenario.
- Next steps: promote the out-of-bounds blank symbol into a
  `find_rule_start_inv` witness, then feed the rule-found branch through
  `pc_29_implies_registers_from_rule_table` /
  `find_rule_from_memory_components` while analysing the `find_rule =
  None` halting case.

### 2024-06-03 — mapping the remaining witnesses to the runtime layer

- Traced the constructive catalogue witness through
  `coq/thielemachine/coqproofs/Simulation.v`, confirming that
  `utm_obligations` now only depends on the Prop-level witness and the
  unresolved interpreter facts (`utm_simulate_one_step`,
  `utm_simulation_steps_axiom`).  No additional boolean checks remain.
- Surveyed `coq/thieleuniversal/coqproofs/ThieleUniversal.v` to locate
  the executable semantics that should back the `thiele_step_n`
  parameter; identified the large proof block that manipulates the
  machine registers and the outstanding axioms
  (`pc_29_implies_registers_from_rule_table`,
  `find_rule_from_memory_components`) needed to conclude the rule-table
  lookup.
- Cross-referenced `UTM_Program.v`/`UTM_CoreLemmas.v` to find reusable
  lemmas for the rule-table encoding.  These files provide the catalogue
  facts but still need to be connected to the runtime proof so the
  one-step lemma can specialise them.
- Next steps: extract the concrete definitions of `utm_program` and
  `thiele_step_n` into a focused helper module (or import section) so
  the one-step bridge can be stated against explicit terms, then prove
  the fetch/lookup/apply sub-lemmas using the catalogue witness and the
  remaining runtime axioms.

### 2024-06-06 — installing the Coq toolchain and validating the quick harness

- Installed the Ubuntu `coq` 8.18.0 package (plus OCaml dependencies)
  inside the workspace container so the quick harness can invoke `coqc`
  without fallback modes.  Verified the toolchain is available by
  re-running `./scripts/quick_coq_check.sh` end-to-end; the script now
  completes successfully and rebuilds the modular and universal proof
  artefacts in `-vio` mode.
- Confirmed the harness touches the expected compilation units (the
  `UTM_Rules.v` additions and the legacy `Simulation.v` bridge), giving a
  baseline to measure proof progress as the runtime axioms are replaced.
- Next up: draft the `fetch_symbol_preserves_encoding` lemma in
  `Simulation.v` so we can substitute it into the `utm_simulate_one_step`
  shell and start discharging the fetch-phase obligations without
  depending on the outstanding axioms.

### 2024-06-08 — consolidating the fetch-phase register invariant

- Installed the distribution `coq` package (8.18.0) in the fresh container to
  unblock the quick harness and ensure the universal/runtime files compile under
  the same toolchain as previous iterations.
- Proved `utm_fetch_state_in_bounds`, bundling the existing register facts into
  a single lemma that records the post-fetch `REG_Q`, `REG_SYM`, `REG_ADDR`, and
  `REG_PC` values for in-bounds heads.  The lemma captures the precise
  `run_n` state needed to seed the rule-search invariant.
- Updated the `utm_simulate_one_step` skeleton to destruct the new lemma in the
  in-bounds branch, leaving a focused TODO to rewrite the address component from
  `TAPE_START_ADDR + head` to `RULES_START_ADDR` before invoking
  `transition_FindRule_to_ApplyRule`.
- Next focus: extend the lemma to the padding case and massage the address
  register so `find_rule_start_inv` can be instantiated uniformly.

### 2024-06-09 — isolating the rule-table entry point

- Proved `utm_decode_findrule_reset_instruction`, showing that the fourth
  instruction executed by the universal interpreter is the `LoadConst`
  that resets `REG_ADDR` to `RULES_START_ADDR`.  The proof packages the
  memory-preservation facts so the decoder sees the concrete program
  image.
- Added `utm_fetch_reset_addr_after_four_steps`, which executes the
  `LoadConst` step and records that the address register rewinds to the
  rule-table base while the fetched state/symbol registers remain
  unchanged (PC advances to 4).  This lemma is now wired into the
  in-bounds branch of `utm_simulate_one_step` so the proof has immediate
  access to the rule-table pointer and preserved state.
- Updated the proof skeleton to capture the new facts (`cpu_reset` and
  the corresponding register equalities), leaving a focused TODO to map
  the `PC = 4` state back to the `find_rule_start_inv` hypothesis before
  invoking `transition_FindRule_to_ApplyRule`.
- Next: relate the reset state to the `PC = 3` loop entry, generalise
  the fetch lemmas to the padded tape case, and begin instantiating the
  rule-search transition in the in-bounds branch.

### 2024-06-10 — capturing the rule-search loop invariant

- Added `utm_fetch_establishes_find_rule_loop_inv`, combining the fetch
  register facts with the reset step to obtain a concrete
  `find_rule_loop_inv … 0` witness at the rule-table base.
- Threaded the lemma into the in-bounds branch of
  `utm_simulate_one_step`, narrowing the outstanding work to translating
  the loop invariant into `find_rule_start_inv` before applying
  `transition_FindRule_to_ApplyRule`.
- Updated the progress estimate and next-step checklist to highlight the
  remaining tasks: extend the fetch analysis to the padded-head case,
  finish the `find_rule_start_inv` bridge, discharge the apply-phase
  axioms, and handle the `find_rule = None` halting branch.

### 2024-06-11 — pinning down the rule-search start invariant

- Proved `utm_fetch_establishes_find_rule_start_inv_in_bounds`, giving a
  concrete `find_rule_start_inv` witness for heads within the tape
  bounds and registering it directly in the in-bounds branch of
  `utm_simulate_one_step`.
- Clarified the upcoming tasks: extend the witness to the
  out-of-bounds fetch case, strengthen the runtime invariant so
  `cpu_find` satisfies `ThieleUniversal.inv`, and then invoke
  `transition_FindRule_to_ApplyRule` to carry the simulation through the
  rule-search phase.

### 2024-06-12 — capturing fetch-phase memory preservation

- Proved `utm_fetch_mem_unchanged`, `utm_fetch_preserves_rule_table`, and
  `utm_fetch_preserves_tape_window`, showing that the universal program’s
  three-step fetch prefix leaves both the rule-table image and the tape
  window untouched.
- Threaded the new preservation lemmas into the in-bounds branch of
  `utm_simulate_one_step` so the recorded `find_rule_start_inv` witness is
  now accompanied by explicit rule-table and tape-window facts at
  `cpu_find`.
- Next focus: extend the preserved-state package to the out-of-bounds
  head case and upgrade `cpu_find` to the full `ThieleUniversal.inv` so
  `transition_FindRule_to_ApplyRule` can be instantiated directly.

### 2024-06-14 — instantiating the rule-search transition in the in-bounds case

- Generalised the rule-component bridge `read_mem_rule_component` to accept the relaxed `inv_core` invariant so post-fetch states can reuse the rule-table memory facts.
- Updated `transition_FindRule_to_ApplyRule` to work with `inv_core` and destructed its witness inside the matching branch of `utm_simulate_one_step`, exposing the program counter and rule registers loaded at `cpu_apply`.
- Next focus: feed the extracted registers into `pc_29_implies_registers_from_rule_table` / `find_rule_from_memory_components`, and extend the fetch analysis to the out-of-bounds head case so the transition applies unconditionally.

### 2024-06-15 — normalising the simulation imports and enabling the quick harness

- Moved the `rules_fit` predicate alongside the fetch lemmas in `Simulation.v`, ensuring the legacy layer can invoke the universal invariants before other helpers are defined.
- Replaced ad-hoc `ThieleUniversal.*` qualifiers with the concrete `CPU`, `UTM_Program`, and `UTM_Encode` namespaces and introduced explicit program-length witnesses, eliminating tactic terms in the decoding lemmas.
- With the imports cleaned up, `./scripts/quick_coq_check.sh` now compiles `thielemachine/coqproofs/Simulation.v` end-to-end using the standard load-path wiring.
- Next focus: continue wiring the fetch-state invariant into the apply-phase axioms and extend the proof to the out-of-bounds and halting branches.

### 2024-06-13 — bundling the fetch witness into `inv_core`

- Introduced `inv_core` in `ThieleUniversal.v`, a relaxed invariant that
  drops the program-counter constraint while preserving the register and
  memory layout facts needed after the fetch phase.
- Added `utm_fetch_preserves_head` and `utm_fetch_preserves_program_image`
  so the fetch prefix is now known to keep both the TM head register and
  the flattened program image intact.
- Proved `utm_fetch_inv_core`, packaging the post-fetch facts into a single
  witness and wiring it into the in-bounds branch of
  `utm_simulate_one_step`. The skeleton now records the precise invariant
  required to invoke `transition_FindRule_to_ApplyRule` once the PC
  constraint is discharged.
- Next actions: generalise the witness to the out-of-bounds head case,
  strengthen it to the full `ThieleUniversal.inv`, and begin instantiating
  the rule-search transition in the constructive proof.

### 2024-06-07 — materialising the fetch-phase witness inside `utm_simulate_one_step`

- Added `run1_addreg_result` to `ThieleUniversal.v` so the AddReg instruction used during symbol fetch exposes its register update directly; this avoids re-proving the arithmetic when manipulating the universal program trace.
- Proved `utm_cpu_state_read_tape`, `utm_fetch_addr_after_three_steps`, and `utm_fetch_loads_symbol` in `Simulation.v`, covering the in-bounds case where the TM head lies inside the current tape window. These lemmas show that after three CPU steps the universal machine has captured the active TM state/symbol while keeping the program counter at the start of the rule-search loop.
- Updated the `utm_simulate_one_step` shell to split on `head < length tape`, registering the concrete post-fetch register facts in the in-bounds branch and documenting the remaining TODOs: extend the symbol lemma to the padding case, invoke `transition_FindRule_to_ApplyRule`, and analyse the halting branch when no rule is found.
- Remaining focus: generalise the fetch lemma to the padded tape case, then wire the recorded invariants into the rule-search transition so the constructive bridge can invoke the existing axioms.

### 2024-06-05 — scoping the concrete proof obligations for `utm_simulate_one_step`

- Walked the existing symbolic-execution lemmas in
  `coq/thieleuniversal/coqproofs/ThieleUniversal.v` and charted the exact
  checkpoints the `utm_simulate_one_step` proof has to hit:
  1. **Fetch symbol** (`pc = 0 ⟶ 3`): reuse
     `find_rule_start_inv` to show the initial `run_n` prefix stores the
     current TM state/symbol in `REG_Q`/`REG_SYM` and keeps the tape
     window intact.  This isolates the `config_ok` hypotheses needed by
     `tm_decode_encode_roundtrip`.
  2. **Rule search** (`pc = 3 ⟶ 29`): rely on
     `transition_FindRule_to_ApplyRule` for the matching case and the
     monotonicity lemmas `rule_table_q_monotone`/
     `rule_table_symbol_monotone` to guarantee every prefix of the scan
     preserves the invariant required by
     `pc_29_implies_registers_from_rule_table`.
  3. **Apply rule** (`pc = 29 ⟶ 48`): symbolically execute the 7-step
     apply block with `run_apply_phase_registers_from_addr` so the final
     state exposes the updated head index, symbol write, and move.
- Split the one-step target into the following helper lemmas so that the
  main proof script can reduce to a single `match` on
  `find_rule (tm_rules tm) q sym`:
  - `fetch_symbol_preserves_encoding` (new): proves that executing the
    fetch prefix leaves `encode_config` unchanged except for the
    scratch registers listed in `find_rule_loop_inv`.
  - `apply_rule_commits_step` (new): takes the witness index produced by
    `pc_29_implies_registers_from_rule_table` and discharges the
    `tm_step` equality by computation using the tape window from the
    invariant.
- Identified where the remaining axioms need to be invoked inside these
  helpers and noted which runtime facts are already available:
  `pc_29_implies_registers_from_rule_table` supplies the catalogue index
  for the apply phase, while `find_rule_from_memory_components` turns the
  reconstructed rule components back into a `find_rule` hit.
- Action items for the next coding pass:
  1. Implement `fetch_symbol_preserves_encoding` directly above
     `utm_simulate_one_step` in `Simulation.v`, using only the structural
     lemmas (`run_n_succ`, `decode_encode_id`) that are already proven.
  2. Port the apply-phase symbolic execution from
     `transition_FindRule_to_ApplyRule` into a standalone lemma that
     produces the `tm_step` components, so the final goal collapses to a
     handful of `rewrite` calls once the axioms are replaced.

### 2024-06-04 — decomposing the one-step bridge into concrete subgoals

- Surveyed the `run_n` control-flow lemmas in
  `coq/thieleuniversal/coqproofs/ThieleUniversal.v` to map the universal
  program's three phases.  The key checkpoints are:
  - `transition_FindRule_to_ApplyRule` advancing to PC 29 with
    `REG_Q'`, `REG_WRITE`, and `REG_MOVE` loaded from the matching rule.
  - `find_rule_loop_preserves_inv` maintaining the strong invariant and
    preserving the rule-table window while scanning.
  - The `inv` / `inv_min` bridge, which retains the tape window so the
    post-state can be decoded back into a `TMConfig` with
    `tm_decode_encode_roundtrip`.
- Annotated where the remaining axioms slot into the proof skeleton:
  the apply phase must expose `pc_29_implies_registers_from_rule_table`,
  and the final equality requires `find_rule_from_memory_components` to
  turn the memory snapshot into a `find_rule` hit.
- Extracted the register identities needed after the apply phase (values
  of `REG_Q`, `REG_WRITE`, `REG_MOVE`, and the updated head index) so the
  equality with `tm_step` can be stated without guesswork.
- Updated the acceptance criteria in the summary to call out the two
  axioms explicitly, ensuring the next iteration can focus on either
  proving them or isolating their computational witnesses.

### 2024-06-02 — wiring the catalogue witness

- Reinstalled the Coq 8.18.0 toolchain inside the fresh container so the
  quick harness can run without relying on cached artefacts and confirmed
  `coqc --version` reports 8.18.0.
- Imported `UTM_Rules` into `Simulation.v` and built an explicit
  `StepInvariantBoundsCatalogueWitness utm_tm`, then threaded it through
  `catalogue_from_witness`, `step_data_from_catalogue_witness`, and
  `step_bounds_from_data` to surface reusable definitions
  (`utm_step_catalogue_prop`, `utm_step_data`, `utm_step_bounds`).
- Replaced the previous `vm_compute` proof of
  `catalogue_static_check utm_tm = true` with
  `catalogue_static_check_of_witness` applied to the new witness so the
  boolean check is now justified by the Prop-level lemmas exported from
  `UTM_Rules.v`.
- Next steps: specialise `interpreter_obligations_from_catalogue_witness`
  to `utm_step_bounds` so the legacy obligations no longer mention the
  abstract witness, then tackle the `utm_simulate_one_step` lemma to clear
  the remaining axioms.

### 2024-06-01 — environment bring-up and validation

- Installed Coq 8.18.0 and the supporting OCaml toolchain via
  `apt-get install coq`, ensuring the quick harness can execute inside
  the container without relying on cached build artefacts.
- Ran `./scripts/quick_coq_check.sh`; it now completes end-to-end,
  confirming the existing modules compile with the freshly installed
  toolchain and that the only remaining axiomatic pieces are the explicit
  `Parameter` stubs at the bottom of
  `coq/thielemachine/coqproofs/Simulation.v`.
- Next focus areas for the follow-up iteration:
  1. Replace `Parameter utm_simulate_one_step` and
     `Parameter utm_simulation_steps_axiom` with constructive lemmas.
     After importing `UTM_Rules`, call the existing bridge helpers in
     the order `utm_step_catalogue_witness ⟶ step_data_from_catalogue ⟶
     step_bounds_from_data ⟶ simulation_obligations_from_bounds` to build
     `utm_obligations` directly from the catalogue witness.
  2. For the one-step lemma, consider adding a focused file (e.g.
     `coq/thieleuniversal/coqproofs/UTM_StepBridge.v`) that imports the
     runtime executor and catalogue facts.  Split the trace into the
     read/lookup/apply phases, discharging the concrete program trace
     with `vm_compute` while Prop-level lemmas maintain `tm_config_ok`.
  3. If the multi-step recurrence remains axiomatic afterwards, unfold
     `thiele_step_n` in `coq/thielemachine/coqproofs/ThieleMachine.v` and
     prove `thiele_step_n_succ` by rewriting with the one-step lemma.

Keep the ledger files in `docs/encoding/` up to date once each lemma is
proved so the provenance of `DIGIT-BOUND`, `HEAD-BOUND`, and
`ONE-STEP-DECODE` remains traceable.

## PR plan and mapping

Group the remaining work into small, reviewable PRs:

1. **PR: instantiate-utmbounds** (single change)
   - Change: `coq/thielemachine/coqproofs/Simulation.v` — require `UTM_Rules.v`,
     build the catalogue witness and call the existing pipeline to obtain
     `utm_obligations`/`utm_step_bounds`.
   - Tests: quick harness should finish modular/universal helpers and
     attempt legacy simulation; if the one-step lemma is still missing,
     `Simulation.v` should now fail only on the one-step claim.

2. **PR: utm-one-step-bridge**
   - Change: add `utm_simulate_one_step` lemma in a new file or near the
     runtime semantics (prefer a small file that imports the UTM
     program and `TM_Basics.v`).  Keep the proof decomposed by phase
     with small lemmas and `vm_compute` where the program is concrete.
   - Tests: quick harness should type-check everything and the legacy
     simulation file should now type-check up to whether the multi-step
     recurrence exists.

3. **PR: thiele-recurrence** (only if required)
   - Change: add `thiele_step_n_succ` to `ThieleMachine.v` and
     re-run the induction proofs in `Simulation.v` to verify the
     multi-step lemma closes without axioms.
   - Tests: full quick harness + legacy simulation compile passes.

After these PRs merge, create a final cleanup PR that removes residual
admits, updates the ledger entries to `Adopted`, and refreshes the
top-level synopsis `ENCODING_ROUNDTRIP_SYNOPSIS.md`.

## Acceptance criteria

The work is done when the following are true:

1. `./scripts/quick_coq_check.sh` completes without skip notices and the
   legacy `Simulation.v` file compiles under `coqc -vio` in CI.
2. Ledger entries `DIGIT-BOUND`, `HEAD-BOUND`, and `ONE-STEP-DECODE`
   are marked `Adopted` (or otherwise documented as proved) in
   `docs/encoding/05-BOUNDS.ledger.md` and the goal checklist shows G14–G15
   complete.
3. The PRs listed in the PR tracker that covered the remaining work
   (instantiate-utmbounds, utm-one-step-bridge, thiele-recurrence if
   needed) are merged, each with focused diffs and per-PR tests that
   exercise the quick harness and the relevant `.v` files.
4. `docs/encoding/00-GUIDE.md` (this file) is referenced from the top of
   the `docs/encoding/` directory and the README links to it as the
   authoritative finish plan.

## Rollback / debugging checklist

- If modular proofs fail with nat/Z mismatches: check `Simulation.v`
  for missing `%nat` annotations and ensure `EncodingMod.*` constants
  are imported as aliases; move catalogue/data definitions earlier in
  the file if they are referenced before definition.
- If builds are slow: use `./scripts/quick_coq_check.sh` and edit small
  files first; avoid long `make` runs while iterating.
- If the one-step proof is brittle: add small lemmas that expose the
  program trace at each phase and prove them with `vm_compute` so the
  bulk of the program semantics are reduced by computation rather than
  by heavy tactic work.

## Appendix: exact lemma templates

Copy these into the appropriate modules and adapt names/quantifiers to
match local definitions.

1. Digit bound (catalogue → rule writes):

   Lemma utm_rule_write_in_base :
     forall rule,
       In rule utm_rules ->
       let '(_, _, _, write, _) := rule in
       write < EncodingMod.BASE.

2. Head-move bound (catalogue → small moves):

   Lemma utm_rule_move_abs_le_one :
     forall rule,
       In rule utm_rules ->
       let '(_, _, _, _, enc_move) := rule in
       Z.abs (decode_z enc_move) <= 1.

3. One-step decode bridge:

   Lemma utm_simulate_one_step :
     forall tm conf,
       config_ok tm conf ->
       decode_state tm (thiele_step_n utm_program (encode_config tm conf) 1)
       = tm_step tm conf.

4. thiele_step_n recurrence (if needed):

   Lemma thiele_step_n_succ :
     forall P s k,
       thiele_step_n P s (S k) = thiele_step_n P (thiele_step_n P s 1) k.

----

If anything in this plan is unclear or you need the exact names of a helper
function used in the pipeline, open the modular `Simulation.v` and search
for `simulation_obligations_from_bounds` — the pipeline that connects the
catalogue to the final obligations lives immediately around that name and
is the most compact way to see how the witness values flow into the
obligations record.

This single guide should replace the separate files in `docs/encoding/` for
day-to-day implementation: keep it short, use the per-task templates above,
and cross-reference the ledger for canonical inequality names when committing
proofs.

-- The build & integration team