# Encoding round-trip — single finish guide

Last updated: 2025-12-11

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
  - The quick-build harness `scripts/quick_coq_check.sh` and modern
    `coqc` flags are in place so experiments iterate quickly.

- What remains (concrete):
  1. Instantiate the universal interpreter bounds witness from the
     formal rule table (`UTM_Rules.v`) so the legacy `utm_step_bounds`
     / `utm_obligations` become constructive.  (DIGIT-BOUND, HEAD-BOUND)
  2. Prove the one-step decode bridge that equates
     `thiele_step_n utm_program … 1` with the modular `tm_step`.
     (ONE-STEP-DECODE)
  3. If the multi-step recurrence for `thiele_step_n` is missing in the
     runtime semantics, add the recurrence lemma so the inductive
     multi-step simulation proof closes without an axiom. (THIELE-RECURRENCE)

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
