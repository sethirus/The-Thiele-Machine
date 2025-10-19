# UTM Closure Summary — December 20, 2025

> **Status update (October 2025):** This document is preserved for historical context. For the current analysis of the kernel, μ-spec v2.0, and reproducible evidence see `docs/kernel_analysis.md` and `docs/final_fact_check.md`.

## Objective
Mechanise the remaining universal interpreter lemmas required to close
`utm_simulate_one_step` and `utm_simulation_steps` without appeals to
`Admitted` or abstract oracle hypotheses.

## Remaining Lemmas

1. **`utm_pc_prefix_full_apply`**
   *Goal:* Given the loop-start CPU state `cpu_find` and the program counter
   witness `utm_pc_prefix_total_from_loop`, produce a concrete
   `< 29` prefix certificate for all 18 apply-phase iterations.  The proof
   composes:
   - `utm_find_rule_start_pc_prefix_step0`
   - `utm_run1_preserves_program_image_before_apply`
   - The per-instruction `pc_lt_29` facts already exported from
     `ThieleUniversal.IS_ApplyRule_*`.
   *Status:* PC arithmetic dependencies catalogued.  Next action is to
   package the existing lemmas into a reusable step-indexed induction.

2. **`utm_fetch_symbol_oob_blank`**
   *Goal:* Extend the fetch-phase analysis to the window overrun case by
   evaluating the concrete `run_n` trace when `head >= length tape`.  Show
   that the decoder observes `tm_blank`, rebuild the rule-search invariant,
   and link it to the TM’s "no rule" path.
   - Requires the established length/digit bounds in
     `EncodingBounds.v`.
   - Re-uses `utm_fetch_reset_state` and `utm_fetch_inv_core`.
   *Status:* Trace outline captured; pending execution of the explicit
   `run_n` calculation.

3. **`utm_interpreter_halting_guard`**
   *Goal:* Bridge the halting guard by showing that when the TM state is
   accepting or rejecting, the interpreter exits immediately and decodes to
   the unchanged configuration.
   - Uses `tm_step_halting_state` for the TM semantics.
   - Previously targeted a direct `run_n` replay over PC 7/11; now the plan
     is to rephrase the argument inside the modular layer so the halting
     trace is witnessed by the lightweight `ThieleMachine` semantics rather
     than the full universal interpreter.
   *Status:* Guard PC addresses and register invariants logged.  New action
   is to package the halting guard as a modular lemma `thiele_halt_no_rule`
   that mirrors `tm_step_halting_state`, then instantiate the existing
   bridge in `utm_simulate_one_step` with that modular witness.  The
   low-level trace will only be revisited if additional register facts are
   required after the modular proof closes.

## Execution Order

1. Prove `utm_pc_prefix_full_apply` to unlock the apply-phase helper
   `utm_apply_phase_registers_from_axioms`.
2. With the loop invariant available, mechanise the halting guard via
   `utm_interpreter_halting_guard`.
3. Finish the out-of-bounds fetch case using
   `utm_fetch_symbol_oob_blank`, completing the non-halting branch.
4. Re-run `utm_simulate_one_step` and then generalise by induction to close
   `utm_simulation_steps`.

## Validation Checklist

- [ ] Coq `make` target `verify_subsumption` builds without `Admitted`.
- [ ] `utm_simulate_one_step` no longer references the abstract step
      oracle.
- [ ] Multi-step bridge derives directly from the proven one-step lemma.
- [ ] Documentation (this file and `docs/COMPLETION_PLAN.md`) reflects the
      final mechanised state.