> **ARCHIVAL NOTICE:** This document is preserved for historical context. The final, unified proof and analysis are now complete. For the authoritative summary, see `README.md` and `docs/final_fact_check.md`.

# Encoding Round-Trip Status Report

> **Status update (October 2025):** This document is preserved for historical context. For the current analysis of the kernel, μ-spec v2.0, and reproducible evidence see `docs/kernel_analysis.md` and `docs/final_fact_check.md`.

## Background

The lemmas `encode_decode_list_with_len` and `encode_decode_config` in
[`coq/modular_proofs/Encoding.v`](../coq/modular_proofs/Encoding.v)
ensure that the numerical encodings of tape contents and full Turing
machine configurations are left-inverses of their decoders.  They are
the last blockers for replacing the simulation axiom
`encode_decode_roundtrip` with a constructive proof in
[`coq/modular_proofs/Simulation.v`](../coq/modular_proofs/Simulation.v).

The packing scheme is fixed as follows:

- Digits are encoded in base `BASE = 2` via `encode_list`.
- Pairs are packed with `pair_small_encode len code = len * SHIFT_SMALL + code`,
  where `SHIFT_SMALL = BASE^SHIFT_LEN` and `SHIFT_LEN = 5` in the
  current development.
- Configurations are packed with `triple_encode`, nesting an additional
  multiplication by `SHIFT_BIG = BASE^(2 * SHIFT_LEN) = SHIFT_SMALL^2`.

The previous iteration uncovered a counterexample showing that the old
hypotheses were inconsistent: without a bound on `length tape`, the
packed triple can overflow and lose information during decoding.  Coq
rightly refused to accept the original statements.

## Updated invariant and helper library (2025-10-18)

The obstruction is removed by strengthening the lemmas so they *derive*
the required small-slot bounds from the tape length, rather than
assuming them outright.  A new helper module
[`coq/modular_proofs/EncodingBounds.v`](../coq/modular_proofs/EncodingBounds.v)
collects the reusable inequalities:

- `POW2-GT-SUCC`, `LEN-LT-SMALL`, and `CODE-LT-SMALL` formalise the
  exponential growth of `BASE^n`, ensuring that `length tape ≤ SHIFT_LEN`
  implies both `length tape < SHIFT_SMALL` and `encode_list tape < SHIFT_SMALL`.
- `PAIR-FITS-BIG` and `DIV-MUL-ADD` provide the strict packing bounds and
  quotient/remainder equalities needed by the pair and triple round-trip
  proofs.
- `SHIFT_BIG_as_product` and `POS-BIG` (proved in `Encoding.v`) bridge the
  helper bounds to the existing `SHIFT_BIG` definition.

With these helpers in scope, both pending lemmas are now proved:

- `encode_decode_list_with_len` assumes only the digit predicate and the
  length bound.  It derives the numeric bound via `CODE-LT-SMALL`, applies
  `pair_small_roundtrip`, and finishes with `encode_list_decode_aux`.
- `encode_decode_config` adds the head bound, uses `PAIR-FITS-BIG` plus
  `SHIFT_BIG_as_product` to show the nested pair stays under `SHIFT_BIG`,
  and then combines `triple_roundtrip`, `pair_small_roundtrip`, and
  `encode_list_decode_aux` to reconstruct the configuration.

The documentation lane reflects this progress:

- Bounds ledger entries `LEN-LT-SMALL`, `CODE-LT-SMALL`, `PAIR-FITS-BIG`,
  and `DIV-MUL-ADD` are marked **Adopted**.
- Goal G9 in `docs/encoding/02-GOALS.todo.md` is checked off, and new goal
  G11 tracks the follow-up work in `Simulation.v`.
- Worksheets G9/G9b capture the final proof scripts and the arithmetic
  adjustments required during promotion to the helper module.

## Implications for `decode_encode_id`

The remaining engineering work lies outside `Encoding.v`.  Any caller of
`encode_config`/`decode_config` must now supply the strengthened
invariant `length tape ≤ SHIFT_LEN` alongside the digit predicate.  Once
`Simulation.v` threads this invariant through its reachable-state
predicates, the constructive round-trip lemmas can replace the existing
axiom.

## Lean arithmetic clean-up (2025-10-19)

The structural lemma `encode_list_decode_aux` previously relied on a
sequence of legacy rewrites (`Nat.add_mod`, `Nat.div_mul`, etc.).  The
proof now uses a single invocation of `div_mul_add_small`, backed by the
base-positivity fact recorded as `POS-BASE`.  This removes the dependency
on deprecated hints, shortens the script, and keeps the round-trip
pipeline consistent with the shared helper style introduced in
`EncodingBounds.v`.

## Linear triple round-trip rewrite (2025-10-22)

To remove the last vestiges of ad-hoc arithmetic reasoning, `Encoding.v`
now aliases the canonical base positivity lemma and rewrites
`triple_roundtrip` to destruct `div_mul_add_small` exactly once per
division.  The proof no longer introduces temporary names via `set`/`replace`;
instead the destructed equalities rewrite the nested `let` bindings
directly.  `encode_list_decode_aux` reuses the same alias so both proofs
share the helper uniformly, keeping the round-trip witnesses compact and
easy to audit.

## Single-source SHIFT bounds (2025-10-20)

`Encoding.v` no longer re-proves local witnesses for `SHIFT_SMALL` and
`SHIFT_BIG`.  The file now imports the canonical equalities and
positivity facts directly from `EncodingBounds.v`, so both round-trip
proofs share a single arithmetic backbone.  This reduces duplication,
simplifies future refactors of the packing bounds, and keeps the
documentation ledger aligned with the actual Coq sources.

## Bundled slot bounds (2025-10-21)

The helper module now exports `encode_list_len_code_small` and
`encode_list_pack_lt_SHIFT_BIG`, consolidating the length and code bounds
required by the round-trip proofs.  `Encoding.v` consumes these helpers
to derive all small-slot and packed bounds with one instantiation each,
eliminating redundant `pose proof` calls and reducing proof search.  The
ledger entries `LEN-CODE-SMALL` and `PACK-LT-BIG` capture these bundled
facts.

## Aggregate list bounds (2025-10-21)

`EncodingBounds.v` now also provides `encode_list_all_bounds`, packaging
the small-slot bounds together with the packed big-slot inequality.
`Encoding.v` destructs this triple conjunction once per lemma, removing
the final duplicated proof plumbing and keeping the scripts linear in
the number of helper calls.  Ledger entry `LEN-CODE-PACK` documents the
aggregate statement for future reuse.

## With-length helper (2025-10-23)

To eliminate the remaining boilerplate, `Encoding.v` now exposes
`encode_list_with_len_all_bounds`, a thin wrapper around the aggregate
helper that rewrites the packed inequality into the exact
`encode_list_with_len` form consumed by both round-trip lemmas.  Each
proof destructs the helper once to obtain the small-slot bounds and the
packed `< SHIFT_BIG` witness, keeping the scripts linear and avoiding
redundant unfolding.  Ledger entry `WITH-LEN-BOUNDS` tracks the new
statement, and the worksheets/logs capture the refactor for future
audits.

## Record-based bounds helper (2025-10-24)

The aggregate inequalities are now available via the record constructor
`encode_list_bounds_of`, which packages the small-slot and packed bounds
behind projections.  `Encoding.v` and the sandbox reuse the projections
directly, avoiding nested pattern matches and keeping each round-trip
proof to a single `pose proof`.  Ledger entry `BOUNDS-RECORD` documents
the helper, and the analytics dashboards include the new trends sheet to
highlight the zero remaining helper backlog before tackling
`Simulation.v`.

## Single-destruct bounds unpack (2025-10-25)

To avoid repeated projection lookups, both the sandbox and
`EncodingBounds.v` now expose `encode_list_bounds_unpack`.  The lemma
destructs an `encode_list_bounds` witness into the length, code, and
packed inequalities in one step, which `Encoding.v` applies directly in
`encode_decode_list_with_len` and `encode_decode_config`.  This keeps the
proofs linear, removes auxiliary `pose proof` calls, and records the
pattern in the bounds ledger as `BOUNDS-UNPACK` so future arithmetic
refactors can rely on the same single-destruct interface.

## Direct record destruct (2025-10-26)

The round-trip lemmas now destruct the `encode_list_bounds_of` witness
inline, eliminating the extra call to `encode_list_bounds_unpack`.
`EncodingBounds.v` mirrors this change so both the helper lemma and the
main proofs reuse the record fields directly.  The shift trims an extra
layer of helper indirection, keeps each proof to a single pattern match,
and ensures the analytics lane records G10i as the iteration that fully
inlined the record destruct pattern.

## Retired unpack helper (2025-10-30)

With the record destruct pattern entrenched across the helpers and main
proofs, the auxiliary lemma `encode_list_bounds_unpack` has been removed
from both the sandbox and shared helper modules.  The bounds ledger now
marks `BOUNDS-UNPACK` as **Retired**, keeping the exported helper surface
focused on the record constructor alone.  The documentation lane (goals
checklist, worksheets, analytics dashboards) logs G10l as the iteration
that completed the cleanup, reducing the maintenance burden for future
packing tweaks.

## Horner orientation for `encode_list` (2025-10-27)

The recursive case of `encode_list` now follows the Horner pattern
`encode_list xs * BASE + x`.  With this orientation the pair round-trip
lemma can apply `div_mul_add_small` immediately, eliminating the extra
commutativity rewrites previously required to massage the goal.  The
upper-bound lemma has been rewritten to compare `(encode_list xs + 1) *
BASE` against the target power, keeping the proof linear while relying on
`Nat.lt_succ_r` for the growth step.  The bounds ledger records the
definition tweak as `ENCODE-HORNER`, and the analytics dashboard tracks
G10j as the iteration that aligned the arithmetic helpers with the
encoding recursion.

## TM configuration bridge (2025-10-28)

The modular round-trip lemmas now lift directly to universal Turing
machine configurations.  The helper file
[`coq/thielemachine/coqproofs/EncodingBridge.v`](../coq/thielemachine/coqproofs/EncodingBridge.v)
introduces wrappers `tm_encode_config`/`tm_decode_config` that reuse the
modular encoders while keeping the configuration invariant explicit via
`tm_config_ok`.  The new lemma `tm_decode_encode_roundtrip` destructs a
`TMConfig` and applies `encode_decode_config`, providing a ready-made
bridge for the simulation development once it starts threading the
length/head bounds through reachable states.  The bounds ledger records
this witness as `TM-ROUNDTRIP`, and the analytics dashboards mark G10k as
the final pre-Simulation milestone.

## Modular Simulation round-trip (2025-10-29)

`coq/modular_proofs/Simulation.v` now consumes the invariant directly.
The wrappers `encode_tm_config`/`decode_tm_config` are rewritten with
tuple pattern matching so the nested `TMConfig` pairs align with the
encoding helpers, and a new predicate `tm_config_ok` mirrors the length,
digit, and head bounds.  The previous axiom `encode_decode_roundtrip` has
been replaced with a lemma that destructs the configuration, applies
`encode_decode_config`, and rebuilds the state.  Quick `coqc -quick`
builds confirm the proof stays lightweight.  With G12 complete, the
legacy `Simulation.v` module now imports the bridge helpers, threads
`tm_config_ok` through `SimulationWitness`, and proves `decode_encode_id`
via `tm_decode_encode_roundtrip`; the analytics dashboards record zero
remaining round-trip milestones and shift focus to the remaining
simulation axioms such as `utm_simulation_steps`.

## Lean div/mod helper and analytics dashboard (2025-10-12)

The shared helper `div_mul_add_small` has been rewritten to lean on the
standard library equalities `Nat.div_add_l` and `Nat.Div0.mod_add`,
eliminating the custom `Nat.div_mod`/`Nat.add_cancel` reasoning.  The
proof now mirrors the arithmetic algebra used elsewhere in the project
and keeps the helper short enough for fast `coqc -quick` rebuilds.

To track progress toward removing `decode_encode_id`, the new
`docs/encoding/07-GOAL-ANALYTICS.md` sheet captures the end goal, current
metrics (micro-goals closed, helpers adopted, docs published), and the
delta-to-target for each iteration.  This dashboard will be updated with
every pass so reviewers can immediately see how close the encoding lane
is to completion.

## Preservation factoring for simulation obligations (2025-11-05)

To prepare for instantiating the modular simulation obligations, the
helper library now includes:

- `replace_nth_Forall`, a structural lemma in `TM_Basics.v` that preserves
  `Forall` predicates across `replace_nth` updates.
- `StepInvariantAssumptions`, a record capturing the per-step digit and
  head bounds that the universal interpreter must satisfy.
- `step_assumptions_preserve_ok`, a lemma showing that any inhabitant of
  `StepInvariantAssumptions` preserves `tm_config_ok` via `replace_nth_Forall`
  and the existing tape-length helper.
- `simulation_obligations_of`, a constructor that pairs the preservation
  lemma with the caller-provided progress equality to obtain a
`SimulationObligations` witness.

*2025-11-07 update:* `tm_config_ok_change_state`, `tm_config_ok_update_write`,
and `tm_config_ok_update_head` factor the invariant rewrites used in
`step_assumptions_preserve_ok`.  These helpers eliminate manual tuple
destructs and make the preservation proof compositional once the
interpreter-specific `StepInvariantAssumptions` record is in scope.  The
ledger records them as `CFG-STATE`, `CFG-WRITE`, and `CFG-HEAD`.

*2025-11-10 update:* Introduced `StepInvariantBounds`, a record that packages
the digit/head witnesses and feeds directly into
`StepInvariantAssumptions`.  The modular definition of `tm_step_assumptions`
now derives from this constructor, so the universal interpreter only needs to
prove the two bounds once before the preservation lemma applies.

*2025-11-11 update:* Introduced `simulation_obligations_from_bounds` and
`simulate_one_step_decode_from_bounds`/`tm_run_n_preserves_ok_from_bounds` so
the packaged bounds witness feeds directly into the modular obligations.  The
ledger records this as `SIM-OBLIGATIONS-FROM-BOUNDS`, and the analytics lane now
tracks helper coverage alongside the interpreter blockers.

*2025-11-12 update:* Attempted to reuse the packaged bounds inside the legacy
simulation layer (goal G14c2); blocked because the universal interpreter still
exposes only the axiomatic witnesses `utm_step_preserves_ok` and
`utm_simulate_one_step`, with no digit/head lemmas or recurrence for
`thiele_step_n`.  Logged the gap across the goal checklist, worksheets,
attempts log, ledger, blocker reference, and analytics dashboards so future
iterations can focus on proving the missing witnesses.

*2025-11-18 update:* Refactored `coq/thielemachine/coqproofs/Simulation.v` to consume the packaged witness `StepInvariantBoundsTM` via `bounds_preserve_ok`.  The legacy preservation parameter is now `utm_step_bounds`, so the remaining work on G14 concentrates on extracting the UTM digit/head lemmas rather than restructuring the proof.

*2025-11-22 update:* Proved `tm_step_digits_from_rule_bounds`, reducing the digit component of `utm_step_bounds` to the blank symbol bound and per-rule write inequalities catalogued in `docs/encoding/15-UTM-BOUNDS-CATALOG.md`.
*2025-11-23 update:* Added `move_abs_le_one_to_nat`, `tm_step_head_le_succ`, and `tm_step_head_within_big_from_moves`, so the head component of `utm_step_bounds` now follows from the rule-table move bound (`Z.abs move ≤ 1`) and the documented safety margin (`S head < SHIFT_BIG`).
*2025-11-24 update:* Proved `tm_step_length_from_head_bound`, introduced `StepInvariantBoundsData`, and derived `utm_step_bounds` via `step_bounds_from_data`; preservation now reduces to instantiating the catalogued digit/head inequalities in the `utm_step_data` witness.
*2025-11-25 update:* Added `StepInvariantBoundsCatalogue`, `find_rule_in`, and `find_rule_forall`, so the preservation assumption now reduces to the boolean checklist + head-margin axioms (`utm_catalogue_static_check`, `utm_head_lt_shift_len`), which `catalogue_static_check_witness` packages into the catalogue witness aligned with the UTM bounds cheat sheet.
*2025-11-26 update:* Introduced `interpreter_obligations_from_catalogue`, allowing the catalogue witness to compose directly into `utm_obligations` via the existing data/bounds bridges.

The documentation lane (goal checklist G13d, worksheets, attempts log,
ledger entry `STEP-ASSUME→OK`, and analytics dashboards) now tracks this
helper, leaving only the interpreter-specific instantiation of the record
fields for milestones G14–G15.

## Next steps

1. Scope the constructive replacement of `utm_simulation_steps` so both
   modular and legacy simulation layers are axiom-free on the round-trip
   boundary.
2. Add a regression script that rebuilds the modular encoding and
   simulation targets to catch arithmetic regressions early.
3. Once the simulation axioms are retired, rerun the proof suite to
   confirm the helpers compose at scale.

## Multi-step simulation skeleton (2025-11-01)

`utm_simulation_steps` no longer appears as an axiom in
`coq/modular_proofs/Simulation.v`.  The lemma now follows from two
one-step obligations:

1. `tm_step_preserves_ok` — the universal interpreter must preserve the
   strengthened `tm_config_ok` invariant after each simulated step.
2. `simulate_one_step` — a single universal interpreter step on the
   encoded configuration must equal the encoding of the TM step.

Given these assumptions, the proof proceeds by induction on the step
count, reusing the new helper lemmas `simulate_one_step_decode` and
`tm_run_n_preserves_ok`.  The ledger entries `RUN-OK` and
`SIM-STEP-DECODE` track the proven pieces, while `STEP-OK` highlights
the remaining assumption to mechanise inside the universal interpreter.
The next iteration will focus on discharging G14–G15 so the multi-step
simulation lemma is fully constructive end-to-end.

## Legacy obligations mirror (2025-11-03)

The legacy containment file now exposes an `InterpreterObligations` record mirroring the modular structure.
Projecting from `utm_obligations` replaces the monolithic `utm_simulation_steps` axiom with three explicit fields:
`tm_step_preserves_ok`, `simulate_one_step`, and `utm_simulation_steps`.
Documentation artefacts (goal checklist, worksheets, analytics) point G14–G15 directly at the preservation and progress fields,
so instantiating the record collapses the remaining assumptions uniformly across both modular and legacy layers.

## Explicit obligation split (2025-11-06)

The legacy witness now rebuilds `utm_obligations` from three standalone parameters
`utm_step_preserves_ok`, `utm_simulate_one_step`, and `utm_simulation_steps_axiom`.
This mirrors the modular record exactly and surfaces the two outstanding lemmas
required to mechanise the universal interpreter.  The checklist, worksheets, attempts
log, analytics dashboards, and PR tracker were updated to reflect the narrower scope—
G14 targets `utm_step_preserves_ok`, while G15 focuses on `utm_simulate_one_step`.
Although the proofs remain pending, future iterations can now address each obligation
in isolation without unravelling the packaging used by the containment witness.

## Quick-build unblocking (2025-11-04)

Moving the `utm_program`/`utm_program_blind` parameters above the new `InterpreterObligations` record removed the forward-reference
error that forced repeated recompilation of the legacy simulation file.
The quick-build command sequence (`coqc -quick … ThieleMachine.v`, `EncodingBounds.v`, `Encoding.v`, `EncodingBridge.v`, and `Simulation.v`)
now succeeds without manual clean steps, keeping each iteration under a couple of minutes while the remaining interpreter obligations (G14–G15)
are addressed.