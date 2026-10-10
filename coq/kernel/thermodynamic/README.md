# kernel/thermodynamic

A two-state calorimeter protocol: exact energy bookkeeping, the boundary of
what population dynamics say about heat, and a driven reset with rates in
detailed balance whose work comes to `kT ln 2`.

## Files

| File | Purpose |
|---|---|
| `CalorimeterProtocolTarget.v` | Definitions for the two-state calorimeter protocol |
| `CalorimeterProtocol.v` | A canonical reset satisfies a discrete master equation exactly and the bath receives `Delta / 2` (`canonical_reset_heat_exact`); gaps with identical dynamics give different heat (`master_equation_does_not_fix_heat_scale`); the reset's ledger change is one unit (`canonical_reset_is_one_mu`); the canonical rates are in detailed balance at no gap (`canonical_rates_break_detailed_balance`), so the canonical reset is a bookkeeping toy with no second law (`canonical_reset_heat_below_landauer_at_small_gap`); a driven reset with rates in detailed balance pays work within `kT exp (- D / kT)` below and `D / (2 N)` above `kT ln 2` (`driven_reset_work_window`) |

## Load-bearing role

The protocol is a physical model with its own parameters. No state map
between it and any machine is claimed, and no machine ledger fixes its units.
Calibrating a ledger in joules needs thermal and device premises; the
top-level README's [Scope](../../../README.md#scope) table states the same.

## Imports

The Coq standard library (Reals).
