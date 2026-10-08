# kernel/thermodynamic

A two-state calorimeter protocol: exact energy bookkeeping, and the boundary
of what population dynamics say about heat.

## Files

| File | Purpose |
|---|---|
| `CalorimeterProtocolTarget.v` | Definitions for the two-state calorimeter protocol |
| `CalorimeterProtocol.v` | A canonical reset satisfies a discrete master equation exactly and the bath receives `Delta / 2` (`canonical_reset_heat_exact`); gaps with identical dynamics give different heat (`master_equation_does_not_fix_heat_scale`); the reset's ledger change is one unit (`canonical_reset_is_one_mu`) |

## Load-bearing role

The protocol is a physical model with its own parameters. No state map
between it and any machine is claimed, and no machine ledger fixes its units.
Calibrating a ledger in joules needs thermal and device premises; the
top-level README's [Scope](../../../README.md#scope) table states the same.

## Imports

The Coq standard library (Reals).
