# Part 4, Round 5 freeze: two-state calorimeter protocol

Date: 2026-10-01

## Definitions

The microscopic register has two states, ground (`false`) and excited
(`true`). Its Hamiltonian assigns energy zero to ground and a real-valued gap
`Delta` to excited. A population is represented by the probability `p` of the
excited state.

For time step `dt`, excitation rate `k01`, and relaxation rate `k10`, the
discrete master equation is

```text
p' = p + dt * (k01 * (1 - p) - k10 * p).
```

At fixed Hamiltonian, heat delivered to the bath is the lost mean register
energy:

```text
Q_bath = Delta * (p - p').
```

The canonical exact reset uses `p = 1/2`, `p' = 0`, `dt = 1`, `k01 = 0`, and
`k10 = 1`. Its logical ledger change is one unit.

## Frozen statements

1. The canonical reset satisfies the discrete master equation.
2. Its exact heat is `Delta / 2`.
3. With `Delta = 2 * k_B * T * ln 2`, exact heat is
   `k_B * T * ln 2`.
4. For positive `k_B` and `T`, choosing
   `Delta = k_B * T * ln 2` makes the exact heat strictly less than
   `k_B * T * ln 2`. Therefore the master equation, Hamiltonian bookkeeping,
   and one-unit logical ledger change alone do not force the Landauer bound.

## Predicted outcomes

- Executable calorimeter blueprint: PROVED.
- Landauer-gap specialization: PROVED BUT BUILT IN, because the Hamiltonian
  gap is selected to make the equality hold.
- Unconditional one-mu physical calibration from the master equation:
  REFUTED by the smaller-gap protocol unless a thermal detailed-balance,
  second-law, or empirical device premise is added.

## Success

All four statements close in Coq with no project-local axioms; the report
distinguishes exact energy bookkeeping from thermodynamic admissibility and
gives an experimental measurement contract.

## Failure

The exact heat calculation does not close, the smaller-gap witness fails to
meet the same frozen master equation, or the report calls a selected
Hamiltonian scale a derived physical constant.
