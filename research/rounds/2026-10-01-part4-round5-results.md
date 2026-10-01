# Part 4, Round 5 results: two-state calorimeter protocol

Date: 2026-10-01

| Statement | Outcome |
|---|---|
| canonical master-equation reset | PROVED |
| exact fixed-Hamiltonian heat `Delta / 2` | PROVED |
| selected Landauer gap gives `k_B T ln 2` | PROVED BUT BUILT IN |
| unconditional one-mu Landauer floor from the master equation | REFUTED |

The microscopic register has a ground state of energy zero and an excited
state of energy `Delta`. Its initial excited-state population is one half and
its final population is zero. With unit time step, zero excitation rate, and
unit relaxation rate, the population update satisfies the frozen discrete
master equation exactly. At fixed Hamiltonian the bath receives the lost mean
register energy, exactly `Delta / 2`.

Selecting `Delta = 2 k_B T ln 2` therefore yields exactly
`Q_bath = k_B T ln 2`. That equality is a valid protocol specialization, not a
derivation of the Hamiltonian scale. With the same distributions, rates,
master equation, and one-unit logical ledger change, selecting
`Delta = k_B T ln 2` yields half the Landauer value. The closed theorem
`master_equation_does_not_fix_heat_scale` also exhibits gaps one and two with
identical population dynamics and different exact heat.

The smaller-gap step has zero reverse rate. It is an irreversible abstract
master step, not by itself a finite-temperature detailed-balance realization.
Ruling it out requires a thermal admissibility premise such as local detailed
balance and the second law, or evidence from the physical device. Those are
exactly the premises already exposed by `LandauerJoules.v`; the master equation
does not manufacture them.

## Experimental contract

A laboratory implementation can instantiate the formal variables by:

1. identifying the two register microstates and measuring their Hamiltonian
   energy gap spectroscopically;
2. preparing a statistically tested half-excited initial ensemble;
3. estimating forward and reverse rates and checking the master-equation
   residual for the stated time interval;
4. measuring the final excited-state population and bath heat independently;
5. checking the fixed-Hamiltonian energy balance against `Delta (p-p')`; and
6. separately testing thermal detailed balance and controller, work-source,
   and retained-history energy flows before applying a Landauer interpretation.

This is an executable symbolic blueprint for a calorimeter test. It is not a
measurement, and it does not convert the abstract VM ledger into joules without
the device correspondence.

## Hollowness checks

- Definitional: the master update and heat are explicit equations. Their
  algebraic evaluation is intentionally exact bookkeeping, not a new physical
  law.
- Built in: the Landauer equality is obtained by selecting the gap that makes
  it hold and is labeled PROVED BUT BUILT IN. The unconditional claim is
  refuted rather than inferred from that selection.
- Vacuity: the canonical populations and rates are concrete; their master
  equation computes to zero final excited population.
- Swap: changing only `Delta` leaves the population dynamics unchanged and
  changes the heat, which is the formal scale-undertermination witness.
- Adversarial read: the result is a two-state discrete master-equation
  protocol. It is not a continuous-time solution, a detailed-balance proof,
  or an experimental result.

The acceptance test was observed failing before the proof file existed. All
theorems compile. Real-number theorems inherit only Coq's standard real-number
axiom families and no project-local assumptions.
