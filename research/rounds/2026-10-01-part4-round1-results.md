# Part 4, round 1 results: pricing and physics

The operative target is round 4. Rounds 1 through 3 preserve two type-level
corrections and the rejected tautological 4.4 formulation.

| Item | Outcome | Exact result |
|---|---|---|
| 4.1 | PROVED BUT KNOWN | `no_forced_price_beyond_merges` proves that, under the frozen definition quantifying over every merge-pricing schedule, no injective instruction is forced to have positive price. |
| 4.2 | PARTIAL | `permanent_write_has_logical_payment` proves logical payment as a finite-state merge. Economic, cryptographic, and physical payment need separate bridges and are not proved universally. |
| 4.3 | PARTIAL | `mu_has_no_intrinsic_joule_value` exhibits two distinct external scales compatible with the bare natural-number ledger; `calibrated_mu_landauer_energy` gives `k_B T ln 2` for one unit only after that scale is selected. |
| 4.4 | PROVED BUT KNOWN | `permanence_heat_floor_uses_landauer` exposes the existing heat floor as a consequence of the named `landauer_heat` premise and the finite-state squeeze. No independent physical prediction was found in the current model. |

## Calls made

1. “Must be priced” in 4.1 means `forced_priced`: every natural-valued cost
   assignment satisfying `merging_steps_priced` charges the instruction at
   least one. With that exact quantifier, forced price is exactly
   non-injectivity. This is a characterization of the stated accounting class,
   not a claim that every physical implementation uses that class.
2. “Paid at some level” in 4.2 was not collapsed into a single predicate.
   The formal theorem closes the logical level. Money, cryptographic work, and
   heat are reported as unproved without explicit real-system bridges.
3. μ is the VM’s declared natural-number ledger. The formalization does not identify one μ with a measured number of joules. A Landauer reading selects
   the scale `k_B T ln 2` per bit removed, conditionally.
4. A checkable experiment would implement a finite memory whose record has no
   reachable revoking transition, prepare a stated input distribution, isolate
   the record-writing protocol, measure dissipated heat over repeated trials,
   and compare the measured average against
   `k_B T ln((m+k)/m)`. It must also account for controller and retained-history
   degrees of freedom. No device measurement was performed.
5. 4.4 is scoped to the current deterministic finite-state entropy model. It
   is not an impossibility theorem over every future physical theory.

## Literature check

Landauer’s 1961 paper already associates logically irreversible many-to-one
operations with heat generation (DOI `10.1147/rd.53.0183`). Sagawa and Ueda’s
2009 analysis shows that the energetic cost depends on the physical memory and
process, so logical reversibility and a unique physical cost cannot be equated
without further conditions (DOI `10.1103/PhysRevLett.102.250602`). Bérut et al.
experimentally tested the one-bit erasure bound in a colloidal memory (DOI
`10.1038/nature10872`). Consequently the thermodynamic formulas here are known;
the checked contribution is the conditional connection from a finite permanent
record write to a many-to-one transition.

## Hollowness checks

### 4.1

- Definitional: the result is a direct corollary of
  `forced_priced_iff_merges`; it is useful as the requested characterization
  but not a new substantive theorem.
- Built in: `forced_priced` quantifies only over schedules already required to
  price merges. The report states that restriction.
- Vacuity: the three-state `tri_step` is a concrete forced-priced merge, while
  the identity instruction is an injective unforced instruction.
- Swap test: the proof is polymorphic in state, instruction, and step, so it
  does not depend on the VM or certification names.
- Adversarial read: PASS. The sentence is limited to the frozen merge-pricing
  accounting class and makes no universal physical-pricing claim.

### 4.2

- Definitional: non-injectivity is derived by the finite pigeonhole argument;
  it is not a field of the permanence premise.
- Built in: no monetary, cryptographic, or heat price is encoded into
  `item42_logical_payment`.
- Vacuity: `quad_stamp` supplies a concrete finite permanent write.
- Swap test: the theorem is event-generic over every Boolean record reading.
- Adversarial read: PASS. “Logical payment” matches non-injectivity, and the
  unproved economic, cryptographic, and physical bridges remain excluded.

### 4.3

- Definitional: the two-scale witness is intentionally elementary. It records
  underdetermination, not a new physical law.
- Built in: the calibrated equality follows after choosing the Landauer scale;
  this is reported as conditional and not counted as a measured calibration.
- Vacuity: scales 1 and 2 are distinct concrete witnesses, and positive
  temperature gives a nonzero Landauer scale when the physical constants have
  their usual positive values.
- Swap test: replacing μ by any dimensionless natural ledger leaves the same
  scale ambiguity.
- Adversarial read: PASS. The report distinguishes scale underdetermination,
  conditional calibration, and actual measurement.

### 4.4

- Definitional: the rejected round-3 target merely unfolded the named premise
  and was hollow. Round 4 proves the full finite-state logarithmic heat floor
  through `permanent_flip_heat_floor` and separately proves entropy invariance
  under permutation of the state enumeration.
- Built in: heat is supplied through `landauer_heat`, never derived from the VM
  schedule.
- Vacuity: the quad stamp and uniform distribution satisfy the finite logical
  side; the physical premise remains an explicit conditional.
- Swap test: the heat wrapper is polymorphic over finite state spaces and event
  readings.
- Adversarial read: PASS. The sentence retains Landauer as an explicit premise
  and does not assert a universal impossibility theorem.

## TDD and proof status

The three Part 4 semantic tests were observed failing before the target, proof,
and report existed. After the preserved corrections and strengthened round 4,
the audit theorems compile. The first two are closed under the global context. The
real-number equalities and heat wrapper use only the Coq standard library’s
real-number and classical infrastructure; there are no project-local axioms.

Predictions were correct. No novelty claim is made.
