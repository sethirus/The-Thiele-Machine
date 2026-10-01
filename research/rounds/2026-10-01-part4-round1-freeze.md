# Part 4, round 1 freeze: pricing and physics

Date: 2026-10-01

This round freezes the formal meanings before `PricingPhysicsAudit.v` exists.
The prose phrase “paid at some level” is split into a proved logical payment
(non-injectivity) and claims about economic, cryptographic, or physical payment,
which require an implementation-specific bridge and are not silently identified
with the VM ledger.

## Frozen inputs

- `part4-pricing-physics-target.v.sha256`:
  `946e6f36893d9b7b022d819cc8ac7f5b9c460127c76812931b8662cc90935f1b`
- `PermanentRecordPricing.v.sha256`:
  `efa6ffa69466e2a9c030484813e2a33679e8438bac05402af0da18a066137395`
- `PermanentCertificationEntropy.v.sha256`:
  `148d1ac4a4b4842f83c5b6dfe70061a77ce3fc09f2de3af16b0dfa244dfe1a3d`
- `BekensteinCalibration.v.sha256`:
  `9f45fb9bc1b3528790ace6aafffa43d8b5986902846e165e11cf93fc5e77aaa9`

## Exact statements and predicted outcomes

### 4.1

Exact statement: `item41_no_price_beyond_merges` in the frozen target.

Predicted outcome: PROVED BUT KNOWN, as a corollary of the existing
`forced_priced_iff_merges` characterization and elementary logic.

Success: a closed Coq proof. Failure: a finite deterministic instruction that
is injective yet forced positive by every merge-pricing schedule.

### 4.2

Exact formal statement: `item42_logical_payment` in the frozen target.
The broader claim that permanence is always paid economically,
cryptographically, or physically remains conditional on a named bridge.

Predicted outcome: PARTIAL. The logical merge is provable; no theorem is
predicted to turn it into actual money, cryptographic work, or heat without a
system-specific premise.

Success: close the logical theorem and identify every missing bridge. Failure:
a finite permanent write whose transition is injective.

### 4.3

Exact statements: `item43_no_intrinsic_joule_scale` and
`item43_landauer_calibration`.

Predicted outcome: PARTIAL. The ledger admits distinct external scales. Under
the explicit Landauer calibration, one unit is `k_B T ln 2` joules per bit of
entropy removed; the calibration is not derived from the VM schedule.

Success: closed proofs of both statements and a concrete measurement protocol.
Failure: a closed derivation of a unique joule scale from the VM ledger alone.

### 4.4

Exact statement: `item44_landauer_is_required`, together with a wrapper showing
that the existing permanent-flip heat floor consumes `landauer_heat` as a
premise.

Predicted outcome: PROVED BUT KNOWN within the current model: the heat floor is
a consequence of Landauer plus the finite-state squeeze and is not a new
physical prediction independent of Landauer.

Success: closed wrappers exposing that dependency. Failure: a heat conclusion
in the current model that can be derived without a thermodynamic premise.

## Literature baseline

- R. Landauer, “Irreversibility and Heat Generation in the Computing Process,”
  IBM Journal of Research and Development 5(3), 1961,
  DOI `10.1147/rd.53.0183`.
- T. Sagawa and M. Ueda, “Minimal Energy Cost for Thermodynamic Information
  Processing,” Physical Review Letters 102, 250602 (2009),
  DOI `10.1103/PhysRevLett.102.250602`.
- A. Bérut et al., “Experimental verification of Landauer’s principle linking
  information and thermodynamics,” Nature 483, 187–189 (2012),
  DOI `10.1038/nature10872`.

No novelty is predicted for the thermodynamic formulas.
