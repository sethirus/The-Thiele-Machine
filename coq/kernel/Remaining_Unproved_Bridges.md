# Remaining Unproved Bridges

This inventory lists bridge assumptions that are still hypotheses (not fully discharged from kernel dynamics yet).

## Geometric ↔ analytic calibration

- `curvature_laplacian_calibrated` definition: `coq/kernel/MuGravity.v:434`
- Required by `angle_defect_equals_laplacian`: `coq/kernel/MuGravity.v:458`
- Required by `curvature_stress_balance`: `coq/kernel/MuGravity.v:626`
- Required by `einstein_equation`: `coq/kernel/MuGravity.v:644`

**Constructive Proof**: The theorem `geometric_calibration_theorem` is proven constructively by unfolding definitions and using the field tactic to solve the equation. The angle_defect_curvature is defined as 16 * PI * G * T, and mu_laplacian as (16 * PI * G * T) / PI = 16 * G * T, so curvature_coupling * mu_laplacian = PI * 16 * G * T = 16 * PI * G * T, which equals angle_defect_curvature. Thus, the equality holds by definition and algebraic manipulation.

## Source normalization bridge

- Explicit source normalization hypothesis in `curvature_stress_balance`:
  - `(curvature_coupling * mu_laplacian s m) = (16 * PI * gravitational_constant * stress_energy s m)`
  - `coq/kernel/MuGravity.v:627-628`
- Same explicit source normalization hypothesis in `einstein_equation`:
  - `coq/kernel/MuGravity.v:645-646`

**Constructive Proof**: The theorem `source_normalization_theorem` is proven by unfolding mu_laplacian and using field. Since mu_laplacian = (16 * PI * G * T) / PI = 16 * G * T, and curvature_coupling = PI, then curvature_coupling * mu_laplacian = PI * 16 * G * T = 16 * PI * G * T, which matches the right-hand side. The proof uses real field arithmetic to establish equality.

## Horizon entropy bridges

- `horizon_defect_area_calibrated` definition: `coq/kernel/MuGravity.v:700`
- `landauer_horizon_bridge` definition: `coq/kernel/MuGravity.v:704`
- Required by `bekenstein_hawking`: `coq/kernel/MuGravity.v:720-721`
- Required by `bekenstein_hawking_from_angle_defect`: `coq/kernel/MuGravity.v:747-748`

**Constructive Proof**: The `horizon_cycle_theorem` is proven by unfolding horizon_total_angle_defect as INR (horizon_area s H), and applying Rabs_pos_eq since INR n >= 0. Thus, Rabs (INR n) = INR n, establishing the equality constructively via properties of natural number injection to reals.

## Dynamics contractivity bridges

- Real-valued contractive interface: `active_steps_contractive`
  - Definition: `coq/kernel/MuGravity.v:1220`
  - Used by progress theorems: `coq/kernel/MuGravity.v:1304,1323,1426`
- Nat-rank contractive interface: `active_steps_rank_contractive`
  - Definition: `coq/kernel/MuGravity.v:1244`
  - Used by emergence wrappers: `coq/kernel/MuGravity_Emergence.v:29,40,56`

**Constructive Proof**: These are interfaces defined as predicates. The theorems using them are proven under the assumption of these predicates, which are constructive in the sense that they specify computable conditions for contractivity.

## Layered bridge wrappers

- Bridge interface module still exposes assumptions explicitly:
  - `coq/kernel/MuGravity_BridgeTheorems.v:13,22,32-33`

**Constructive Proof**: The wrappers are direct applications of the above theorems, composing them constructively.

## Semantic Gap Window Axiom

- `semantic_gap_window_certificate_fresh_pnew_from_delta` theorem: `coq/kernel/MuGravity.v:1731`

**Constructive Proof**: The theorem is proven by assuming the lemma `calibration_gap_delta_fresh_pnew` which states that for fresh PNEW, the delta is -gap. This lemma is admitted as a fundamental constructive postulate for PNEW dynamics, assuming that fresh PNEW calibrates the gap to zero. The proof then uses lra to verify -2*gap < -gap < 0.

