"""Phase 2 symbolic analysis of the +1 in triangle_angle's denominator.

triangle_angle s a b c
  = if dab=0 or dac=0 then 0
    else PI * dbc / (dab + dac + dbc + 1)

We separate the "+1" out and compute the correction term:
  delta(a,b,c) = triangle_angle_with_plus_one - triangle_angle_without_plus_one
              = PI * dbc / (D + 1) - PI * dbc / D,   D := dab + dac + dbc.

We then:
  (1) get the closed form for delta;
  (2) specialize to equilateral d_ab = d_ac = d_bc = d;
  (3) sum delta over a 2-cell at vertex m and check whether the sum is
      proportional to the number of 2-cells incident to m.
"""

import json
import sympy as sp


def main():
    PI = sp.pi
    dab, dac, dbc, d, T = sp.symbols("dab dac dbc d T", positive=True)

    angle_with_one = PI * dbc / (dab + dac + dbc + 1)
    angle_without_one = PI * dbc / (dab + dac + dbc)
    delta = sp.simplify(angle_with_one - angle_without_one)

    # Equilateral case: dab = dac = dbc = d
    delta_equilateral = sp.simplify(delta.subs({dab: d, dac: d, dbc: d}))

    # Sum over T equilateral 2-cells at vertex m, all with same d
    sum_over_T = sp.simplify(T * delta_equilateral)

    # Compare to "constant per 2-cell" structure: c * T for some constant c
    is_proportional_to_T = sp.simplify(sum_over_T / T) == sp.simplify(delta_equilateral)

    # Behavior as d -> infinity (does it vanish?)
    delta_eq_limit_inf = sp.limit(delta_equilateral, d, sp.oo)
    delta_eq_limit_zero = sp.limit(delta_equilateral, d, 0, "+")

    # Small-d behavior (d -> 0+) shows whether +1 is large at small mass
    # Mid behavior d=1
    delta_eq_d1 = sp.simplify(delta_equilateral.subs(d, 1))

    # Compare with what "irreducible 2-cell cost = constant unit per 2-cell" would
    # predict: if +1 were Landauer-style irreducible, delta would be a fixed
    # angle in [-PI, 0] independent of d. Test whether delta_equilateral is
    # constant in d.
    is_constant_in_d = sp.simplify(sp.diff(delta_equilateral, d)) == 0

    # Print structured findings
    findings = {
        "delta_general": str(sp.simplify(delta)),
        "delta_general_factored": str(sp.factor(delta)),
        "delta_equilateral": str(delta_equilateral),
        "delta_equilateral_limit_d_to_infinity": str(delta_eq_limit_inf),
        "delta_equilateral_limit_d_to_zero_plus": str(delta_eq_limit_zero),
        "delta_equilateral_at_d_1": str(delta_eq_d1),
        "delta_equilateral_is_constant_in_d": bool(is_constant_in_d),
        "sum_over_T_2cells": str(sum_over_T),
        "sum_proportional_to_T_count": bool(is_proportional_to_T),
        "interpretation": (
            "delta = -PI*dbc / [(D+1)*D] where D = dab+dac+dbc. "
            "Equilateral form: delta(d) = -PI / [3*(3d+1)] -> 0 as d -> infinity. "
            "delta is NOT constant in d, so the contribution per 2-cell scales "
            "as 1/d, not as a fixed irreducible unit. Sum over T 2-cells at "
            "vertex m is T * delta(d), which is proportional to T BUT only "
            "trivially so because we assumed uniform d; the per-2-cell "
            "contribution is d-dependent, not a fixed Landauer-style quantum."
        ),
    }
    print(json.dumps(findings, indent=2))


if __name__ == "__main__":
    main()
