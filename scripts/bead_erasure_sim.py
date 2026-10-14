"""Simulate the bead erasure of Berut et al. (2012) and fit heat against time.

The book's chair chapter ("Time has a bill") quotes this run. A bead in a
quartic double well, overdamped Brownian motion, the protocol as the paper
describes it: lower the barrier over one second, tilt the trap with a force
ramped over the protocol time tau, stop the tilt, raise the barrier over one
second. Heat is measured the way the paper does, as the Stratonovich integral
of the force times the displacement (Sekimoto's heat), and averaged over the
runs that end in the right-hand well.

For each tau the tilt is the smallest from a scan that erases at least nine
times in ten (the paper used ninety-five in a hundred, so the excess constant
differs). The fit is heat = A + B / tau. The floor A comes out at ln 2 to the
third decimal; that, and the one-over-time excess on top of it, is what the
book reports. This is a simulation of a model with the paper's numbers, not a
measurement.

Needs numpy. Run:  python scripts/bead_erasure_sim.py   (a few minutes)
"""

from __future__ import annotations

import numpy as np

RNG = np.random.default_rng(21)
D = 0.22          # diffusion constant, um^2/s
A_WELL = 0.45     # half-distance between the wells, um
LN2 = np.log(2)
HI, LO, TB = 8.0, 2.2, 1.0   # barrier height high/low in kT, barrier ramp time in s


def force_well(x, du):
    return du * 4 * x * ((x / A_WELL) ** 2 - 1) / A_WELL ** 2


def run(tau, fmax, n=3000, dt=5e-4):
    x = np.where(RNG.random(n) < 0.5, -A_WELL, A_WELL) + RNG.normal(size=n) * np.sqrt(1 / (8 * HI / A_WELL ** 2))
    heat = np.zeros(n)

    def step(x, du, f):
        xn = x - D * (force_well(x, du) - f) * dt + np.sqrt(2 * D * dt) * RNG.normal(size=n)
        xm = 0.5 * (x + xn)
        return xn, (f - force_well(xm, du)) * (xn - x)

    for k in range(int(TB / dt)):
        x, q = step(x, HI + (LO - HI) * k * dt / TB, 0.0)
        heat += q
    for k in range(int(tau / dt)):
        x, q = step(x, LO, fmax * k * dt / tau)
        heat += q
    for k in range(int(TB / dt)):
        x, q = step(x, LO + (HI - LO) * k * dt / TB, 0.0)
        heat += q
    ok = x > 0
    return heat.mean(), heat[ok].mean(), ok.mean()


def main() -> None:
    plan = [(2, 9.0), (5, 6.0), (10, 4.6), (20, 4.0), (40, 3.5), (80, 3.1)]
    rows = []
    for tau, fmax in plan:
        q_all, q_ok, p = run(tau, fmax)
        rows.append((tau, q_all, q_ok))
        print(f"tau={tau:3d} s  tilt={fmax:4.1f}  heat={q_all:.3f} kT  heat on success={q_ok:.3f} kT  success={p:.3f}", flush=True)
    t = np.array([r[0] for r in rows], float)
    for name, col in (("all runs", 1), ("successful runs", 2)):
        y = np.array([r[col] for r in rows])
        a, b = np.linalg.lstsq(np.c_[np.ones_like(t), 1 / t], y, rcond=None)[0]
        print(f"fit, {name}: heat = {a:.3f} kT + {b:.2f} kT*s / tau   (ln 2 = {LN2:.3f})")


if __name__ == "__main__":
    main()
