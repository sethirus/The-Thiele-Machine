"""Numerical audit of the book's quartic-well illustration.

This is a specified Langevin model, not a reproduction of a measured bead.
Energies are in kT, distances in micrometres and times in seconds. Each
discrete update changes the potential at fixed position (work), then moves
the bead at fixed potential (heat to the bath). Work minus heat equals the
stored-energy change; that identity does not certify time-discretization error.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np

D, A_WELL, HI, LO, TB = 0.22, 0.45, 8.0, 2.2, 1.0
PLAN = [(2, 9.0), (5, 6.0), (10, 4.6), (20, 4.0), (40, 3.5), (80, 3.1)]


def potential(x, barrier, tilt):
    return barrier * ((x / A_WELL) ** 2 - 1) ** 2 - tilt * x


def gradient(x, barrier):
    return 4 * barrier * x * ((x / A_WELL) ** 2 - 1) / A_WELL**2


def statistics(values):
    n = len(values)
    return dict(count=n, mean=float(np.mean(values)) if n else None,
                standard_error=float(np.std(values, ddof=1) / np.sqrt(n)) if n > 1 else None)


def equilibrium_sample(rng, n):
    # Inverse CDF of the quartic Boltzmann density, with stated finite grid.
    grid = np.linspace(-1.2, 1.2, 240001)
    density = np.exp(-potential(grid, HI, 0))
    cdf = np.r_[0, np.cumsum((density[:-1] + density[1:]) / 2)]
    return np.interp(rng.random(n), cdf / cdf[-1], grid)


def run(tau, fmax, n=3000, dt=5e-4, seed=21):
    if tau <= 0 or dt <= 0 or n < 2:
        raise ValueError('Positive times and at least two trajectories are required')
    rng = np.random.default_rng(seed)
    x = equilibrium_sample(rng, n)
    initial_energy = potential(x, HI, 0)
    heat, work, midpoint_heat = np.zeros(n), np.zeros(n), np.zeros(n)
    old_b, old_f = HI, 0.0
    for duration, b0, b1, f1 in [(TB, HI, LO, 0), (tau, LO, LO, fmax), (TB, LO, HI, 0)]:
        steps = max(1, int(np.ceil(duration / dt)))
        h = duration / steps
        for k in range(steps):
            b, f = b0 + (b1-b0)*k/steps, f1*k/steps
            work += potential(x, b, f) - potential(x, old_b, old_f)
            xn = x - D*(gradient(x, b)-f)*h + np.sqrt(2*D*h)*rng.normal(size=n)
            heat += potential(x, b, f) - potential(xn, b, f)
            midpoint_heat += (f-gradient((x+xn)/2, b))*(xn-x)
            x, old_b, old_f = xn, b, f
    # Include the last parameter change and the sudden tilt removal above.
    work += potential(x, HI, 0) - potential(x, old_b, old_f)
    energy_change = potential(x, HI, 0) - initial_energy
    if not np.all(np.isfinite(work + heat + energy_change)):
        raise ArithmeticError('Nonfinite trajectory; reduce the time step')
    ok = x > 0
    p = float(np.mean(ok))
    entropy = -sum(q*np.log(q) for q in (p, 1-p) if q > 0)
    return dict(tau=tau, tilt=fmax, trajectories=n, dt=dt, seed=seed,
                success=statistics(ok.astype(float)),
                heat_all=statistics(heat), heat_success=statistics(heat[ok]),
                work_all=statistics(work), work_success=statistics(work[ok]),
                energy_change_all=statistics(energy_change),
                energy_change_success=statistics(energy_change[ok]),
                midpoint_heat_success=statistics(midpoint_heat[ok]),
                midpoint_error=statistics(work-midpoint_heat-energy_change),
                first_law_max_error=float(np.max(np.abs(work-heat-energy_change))),
                continuum_all_run_work_bound=float(np.log(2)-entropy),
                continuum_success_work_bound=float(np.log(2*p)) if p else None,
                success_exponential_work_weight=statistics(ok*np.exp(-work)))


def fit(rows, key):
    # Ordinary least squares; propagate trajectory sampling errors through
    # the linear fit. No uncertainty claim for the model or the time step.
    x = np.array([[1, 1/r['tau']] for r in rows])
    y = np.array([r[key]['mean'] for r in rows])
    errors = np.array([r[key]['standard_error'] for r in rows])
    transform = np.linalg.pinv(x)
    coefficients = transform @ y
    covariance = (transform * errors**2) @ transform.T
    residual = y-x@coefficients
    return dict(intercept=float(coefficients[0]), inverse_time_coefficient=float(coefficients[1]),
                sampling_standard_errors=np.sqrt(np.diag(covariance)).tolist(),
                residual_rms=float(np.sqrt(np.mean(residual**2))),
                scope='Descriptive six-point fit; intercept is not a proved slow-limit heat floor')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--trajectories', type=int, default=3000)
    parser.add_argument('--dt', type=float, default=5e-4)
    parser.add_argument('--seed', type=int, default=21)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = dict(status='running', script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  numpy_version=np.__version__, initialization='Numerical quartic Boltzmann CDF: [-1.2,1.2], 240001 points',
                  limitations='Sampling errors exclude discretization and model errors; continuum work bounds are comparisons, not heat bounds or kernel-checked theorems.', rows=[])
    def save():
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(report, indent=2)+'\n')
    save()
    for index, (tau, tilt) in enumerate(PLAN):
        row = run(tau, tilt, args.trajectories, args.dt, args.seed+index)
        report['rows'].append(row)
        save()
        print(json.dumps(row), flush=True)
    report['fits'] = {key: fit(report['rows'], key) for key in ['heat_all', 'heat_success', 'work_all', 'work_success']}
    report['status'] = 'completed'
    save()
    print(json.dumps(report['fits']), flush=True)


if __name__ == '__main__':
    main()
