"""Check the numerical illustration's force and energy accounting."""
import importlib.util
from pathlib import Path
import unittest

import numpy as np

MODULE_PATH = Path(__file__).resolve().parents[1] / 'scripts' / 'bead_erasure_sim.py'
spec = importlib.util.spec_from_file_location('bead_erasure_sim', MODULE_PATH)
bead = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bead)


class BeadAccountingTests(unittest.TestCase):
    def test_force_matches_potential_derivative(self):
        x = np.linspace(-0.8, 0.8, 31)
        h = 1e-6
        for barrier, tilt in [(8, 0), (2.2, 3.1)]:
            finite_difference = (bead.potential(x+h, barrier, tilt)-bead.potential(x-h, barrier, tilt))/(2*h)
            np.testing.assert_allclose(bead.gradient(x, barrier)-tilt, finite_difference, rtol=1e-7, atol=1e-7)

    def test_initial_sampler_matches_quartic_density(self):
        samples = bead.equilibrium_sample(np.random.default_rng(42), 100000)
        grid = np.linspace(-1.2, 1.2, 10001)
        weight = np.exp(-bead.potential(grid, bead.HI, 0))
        def integral(values):
            return np.sum((values[1:]+values[:-1])*np.diff(grid)/2)
        expected_energy = integral(weight*bead.potential(grid, bead.HI, 0))/integral(weight)
        self.assertLess(abs(np.mean(samples > 0)-0.5), 0.006)
        self.assertLess(abs(np.mean(bead.potential(samples, bead.HI, 0))-expected_energy), 0.012)

    def test_complete_protocol_accounts_for_work_heat_and_energy(self):
        row = bead.run(0.02, 3.1, n=64, dt=1e-4, seed=9)
        self.assertLess(row['first_law_max_error'], 1e-10)
        self.assertAlmostEqual(row['work_all']['mean']-row['heat_all']['mean'], row['energy_change_all']['mean'], places=10)
        self.assertEqual(row['heat_all']['count'], 64)
        self.assertEqual(row['heat_success']['count'], round(64*row['success']['mean']))


if __name__ == '__main__':
    unittest.main()
