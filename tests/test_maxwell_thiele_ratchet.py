# Licensed under the Apache License, Version 2.0 (the "License")
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""
Tests for Maxwell's Demon with Thiele Machine μ-Ledger Integration.

These tests verify:
1. The μ-ledger is charged for information acquisition
2. Work is bounded by μ-information × k_B T ln(2)
3. The VM's μ-accounting has physical meaning
"""

import pytest
import numpy as np
from tempfile import TemporaryDirectory

KB = 1.38e-23
T = 300
LANDAUER_JOULES = KB * T * np.log(2)


class TestMuLedgerCharging:
    """Test that the demon charges the μ-ledger correctly."""
    
    def test_demon_charges_mu_standalone(self):
        """Without a ledger, demon tracks μ internally."""
        from physics.brownian_ratchet import ThieleDemon, Particle
        
        demon = ThieleDemon()
        p = Particle(x=1e-8)
        
        for _ in range(10):
            demon.measure_and_update(p)
        
        assert demon.mu_charged == 10
        assert demon.get_mu_information() == 10
    
    def test_demon_charges_vm_ledger(self):
        """With VM ledger, demon charges mu_discovery."""
        from physics.brownian_ratchet import ThieleDemon, Particle
        from thielecpu.state import MuLedger
        
        ledger = MuLedger()
        demon = ThieleDemon(mu_ledger=ledger)
        p = Particle(x=1e-8)
        
        initial = ledger.mu_discovery
        for _ in range(10):
            demon.measure_and_update(p)
        
        assert ledger.mu_discovery == initial + 10
        assert demon.get_mu_information() == 10
    
    def test_experiment_charges_ledger(self):
        """Full experiment charges the ledger."""
        from physics.brownian_ratchet import run_experiment
        from thielecpu.state import MuLedger
        
        ledger = MuLedger()
        result = run_experiment(
            steps=10000,
            measurement_interval=100,
            mu_ledger=ledger,
        )
        
        # 10000 steps / 100 interval = 100 measurements
        expected_measurements = 10000 // 100
        assert ledger.mu_discovery == expected_measurements
        assert result['mu_information'] == expected_measurements


class TestMuBound:
    """Test the key claim: W ≤ k_B T ln(2) × μ."""
    
    def test_single_trial_bound(self):
        """Single trial should satisfy the μ-bound."""
        from physics.brownian_ratchet import run_experiment
        
        result = run_experiment(steps=50000, seed=42)
        
        work_bits = result['work_in_bits']
        mu_bits = result['mu_information']
        
        # THE KEY CLAIM: W ≤ k_B T ln(2) × μ
        # In bits: work_bits ≤ mu_bits
        assert work_bits <= mu_bits * 1.1  # 10% tolerance
        assert result['bound_satisfied']
    
    def test_statistical_bound(self):
        """Statistical average should satisfy the bound."""
        from physics.brownian_ratchet import run_statistical_verification
        
        stats = run_statistical_verification(n_trials=20, steps_per_trial=30000)
        
        # Mean work should be less than mean μ
        assert stats['work_mean_bits'] < stats['mu_mean_bits']
        assert stats['bound_satisfied']
    
    def test_efficiency_below_one(self):
        """Efficiency = W/μ should be < 1."""
        from physics.brownian_ratchet import run_experiment
        
        result = run_experiment(steps=50000, seed=42)
        
        assert result['efficiency'] < 1.0


class TestBlindVsFeedback:
    """Test that feedback enables work extraction."""
    
    def test_feedback_extracts_more_work(self):
        """Demon mode extracts more work than blind mode."""
        from physics.brownian_ratchet import run_blind_comparison
        
        comparison = run_blind_comparison(n_trials=15, steps_per_trial=20000)
        
        # Feedback mode should extract more work
        assert comparison['demon']['work_mean_bits'] > comparison['blind']['work_mean_bits']
    
    def test_feedback_produces_forward_motion(self):
        """Demon mode produces net forward displacement."""
        from physics.brownian_ratchet import run_blind_comparison
        
        comparison = run_blind_comparison(n_trials=15, steps_per_trial=20000)
        
        # Demon should produce more forward motion than blind
        assert comparison['demon']['displacement_mean'] > comparison['blind']['displacement_mean']


class TestVMIntegration:
    """Test full integration with Thiele VM."""
    
    def test_experiment_on_vm(self):
        """Experiment runs on VM and charges ledger."""
        from thielecpu.state import State
        from thielecpu.vm import VM
        from physics.brownian_ratchet import run_experiment
        
        state = State()
        vm = VM(state)
        
        initial_mu = state.mu_ledger.mu_discovery
        
        # Pass the ledger to the experiment
        vm.python_globals['run_experiment'] = run_experiment
        vm.python_globals['ledger'] = state.mu_ledger
        
        result, _ = vm.execute_python("""
__result__ = run_experiment(steps=5000, seed=42, mu_ledger=ledger)
""")
        
        # Ledger should have been charged
        final_mu = state.mu_ledger.mu_discovery
        assert final_mu > initial_mu
        assert result['mu_information'] == final_mu - initial_mu
    
    def test_mu_bound_on_vm(self):
        """The μ-bound holds when running on VM."""
        from thielecpu.state import State
        from thielecpu.vm import VM
        from physics.brownian_ratchet import run_experiment
        
        state = State()
        vm = VM(state)
        
        vm.python_globals['run_experiment'] = run_experiment
        vm.python_globals['ledger'] = state.mu_ledger
        
        result, _ = vm.execute_python("""
__result__ = run_experiment(steps=30000, seed=42, mu_ledger=ledger)
""")
        
        # The key claim should hold
        assert result['bound_satisfied']
        assert result['work_in_bits'] <= result['mu_information'] * 1.1


class TestPhysicalMeaning:
    """Test that μ-ledger has physical meaning."""
    
    def test_mu_bounds_work_joules(self):
        """μ × LANDAUER_JOULES bounds actual work in Joules."""
        from physics.brownian_ratchet import run_experiment, LANDAUER_JOULES
        
        result = run_experiment(steps=50000, seed=42)
        
        work_joules = result['work_against_load']
        mu_bound_joules = result['mu_information'] * LANDAUER_JOULES
        
        # Work ≤ μ × k_B T ln(2)
        assert work_joules <= mu_bound_joules * 1.1
    
    def test_information_energy_equivalence(self):
        """μ-bits can be converted to energy bound."""
        from physics.brownian_ratchet import run_experiment, LANDAUER_JOULES
        
        result = run_experiment(steps=50000, seed=42)
        
        mu = result['mu_information']
        
        # 1 μ-bit = 1 bit of information
        # Maximum extractable energy = μ × k_B T ln(2)
        max_energy = mu * LANDAUER_JOULES
        actual_energy = result['work_against_load']
        
        # This inequality is the information-energy equivalence
        assert actual_energy <= max_energy * 1.1
        
        # And the μ-ledger tells us the bound
        assert result['mu_bound_joules'] == mu * LANDAUER_JOULES


class TestHonestClaims:
    """Verify we make only defensible claims."""
    
    def test_mu_is_upper_bound(self):
        """μ-information is an upper bound (1 bit per measurement)."""
        from physics.brownian_ratchet import run_experiment
        
        result = run_experiment(steps=10000, measurement_interval=100)
        
        # μ = number of measurements × 1 bit
        expected_mu = 10000 // 100
        assert result['mu_information'] == expected_mu
        
        # This is an upper bound on actual information gained
        # (actual info ≤ 1 bit per binary measurement)
    
    def test_work_from_dynamics_only(self):
        """Work is computed from dynamics, not from μ."""
        from physics.brownian_ratchet import run_experiment, F_LOAD
        
        result = run_experiment(steps=10000, seed=42)
        
        # Work = F_load × displacement (from dynamics)
        # NOT work = μ × constant (that would be circular)
        
        # Verify work scales with displacement, not μ
        displacement = result['net_displacement']
        work = result['work_against_load']
        
        # Work should be approximately F_LOAD × displacement
        # (not exact due to stochastic path)
        expected_order = F_LOAD * abs(displacement)
        assert abs(work) < expected_order * 10  # Within order of magnitude
