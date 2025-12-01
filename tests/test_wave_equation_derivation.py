#!/usr/bin/env python3
"""
Tests for Wave Equation Derivation via Thiele Machine

Copyright 2025 Devon Thiele
Licensed under the Apache License, Version 2.0
"""

import math
import sys
from pathlib import Path

import numpy as np
import pytest

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from tools.wave_equation_derivation import (
    WaveModel,
    enumerate_partitions,
    fit_partition,
    select_best_partition,
    extract_discrete_rule,
    discrete_to_pde,
    validate_rule,
    generate_coq_formalization,
    run_derivation,
)
from tools.wave_falsification_test import run_falsification_test


class TestWaveModel:
    """Tests for the WaveModel class."""
    
    def test_wave_model_initialization(self):
        """Test WaveModel initializes correctly."""
        model = WaveModel(lattice_size=64, wave_speed=0.5)
        assert model.lattice_size == 64
        assert model.wave_speed == 0.5
        assert model.c_squared == 0.25
    
    def test_cfl_condition_violation(self):
        """Test that CFL condition violations raise errors."""
        with pytest.raises(ValueError, match="CFL condition violated"):
            WaveModel(lattice_size=64, wave_speed=1.0)  # Too fast
    
    def test_initial_packet_shape(self):
        """Test initial packet has correct shape."""
        model = WaveModel(lattice_size=64)
        packet = model.initial_packet()
        assert packet.shape == (64,)
        assert np.max(packet) <= 1.0
    
    def test_evolve_step_preserves_shape(self):
        """Test that evolution preserves array shape."""
        model = WaveModel(lattice_size=64)
        u0 = model.initial_packet()
        u1 = model.evolve_step(u0, u0)
        assert u1.shape == u0.shape
    
    def test_generate_evolution_shape(self):
        """Test generated evolution has correct shape."""
        model = WaveModel(lattice_size=64)
        evolution = model.generate_evolution(timesteps=100)
        assert evolution.shape == (100, 64)
    
    def test_wave_energy_conservation(self):
        """Test approximate energy conservation for wave evolution."""
        model = WaveModel(lattice_size=64, wave_speed=0.5)
        evolution = model.generate_evolution(timesteps=50)
        
        # Compute energy at each timestep
        energies = []
        for t in range(1, 49):
            # Kinetic energy: (u(t+1) - u(t-1))² / (4*dt²)
            du_dt = (evolution[t+1] - evolution[t-1]) / 2.0
            kinetic = 0.5 * np.sum(du_dt ** 2)
            
            # Potential energy: c² * (u(x+1) - u(x))²
            du_dx = np.roll(evolution[t], -1) - evolution[t]
            potential = 0.5 * model.c_squared * np.sum(du_dx ** 2)
            
            energies.append(kinetic + potential)
        
        # Energy should be approximately conserved
        energies = np.array(energies)
        energy_variation = np.std(energies) / np.mean(energies)
        assert energy_variation < 0.1  # Less than 10% variation


class TestPartitions:
    """Tests for partition enumeration and fitting."""
    
    def test_enumerate_partitions_count(self):
        """Test that we enumerate expected number of partitions."""
        partitions = enumerate_partitions()
        assert len(partitions) >= 4  # At least 4 different structures
    
    def test_partition_stencils_valid(self):
        """Test that all partition stencils are valid."""
        partitions = enumerate_partitions()
        for p in partitions:
            assert len(p.stencil) > 0
            for dt, dx in p.stencil:
                assert isinstance(dt, int)
                assert isinstance(dx, int)
    
    def test_fit_partition_returns_result(self):
        """Test that fitting returns a valid result."""
        model = WaveModel(lattice_size=32)
        evolution = model.generate_evolution(timesteps=50)
        
        partitions = enumerate_partitions()
        result = fit_partition(evolution, partitions[0])
        
        assert result.rms_error >= 0
        assert result.mu_total >= 0
        assert result.num_samples > 0


class TestDerivation:
    """Tests for the full derivation pipeline."""
    
    def test_select_best_partition_finds_wave_eq(self):
        """Test that optimal partition is wave equation form."""
        model = WaveModel(lattice_size=64, wave_speed=0.5)
        evolution = model.generate_evolution(timesteps=100)
        
        partitions = enumerate_partitions()
        results = [fit_partition(evolution, p) for p in partitions]
        best = select_best_partition(results)
        
        # Best partition should have very low RMS error
        assert best.rms_error < 1e-10
    
    def test_extract_discrete_rule_coefficients(self):
        """Test that extracted coefficients are physically correct."""
        model = WaveModel(lattice_size=64, wave_speed=0.5)
        evolution = model.generate_evolution(timesteps=100)
        
        partitions = enumerate_partitions()
        results = [fit_partition(evolution, p) for p in partitions]
        best = select_best_partition(results)
        
        rule = extract_discrete_rule(best)
        
        # For wave equation with c²=0.25:
        # coeff_u_t ≈ 2 - 2*0.25 = 1.5
        # coeff_u_tm1 ≈ -1
        # coeff_u_xp ≈ 0.25
        # coeff_u_xm ≈ 0.25
        assert abs(rule.coeff_u_t - 1.5) < 1e-6
        assert abs(rule.coeff_u_tm1 - (-1.0)) < 1e-6
        assert abs(rule.coeff_u_xp - 0.25) < 1e-6
        assert abs(rule.coeff_u_xm - 0.25) < 1e-6
    
    def test_discrete_to_pde_extracts_c_squared(self):
        """Test that PDE conversion extracts correct c²."""
        model = WaveModel(lattice_size=64, wave_speed=0.5)
        evolution = model.generate_evolution(timesteps=100)
        
        partitions = enumerate_partitions()
        results = [fit_partition(evolution, p) for p in partitions]
        best = select_best_partition(results)
        rule = extract_discrete_rule(best)
        pde = discrete_to_pde(rule)
        
        # Should extract c² = 0.25
        assert abs(pde.wave_speed_squared - 0.25) < 1e-6
        assert abs(pde.wave_speed - 0.5) < 1e-6
    
    def test_validate_rule_low_error(self):
        """Test that validated rule has low error."""
        model = WaveModel(lattice_size=64, wave_speed=0.5)
        evolution = model.generate_evolution(timesteps=100)
        
        partitions = enumerate_partitions()
        results = [fit_partition(evolution, p) for p in partitions]
        best = select_best_partition(results)
        rule = extract_discrete_rule(best)
        
        rms_error, max_error = validate_rule(evolution, rule)
        
        # Should have machine-precision error
        assert rms_error < 1e-10
        assert max_error < 1e-10
    
    def test_generate_coq_formalization_valid(self):
        """Test that Coq formalization is valid."""
        model = WaveModel(lattice_size=64, wave_speed=0.5)
        evolution = model.generate_evolution(timesteps=100)
        
        partitions = enumerate_partitions()
        results = [fit_partition(evolution, p) for p in partitions]
        best = select_best_partition(results)
        rule = extract_discrete_rule(best)
        pde = discrete_to_pde(rule)
        
        coq_code = generate_coq_formalization(rule, pde, best.rms_error)
        
        # Check Coq code contains expected elements
        assert "Definition wave_coeff_u_t" in coq_code
        assert "Definition wave_c_squared" in coq_code
        assert "Theorem emergent_wave_eq" in coq_code
        assert "WaveCheck" in coq_code


class TestFalsificationTest:
    """Tests for the falsification test script."""
    
    def test_falsification_passes_correct_params(self):
        """Test that falsification passes with correct parameters."""
        result = run_falsification_test(
            lattice_size=32,
            timesteps=50,
            wave_speed=0.5,
            seed=42,
            verbose=False
        )
        assert result is True
    
    def test_falsification_passes_different_wave_speeds(self):
        """Test falsification with different wave speeds."""
        for c in [0.3, 0.4, 0.5, 0.6]:
            result = run_falsification_test(
                lattice_size=32,
                timesteps=50,
                wave_speed=c,
                seed=42,
                verbose=False
            )
            assert result is True, f"Failed for c={c}"
    
    def test_falsification_reproducible(self):
        """Test that falsification results are reproducible."""
        results = []
        for _ in range(3):
            result = run_falsification_test(
                lattice_size=32,
                timesteps=50,
                wave_speed=0.5,
                seed=42,
                verbose=False
            )
            results.append(result)
        
        # All runs should give the same result
        assert all(r == results[0] for r in results)


class TestFullPipeline:
    """Integration tests for the full derivation pipeline."""
    
    def test_run_derivation_returns_dict(self):
        """Test that run_derivation returns complete results."""
        results = run_derivation(
            lattice_size=32,
            timesteps=50,
            wave_speed=0.5,
            seed=42,
            output_path=None
        )
        
        assert "evolution" in results
        assert "best_result" in results
        assert "rule" in results
        assert "pde" in results
        assert "verdict" in results
    
    def test_run_derivation_verified_verdict(self):
        """Test that derivation produces verified verdict."""
        results = run_derivation(
            lattice_size=64,
            timesteps=100,
            wave_speed=0.5,
            seed=42,
            output_path=None
        )
        
        assert results["verdict"] == "VERIFIED"
    
    def test_run_derivation_correct_pde(self):
        """Test that derivation extracts correct PDE."""
        c = 0.4
        results = run_derivation(
            lattice_size=64,
            timesteps=100,
            wave_speed=c,
            seed=42,
            output_path=None
        )
        
        pde = results["pde"]
        assert abs(pde.wave_speed_squared - c**2) < 0.01
