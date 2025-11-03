#!/usr/bin/env python3
"""
Generate synthetic calorimetry data for testing the analysis pipeline.

This generates realistic-looking data that should PASS all gates if the
thermodynamic prediction E_dyn ≈ (k_B T ln 2)·Σμ holds.

Usage:
    python generate_synthetic_data.py [--fail]
    
Options:
    --fail  Generate data that will fail some gates (for testing)
"""

import argparse
import hashlib
import json
import sys
from datetime import datetime
from pathlib import Path

import numpy as np
import pandas as pd

# Boltzmann constant (J/K)
K_B = 1.380649e-23

def generate_program_suite():
    """Generate a suite of programs covering low to high μ."""
    programs = [
        {'id': 'tseitin_small', 'mu_range': (100, 500), 'category': 'low'},
        {'id': 'tseitin_medium_a', 'mu_range': (500, 1000), 'category': 'mid'},
        {'id': 'tseitin_medium_b', 'mu_range': (800, 1200), 'category': 'mid'},
        {'id': 'tseitin_large', 'mu_range': (1200, 2000), 'category': 'high'},
        {'id': 'mispartition_chaos', 'mu_range': (2000, 3500), 'category': 'high'},
        {'id': 'shuffled_blind', 'mu_range': (3000, 4500), 'category': 'high'},
        {'id': 'control_constant_mu', 'mu_range': (1000, 1000), 'category': 'control'},
        {'id': 'control_constant_time', 'mu_range': (500, 2500), 'category': 'control'},
    ]
    return programs


def generate_trials(programs, n_repeats=10, temp_range=(293, 313), 
                   dvfs_conditions=None, add_noise=True, fail_mode=False):
    """
    Generate synthetic calorimetry trials.
    
    Args:
        programs: List of program specifications
        n_repeats: Number of repeats per program
        temp_range: (min_T, max_T) in Kelvin
        dvfs_conditions: List of (V, f) tuples or None
        add_noise: Whether to add realistic measurement noise
        fail_mode: If True, generate data that fails some gates
    """
    if dvfs_conditions is None:
        dvfs_conditions = [(1.0, 100e6), (1.2, 150e6), (0.9, 75e6)]
    
    trials = []
    trial_id = 0
    
    # Generate temperature sweep
    temps = np.linspace(temp_range[0], temp_range[1], 3)
    
    for program in programs:
        for temp in temps:
            for v, f in dvfs_conditions:
                for repeat in range(n_repeats):
                    # Generate μ_sum
                    mu_min, mu_max = program['mu_range']
                    mu_sum = np.random.uniform(mu_min, mu_max)
                    
                    # Compute expected energy
                    # E_dyn = (k_B T ln 2) · μ_sum
                    # Scale up by 10^9 to represent realistic FPGA operations
                    # (accounts for multiple gate transitions per logical μ-bit)
                    SCALE_FACTOR = 1e9
                    X = K_B * temp * np.log(2) * mu_sum * SCALE_FACTOR
                    
                    if fail_mode:
                        # Add systematic bias to fail slope gate
                        slope = 0.85  # Will fail slope gate
                        intercept = 0.1 * X  # Will fail intercept gate
                    else:
                        # Near-perfect relationship
                        slope = 1.0 + np.random.normal(0, 0.01)
                        intercept = np.random.normal(0, 0.001 * X)
                    
                    E_joules = slope * X + intercept
                    
                    # Add measurement noise
                    if add_noise:
                        noise_level = 0.02 if not fail_mode else 0.15
                        E_joules += np.random.normal(0, noise_level * E_joules)
                    
                    # Execution time (correlated with μ but not energy in ideal case)
                    time_s = mu_sum / 1000.0 + np.random.normal(0, 0.05)
                    
                    # Handle control programs
                    control_type = ''
                    stalls = 0
                    
                    if program['category'] == 'control':
                        if 'constant_mu' in program['id']:
                            control_type = 'constant_mu'
                            # Half with stalls, half without
                            if repeat >= n_repeats // 2:
                                stalls = 100
                                # Energy should NOT change (constant μ)
                                time_s *= 1.5
                        elif 'constant_time' in program['id']:
                            control_type = 'constant_time'
                            # Keep time constant, vary μ
                            time_s = 1.0
                    
                    # Generate receipt hash
                    receipt_data = f"{program['id']}_{mu_sum}_{repeat}_{temp}_{v}_{f}"
                    receipt_hash = hashlib.sha256(receipt_data.encode()).hexdigest()
                    
                    trial = {
                        'trial_id': f'trial_{trial_id:06d}',
                        'program_id': program['id'],
                        'mu_sum': mu_sum,
                        'T_K': temp,
                        'E_joules': max(0, E_joules),  # Energy can't be negative
                        'time_s': max(0.001, time_s),
                        'V_volts': v,
                        'f_hz': f,
                        'board_id': 'synthetic_fpga_001',
                        'seed': repeat,
                        'repeat_idx': repeat,
                        'receipt_sha256': receipt_hash,
                        'code_commit': 'abc123def456',
                        'sensor_source': 'synthetic_ina226',
                        'control_type': control_type,
                        'stalls': stalls
                    }
                    
                    trials.append(trial)
                    trial_id += 1
    
    return pd.DataFrame(trials)


def generate_idle_baseline(duration_s=60, sample_rate_hz=10):
    """Generate synthetic idle baseline measurements."""
    n_samples = int(duration_s * sample_rate_hz)
    
    # Stable idle power around 5W
    V = 12.0
    I_idle = 5.0 / V  # ~0.417A
    
    timestamps = np.arange(n_samples) / sample_rate_hz
    V_samples = V + np.random.normal(0, 0.01, n_samples)
    I_samples = I_idle + np.random.normal(0, 0.005, n_samples)
    P_samples = V_samples * I_samples
    
    df = pd.DataFrame({
        'timestamp': timestamps,
        'V_volts': V_samples,
        'I_amps': I_samples,
        'P_watts': P_samples
    })
    
    return df


def main():
    parser = argparse.ArgumentParser(description='Generate synthetic calorimetry data')
    parser.add_argument('--fail', action='store_true',
                       help='Generate data that will fail some gates')
    parser.add_argument('--output-dir', type=str,
                       default=None,
                       help='Output directory (default: ../data/)')
    args = parser.parse_args()
    
    # Determine output directory
    if args.output_dir:
        output_dir = Path(args.output_dir)
    else:
        script_dir = Path(__file__).parent
        output_dir = script_dir.parent / 'data'
    
    output_dir.mkdir(parents=True, exist_ok=True)
    
    print("=" * 60)
    print("Synthetic Calorimetry Data Generator")
    print("=" * 60)
    print(f"\nMode: {'FAIL' if args.fail else 'PASS'}")
    print(f"Output: {output_dir}/")
    
    # Generate program suite
    print("\n1. Generating program suite...")
    programs = generate_program_suite()
    print(f"   {len(programs)} programs")
    
    # Generate trials
    print("\n2. Generating trials...")
    df = generate_trials(programs, n_repeats=10, fail_mode=args.fail)
    print(f"   {len(df)} trials")
    
    # Save trial data
    print("\n3. Saving trial data...")
    cal_data_path = output_dir / 'cal_data.csv'
    df.to_csv(cal_data_path, index=False)
    print(f"   Saved to {cal_data_path}")
    
    # Generate idle baseline
    print("\n4. Generating idle baseline...")
    idle_df = generate_idle_baseline()
    idle_path = output_dir / 'idle_baseline.csv'
    idle_df.to_csv(idle_path, index=False)
    print(f"   Saved to {idle_path}")
    
    # Summary statistics
    print("\n5. Summary statistics:")
    print(f"   μ range: {df['mu_sum'].min():.0f} - {df['mu_sum'].max():.0f}")
    print(f"   E range: {df['E_joules'].min():.2e} - {df['E_joules'].max():.2e} J")
    print(f"   T range: {df['T_K'].min():.1f} - {df['T_K'].max():.1f} K")
    print(f"   Programs: {df['program_id'].nunique()}")
    print(f"   Conditions: {len(df.groupby(['T_K', 'V_volts', 'f_hz']))}")
    
    print("\n" + "=" * 60)
    if args.fail:
        print("Generated data that should FAIL analysis gates")
        print("(for testing failure detection)")
    else:
        print("Generated data that should PASS analysis gates")
        print("(validates E_dyn ≈ (k_B T ln 2)·Σμ)")
    print("=" * 60)
    
    return 0


if __name__ == '__main__':
    sys.exit(main())
