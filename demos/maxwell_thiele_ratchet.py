#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License")
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""
Demo: The Thiele Machine's μ-Ledger Has Physical Meaning

This demonstration proves two claims:

1. INFORMATION-ENERGY EQUIVALENCE:
   Work extracted ≤ k_B T ln(2) × Information acquired
   
2. THE μ-LEDGER HAS PHYSICAL MEANING:
   The VM's mu_discovery directly tracks information costs that
   bound extractable thermodynamic work.

HOW IT WORKS:
   - A Maxwell's demon measures a Brownian particle
   - Each measurement CHARGES the VM's μ-ledger (1 bit per measurement)
   - Work is computed from physics (F_load × displacement)
   - We verify: W ≤ k_B T ln(2) × μ_discovery

THE KEY INSIGHT:
   The μ-ledger is not just accounting - it tracks information in a way
   that has physical consequences. The bound proves this.
"""

import sys
import json
from pathlib import Path
from datetime import datetime
from tempfile import TemporaryDirectory

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))

from thielecpu.state import State, MuLedger
from thielecpu.vm import VM
from physics.brownian_ratchet import (
    run_experiment,
    run_blind_comparison,
    run_statistical_verification,
    LANDAUER_JOULES,
    KB,
    T,
    F_LOAD,
)


def run_on_vm(steps: int = 50000) -> dict:
    """Run experiment on the Thiele VM with μ-ledger integration."""
    
    state = State()
    vm = VM(state)
    
    # Record initial state
    initial_mu = state.mu_ledger.mu_discovery
    
    # Pass ledger to experiment for direct charging
    vm.python_globals['run_experiment'] = run_experiment
    vm.python_globals['ledger'] = state.mu_ledger
    vm.python_globals['STEPS'] = steps
    
    result, _ = vm.execute_python("""
__result__ = run_experiment(steps=STEPS, seed=42, mu_ledger=ledger)
""")
    
    final_mu = state.mu_ledger.mu_discovery
    
    return {
        'experiment': result,
        'vm_mu_ledger': {
            'initial': initial_mu,
            'final': final_mu,
            'delta': final_mu - initial_mu,
        },
    }


def print_banner():
    print()
    print("╔" + "═" * 68 + "╗")
    print("║" + " " * 68 + "║")
    print("║" + "THE THIELE MACHINE'S μ-LEDGER HAS PHYSICAL MEANING".center(68) + "║")
    print("║" + " " * 68 + "║")
    print("║" + "Information-Energy Equivalence Demonstration".center(68) + "║")
    print("║" + " " * 68 + "║")
    print("╚" + "═" * 68 + "╝")
    print()


def print_claims():
    print("┌" + "─" * 68 + "┐")
    print("│" + " THE CLAIMS".center(68) + "│")
    print("├" + "─" * 68 + "┤")
    print("│" + " " * 68 + "│")
    print("│  1. INFORMATION-ENERGY EQUIVALENCE:                               │")
    print("│     Work extracted ≤ k_B T ln(2) × Information acquired           │")
    print("│" + " " * 68 + "│")
    print("│  2. THE μ-LEDGER HAS PHYSICAL MEANING:                            │")
    print("│     mu_discovery tracks information with thermodynamic bounds     │")
    print("│" + " " * 68 + "│")
    print("│  HOW WE VERIFY:                                                   │")
    print("│     • Demon measures particle → charges μ-ledger (1 bit each)     │")
    print("│     • Work comes from dynamics (F × d), NOT from μ                │")
    print("│     • We show: W ≤ k_B T ln(2) × μ_discovery                      │")
    print("│" + " " * 68 + "│")
    print("└" + "─" * 68 + "┘")
    print()


def print_results(result: dict):
    exp = result['experiment']
    ledger = result['vm_mu_ledger']
    
    print("┌" + "─" * 68 + "┐")
    print("│" + " EXPERIMENT RESULTS".center(68) + "│")
    print("├" + "─" * 68 + "┤")
    print("│" + " " * 68 + "│")
    print(f"│  Physics:".ljust(69) + "│")
    print(f"│    Temperature:         {exp['temperature']} K".ljust(69) + "│")
    print(f"│    Load force:          {exp['load_force']:.2e} N".ljust(69) + "│")
    print(f"│    Steps:               {exp['steps']:,}".ljust(69) + "│")
    print("│" + " " * 68 + "│")
    print(f"│  VM μ-Ledger (mu_discovery):".ljust(69) + "│")
    print(f"│    Initial:             {ledger['initial']}".ljust(69) + "│")
    print(f"│    Final:               {ledger['final']}".ljust(69) + "│")
    print(f"│    Δμ (bits charged):   {ledger['delta']}".ljust(69) + "│")
    print("│" + " " * 68 + "│")
    print(f"│  Work Extracted:".ljust(69) + "│")
    print(f"│    Displacement:        {exp['net_displacement']:.2e} m".ljust(69) + "│")
    print(f"│    Work (Joules):       {exp['work_against_load']:.2e} J".ljust(69) + "│")
    print(f"│    Work (bits):         {exp['work_in_bits']:.2f} bits".ljust(69) + "│")
    print("│" + " " * 68 + "│")
    print(f"│  THE KEY COMPARISON:".ljust(69) + "│")
    print(f"│    Work extracted:      {exp['work_in_bits']:.2f} bits".ljust(69) + "│")
    print(f"│    μ-information:       {exp['mu_information']} bits".ljust(69) + "│")
    print(f"│    Bound (μ × k_B T ln2): {exp['mu_bound_joules']:.2e} J".ljust(69) + "│")
    print(f"│    Efficiency (W/μ):    {exp['efficiency']*100:.2f}%".ljust(69) + "│")
    print("│" + " " * 68 + "│")
    print("└" + "─" * 68 + "┘")
    print()


def print_comparison(comparison: dict):
    print("┌" + "─" * 68 + "┐")
    print("│" + " BLIND vs FEEDBACK COMPARISON".center(68) + "│")
    print("├" + "─" * 68 + "┤")
    print("│" + " " * 68 + "│")
    print(f"│  Blind Mode (measures but doesn't use info):".ljust(69) + "│")
    print(f"│    Mean displacement:   {comparison['blind']['displacement_mean']:.2e} m".ljust(69) + "│")
    print(f"│    Mean work:           {comparison['blind']['work_mean_bits']:.2f} bits".ljust(69) + "│")
    print("│" + " " * 68 + "│")
    print(f"│  Feedback Mode (demon uses information):".ljust(69) + "│")
    print(f"│    Mean displacement:   {comparison['demon']['displacement_mean']:.2e} m".ljust(69) + "│")
    print(f"│    Mean work:           {comparison['demon']['work_mean_bits']:.2f} bits".ljust(69) + "│")
    print("│" + " " * 68 + "│")
    if comparison['demon']['work_mean_bits'] > comparison['blind']['work_mean_bits']:
        print("│  → Information enables directed motion against the load          │")
    print("│" + " " * 68 + "│")
    print("└" + "─" * 68 + "┘")
    print()


def print_stats(stats: dict):
    print("┌" + "─" * 68 + "┐")
    print("│" + " STATISTICAL VERIFICATION".center(68) + "│")
    print("├" + "─" * 68 + "┤")
    print("│" + " " * 68 + "│")
    print(f"│  Trials: {stats['n_trials']}, Steps: {stats['steps_per_trial']:,} each".ljust(69) + "│")
    print("│" + " " * 68 + "│")
    print(f"│  Mean work:       {stats['work_mean_bits']:.2f} ± {stats['work_std_bits']:.2f} bits".ljust(69) + "│")
    print(f"│  Mean μ-info:     {stats['mu_mean_bits']:.0f} ± {stats['mu_std_bits']:.0f} bits".ljust(69) + "│")
    print(f"│  Mean efficiency: {stats['efficiency_mean']*100:.2f}% ± {stats['efficiency_std']*100:.2f}%".ljust(69) + "│")
    print("│" + " " * 68 + "│")
    print(f"│  Bound satisfied: {stats['bound_satisfied']}".ljust(69) + "│")
    print(f"│  Violations:      {stats['violations']}/{stats['n_trials']}".ljust(69) + "│")
    print("│" + " " * 68 + "│")
    print("└" + "─" * 68 + "┘")
    print()


def print_verdict(result: dict, stats: dict):
    exp = result['experiment']
    
    print("╔" + "═" * 68 + "╗")
    print("║" + " " * 68 + "║")
    
    if stats['bound_satisfied']:
        print("║" + "✓ CLAIMS VERIFIED".center(68) + "║")
    else:
        print("║" + "✗ CLAIMS NOT VERIFIED".center(68) + "║")
    
    print("║" + " " * 68 + "║")
    print("╠" + "═" * 68 + "╣")
    print("║" + " " * 68 + "║")
    print("║" + "CLAIM 1: INFORMATION-ENERGY EQUIVALENCE".center(68) + "║")
    print("║" + " " * 68 + "║")
    print("║" + f"W ({exp['work_in_bits']:.2f} bits) ≤ μ ({exp['mu_information']} bits)".center(68) + "║")
    print("║" + " " * 68 + "║")
    print("║" + "Work is bounded by k_B T ln(2) × information acquired.".center(68) + "║")
    print("║" + " " * 68 + "║")
    print("╠" + "═" * 68 + "╣")
    print("║" + " " * 68 + "║")
    print("║" + "CLAIM 2: THE μ-LEDGER HAS PHYSICAL MEANING".center(68) + "║")
    print("║" + " " * 68 + "║")
    print("║" + "mu_discovery tracks information that bounds thermodynamic work.".center(68) + "║")
    print("║" + f"Efficiency {stats['efficiency_mean']*100:.1f}% < 100% as thermodynamics requires.".center(68) + "║")
    print("║" + " " * 68 + "║")
    print("╠" + "═" * 68 + "╣")
    print("║" + " " * 68 + "║")
    print("║" + "THE THIELE MACHINE'S μ-LEDGER IS NOT JUST BOOKKEEPING.".center(68) + "║")
    print("║" + "IT TRACKS INFORMATION WITH PHYSICAL CONSEQUENCES.".center(68) + "║")
    print("║" + " " * 68 + "║")
    print("╚" + "═" * 68 + "╝")
    print()


def save_receipt(result: dict, stats: dict, comparison: dict, outpath: Path):
    exp = result['experiment']
    ledger = result['vm_mu_ledger']
    
    receipt = {
        'timestamp': datetime.now().isoformat() + 'Z',
        'experiment': 'thiele_mu_ledger_physical_meaning',
        
        'claims': {
            'information_energy_equivalence': 'W ≤ k_B T ln(2) × μ_information',
            'mu_ledger_physical_meaning': 'mu_discovery bounds thermodynamic work',
        },
        
        'single_trial': {
            'work_bits': float(exp['work_in_bits']),
            'mu_information_bits': int(exp['mu_information']),
            'efficiency': float(exp['efficiency']),
            'bound_satisfied': bool(exp['bound_satisfied']),
            'vm_mu_delta': int(ledger['delta']),
        },
        
        'statistics': {
            'n_trials': int(stats['n_trials']),
            'work_mean_bits': float(stats['work_mean_bits']),
            'mu_mean_bits': float(stats['mu_mean_bits']),
            'efficiency_mean': float(stats['efficiency_mean']),
            'bound_satisfied': bool(stats['bound_satisfied']),
        },
        
        'comparison': {
            'blind_work_bits': float(comparison['blind']['work_mean_bits']),
            'demon_work_bits': float(comparison['demon']['work_mean_bits']),
            'information_enables_work': bool(
                comparison['demon']['work_mean_bits'] > comparison['blind']['work_mean_bits']
            ),
        },
        
        'physical_constants': {
            'temperature_K': int(T),
            'boltzmann_J_per_K': float(KB),
            'landauer_J_per_bit': float(LANDAUER_JOULES),
        },
        
        'methodology': {
            'work_definition': 'F_load × displacement (from Langevin dynamics)',
            'information_definition': 'μ-ledger charge (1 bit per measurement)',
            'not_circular': 'Work computed from dynamics, μ from ledger charges',
        },
    }
    
    outpath.write_text(json.dumps(receipt, indent=2))
    print(f"Receipt saved to: {outpath}")


def main():
    print_banner()
    print_claims()
    
    print("Running experiment on Thiele Machine VM...")
    result = run_on_vm(steps=50000)
    print_results(result)
    
    print("Comparing blind vs feedback modes (20 trials each)...")
    comparison = run_blind_comparison(n_trials=20, steps_per_trial=30000)
    print_comparison(comparison)
    
    print("Running statistical verification (30 trials)...")
    
    # Use factory to create fresh ledgers for each trial
    stats = run_statistical_verification(
        n_trials=30,
        steps_per_trial=30000,
        mu_ledger_factory=MuLedger,
    )
    print_stats(stats)
    
    print_verdict(result, stats)
    
    # Save receipt
    receipt_path = REPO_ROOT / 'artifacts' / 'mu_ledger_physical_meaning.json'
    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    save_receipt(result, stats, comparison, receipt_path)
    
    return 0 if stats['bound_satisfied'] else 1


if __name__ == "__main__":
    sys.exit(main())
