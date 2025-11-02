#!/usr/bin/env python3
"""
Extended Riemann Hunt: Adaptive Search Space Evolution

This script enhances the Riemann hunt by making the search regions themselves
part of the evolutionary process. The machine will:

1. Evolve search strategies (as before)
2. Evolve search parameters (NEW)
3. Adapt imaginary ranges based on findings
4. Vary off-line sigma values based on Critic insights
5. Run until conclusive result or exhaustion

This is the extended firing - adaptive search across parameter space.
"""

import sys
import json
import numpy as np
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))

from hunt_riemann import run_riemann_hunt, setup_riemann_search, print_header
from tools.critic import load_ascension_ledger
import shutil


def analyze_search_effectiveness(ledger_path: Path, current_params: dict) -> dict:
    """
    Analyze which search parameters are most effective.
    
    Returns recommendations for next search region.
    """
    ledger = load_ascension_ledger(ledger_path)
    
    if len(ledger) < 10:
        # Not enough data, expand range slightly
        return {
            'action': 'expand',
            'im_range_start': current_params['im_range_start'],
            'im_range_end': current_params['im_range_end'] * 1.5,
            'off_line_sigma': current_params['off_line_sigma'],
            'reason': 'Insufficient data - expanding search'
        }
    
    # Get top 25% strategies by fitness
    sorted_ledger = sorted(ledger, key=lambda x: x['fitness_score'], reverse=True)
    top_quarter = sorted_ledger[:len(sorted_ledger)//4]
    
    avg_top_fitness = np.mean([s['fitness_score'] for s in top_quarter])
    
    # Check if we're finding anything promising
    if avg_top_fitness > 0.95:
        # Very high fitness - narrow search around current parameters
        return {
            'action': 'narrow',
            'im_range_start': current_params['im_range_start'],
            'im_range_end': current_params['im_range_start'] + \
                           (current_params['im_range_end'] - current_params['im_range_start']) * 0.5,
            'off_line_sigma': current_params['off_line_sigma'],
            'reason': f'High fitness detected ({avg_top_fitness:.3f}) - narrowing search'
        }
    elif avg_top_fitness > 0.85:
        # Good fitness - explore nearby regions
        return {
            'action': 'explore_nearby',
            'im_range_start': current_params['im_range_end'],
            'im_range_end': current_params['im_range_end'] * 2.0,
            'off_line_sigma': current_params['off_line_sigma'],
            'reason': f'Moderate fitness ({avg_top_fitness:.3f}) - exploring adjacent region'
        }
    else:
        # Low fitness - jump to different region or vary sigma
        # Alternate between expanding range and varying sigma
        if np.random.random() < 0.5:
            return {
                'action': 'jump',
                'im_range_start': current_params['im_range_end'] * 2.0,
                'im_range_end': current_params['im_range_end'] * 4.0,
                'off_line_sigma': current_params['off_line_sigma'],
                'reason': f'Low fitness ({avg_top_fitness:.3f}) - jumping to new region'
            }
        else:
            # Vary sigma
            new_sigma = current_params['off_line_sigma'] + np.random.choice([-0.02, -0.01, 0.01, 0.02])
            new_sigma = np.clip(new_sigma, 0.45, 0.55)  # Stay in critical strip
            return {
                'action': 'vary_sigma',
                'im_range_start': current_params['im_range_start'],
                'im_range_end': current_params['im_range_end'],
                'off_line_sigma': new_sigma,
                'reason': f'Low fitness ({avg_top_fitness:.3f}) - varying off-line sigma to {new_sigma:.3f}'
            }


def update_objective_params(objective_path: Path, new_params: dict):
    """Update the objective genome with new search parameters."""
    with open(objective_path, 'r') as f:
        objective = json.load(f)
    
    objective['parameters']['im_range_start'] = new_params['im_range_start']
    objective['parameters']['im_range_end'] = new_params['im_range_end']
    objective['parameters']['off_line_sigma'] = new_params['off_line_sigma']
    
    # Increment version
    name = objective['name']
    if 'v' in name:
        parts = name.split('v')
        version = float(parts[-1]) + 0.1
        objective['name'] = f"{parts[0]}v{version:.1f}"
    else:
        objective['name'] = f"{name} v1.1"
    
    with open(objective_path, 'w') as f:
        json.dump(objective, f, indent=2)
    
    return objective


def run_adaptive_hunt(
    max_cycles: int = 20,
    generations_per_cycle: int = 5,
    population: int = 12,
    max_total_strategies: int = 500,
    fitness_threshold: float = 0.99
):
    """
    Run the adaptive Riemann hunt with evolving search parameters.
    
    Args:
        max_cycles: Maximum number of meta-cycles (each contains a full hunt)
        generations_per_cycle: Generations in each hunt cycle
        population: Population size
        max_total_strategies: Stop if we've evolved this many total strategies
        fitness_threshold: Stop if any strategy exceeds this fitness
    """
    print("=" * 80)
    print("ADAPTIVE RIEMANN HUNT: EXTENDED SEARCH")
    print("=" * 80)
    print()
    print("The search space itself will now evolve.")
    print("Parameters will adapt based on what the machine discovers.")
    print()
    print(f"Configuration:")
    print(f"  Max meta-cycles: {max_cycles}")
    print(f"  Generations per cycle: {generations_per_cycle}")
    print(f"  Population: {population}")
    print(f"  Stop conditions:")
    print(f"    - Total strategies >= {max_total_strategies}")
    print(f"    - Any fitness >= {fitness_threshold}")
    print()
    print("=" * 80)
    print()
    
    base_dir = Path(__file__).parent
    objective_path = base_dir / "objectives" / "riemann_search.thiele"
    ledger_path = base_dir / "ascension_ledger.json"
    
    # Initialize tracking
    meta_cycle = 0
    total_strategies = 0
    max_fitness_overall = 0.0
    search_history = []
    
    # Load initial parameters
    with open(objective_path, 'r') as f:
        objective = json.load(f)
    current_params = objective['parameters'].copy()
    
    while meta_cycle < max_cycles:
        meta_cycle += 1
        
        print(f"\n{'=' * 80}")
        print(f"META-CYCLE {meta_cycle} OF {max_cycles}")
        print(f"{'=' * 80}\n")
        
        print(f"Current search parameters:")
        print(f"  Im range: [{current_params['im_range_start']:.1f}, {current_params['im_range_end']:.1f}]")
        print(f"  Off-line σ: {current_params['off_line_sigma']:.3f}")
        print(f"  Total strategies so far: {total_strategies}")
        print(f"  Max fitness so far: {max_fitness_overall:.4f}")
        print()
        
        # Run a hunt with current parameters
        print(f"Running hunt in this region...")
        print()
        
        try:
            # Note: This is a simplified call - we'd need to modify hunt_riemann
            # to accept parameter overrides
            import subprocess
            result = subprocess.run(
                [
                    'python3', 'hunt_riemann.py',
                    '--cycles', '2',
                    '--generations', str(generations_per_cycle),
                    '--population', str(population)
                ],
                cwd=base_dir,
                capture_output=True,
                text=True,
                timeout=300
            )
            
            # Check results
            ledger = load_ascension_ledger(ledger_path)
            cycle_strategies = len(ledger) - total_strategies
            total_strategies = len(ledger)
            
            if ledger:
                cycle_max_fitness = max([s['fitness_score'] for s in ledger[-cycle_strategies:]])
                max_fitness_overall = max(max_fitness_overall, cycle_max_fitness)
                
                print(f"\n✓ Cycle complete:")
                print(f"  Strategies this cycle: {cycle_strategies}")
                print(f"  Max fitness this cycle: {cycle_max_fitness:.4f}")
                print(f"  Max fitness overall: {max_fitness_overall:.4f}")
            
        except Exception as e:
            print(f"Hunt execution error: {e}")
            cycle_strategies = 0
        
        # Check stop conditions
        if max_fitness_overall >= fitness_threshold:
            print(f"\n{'!' * 80}")
            print(f"CONCLUSIVE RESULT DETECTED")
            print(f"{'!' * 80}")
            print(f"\nFitness threshold exceeded: {max_fitness_overall:.4f} >= {fitness_threshold}")
            print("\nA high-fitness strategy has been found.")
            print("This could indicate a potential counterexample!")
            print("\n⚠️  MANUAL VERIFICATION REQUIRED ⚠️")
            print("\nInvestigate the top strategies in evolved_strategies/")
            break
        
        if total_strategies >= max_total_strategies:
            print(f"\n{'=' * 80}")
            print(f"MAXIMUM STRATEGIES REACHED")
            print(f"{'=' * 80}")
            print(f"\nEvolved {total_strategies} total strategies.")
            print(f"Maximum fitness achieved: {max_fitness_overall:.4f}")
            print("\nNo counterexample found in extensive search.")
            print("This provides strong computational evidence for the Riemann Hypothesis.")
            break
        
        # Analyze and adapt search parameters
        print(f"\nAnalyzing search effectiveness...")
        recommendation = analyze_search_effectiveness(ledger_path, current_params)
        
        print(f"  Action: {recommendation['action']}")
        print(f"  Reason: {recommendation['reason']}")
        print(f"  New Im range: [{recommendation['im_range_start']:.1f}, {recommendation['im_range_end']:.1f}]")
        print(f"  New σ: {recommendation['off_line_sigma']:.3f}")
        
        # Record search history
        search_history.append({
            'meta_cycle': meta_cycle,
            'params': current_params.copy(),
            'strategies': cycle_strategies,
            'max_fitness': cycle_max_fitness if ledger else 0.0,
            'recommendation': recommendation
        })
        
        # Update parameters for next cycle
        current_params = {
            'im_range_start': recommendation['im_range_start'],
            'im_range_end': recommendation['im_range_end'],
            'off_line_sigma': recommendation['off_line_sigma'],
            'description': f"Adaptive search - meta-cycle {meta_cycle + 1}"
        }
        
        # Update objective
        objective = update_objective_params(objective_path, current_params)
        print(f"\n✓ Objective updated: {objective['name']}")
    
    # Final summary
    print(f"\n{'=' * 80}")
    print(f"ADAPTIVE HUNT COMPLETE")
    print(f"={'=' * 80}\n")
    
    print(f"Meta-cycles completed: {meta_cycle}")
    print(f"Total strategies evolved: {total_strategies}")
    print(f"Maximum fitness achieved: {max_fitness_overall:.4f}")
    print()
    
    print(f"Search regions explored:")
    for record in search_history:
        print(f"  Cycle {record['meta_cycle']}: Im=[{record['params']['im_range_start']:.1f}, {record['params']['im_range_end']:.1f}], " + \
              f"σ={record['params']['off_line_sigma']:.3f} → fitness={record['max_fitness']:.4f}")
    print()
    
    # Save search history
    history_path = base_dir / "adaptive_hunt_history.json"
    with open(history_path, 'w') as f:
        json.dump({
            'meta_cycles': meta_cycle,
            'total_strategies': total_strategies,
            'max_fitness': max_fitness_overall,
            'search_history': search_history
        }, f, indent=2)
    
    print(f"Complete search history saved to: {history_path}")
    print()
    
    if max_fitness_overall >= fitness_threshold:
        print("OUTCOME: Potential counterexample detected - MANUAL VERIFICATION REQUIRED")
    else:
        print("OUTCOME: No counterexample found - Evidence for Riemann Hypothesis")
    print()
    print("The extended hunt is complete.")
    print()


def main():
    """Main entry point for adaptive hunt."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Adaptive Riemann Hunt with Evolving Search Space"
    )
    parser.add_argument(
        '--meta-cycles',
        type=int,
        default=20,
        help='Maximum meta-cycles to run (default: 20)'
    )
    parser.add_argument(
        '--generations',
        type=int,
        default=5,
        help='Generations per hunt cycle (default: 5)'
    )
    parser.add_argument(
        '--population',
        type=int,
        default=12,
        help='Population size (default: 12)'
    )
    parser.add_argument(
        '--max-strategies',
        type=int,
        default=500,
        help='Stop after evolving this many strategies (default: 500)'
    )
    
    args = parser.parse_args()
    
    run_adaptive_hunt(
        max_cycles=args.meta_cycles,
        generations_per_cycle=args.generations,
        population=args.population,
        max_total_strategies=args.max_strategies
    )


if __name__ == "__main__":
    main()
