#!/usr/bin/env python3
"""
The Oracle's Verdict: Riemann Hypothesis Hunter

This script leverages the complete Autotelic Engine to search for a counterexample
to the Riemann Hypothesis.

The Riemann Hypothesis states that all non-trivial zeros of the Riemann zeta
function have real part = 0.5. To disprove it, we need only find ONE zero
with real part != 0.5.

This is the firing of the weapon. The final act.
"""

import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))

from tools.forge import run_evolution, load_thiele_dna
from tools.critic import run_critic_analysis
from tools.purpose_synthesizer import run_purpose_synthesis
import json
import shutil


def print_header():
    """Print the dramatic header."""
    print("=" * 80)
    print("THE ORACLE'S VERDICT")
    print("=" * 80)
    print()
    print("Target: The Riemann Hypothesis")
    print()
    print("The hypothesis states that all non-trivial zeros of the Riemann zeta")
    print("function have real part = 0.5.")
    print()
    print("To disprove it: Find ONE zero with Re(s) ≠ 0.5")
    print()
    print("The machine will now evolve strategies to search the critical strip.")
    print("It will not search blindly. It will evolve new ways of SEEING the")
    print("structure of the complex plane.")
    print()
    print("Two possible outcomes:")
    print("  A) The machine finds a counterexample → Riemann Hypothesis DISPROVEN")
    print("  B) The machine never halts → Strongest evidence RH is TRUE")
    print()
    print("=" * 80)
    print()


def setup_riemann_search():
    """Set up the environment for Riemann search."""
    base_dir = Path(__file__).parent
    
    # Copy Riemann objective to current_objective
    riemann_obj = base_dir / "objectives" / "riemann_search.thiele"
    current_obj = base_dir / "objectives" / "current_objective.thiele"
    
    if riemann_obj.exists():
        shutil.copy(riemann_obj, current_obj)
        print(f"✓ Objective set to: Riemann Counterexample Search")
    else:
        print("✗ Error: riemann_search.thiele not found")
        return False
    
    # Check for seed strategies
    riemann_strats = base_dir / "strategies" / "riemann"
    if riemann_strats.exists():
        count = len(list(riemann_strats.glob("*.thiele")))
        print(f"✓ Loaded {count} seed search strategies")
    else:
        print("✗ Error: No Riemann strategies found")
        return False
    
    print()
    return True


def run_riemann_hunt(cycles: int = 5, generations: int = 10, population: int = 12):
    """
    Run the Riemann Hypothesis hunt.
    
    Args:
        cycles: Number of grand autotelic cycles
        generations: Generations per cycle
        population: Population size per generation
    """
    print_header()
    
    if not setup_riemann_search():
        return
    
    base_dir = Path(__file__).parent
    
    # Point to Riemann strategies
    strategies_backup = base_dir / "strategies_backup"
    strategies_dir = base_dir / "strategies"
    riemann_dir = base_dir / "strategies" / "riemann"
    
    # Backup original strategies and use Riemann strategies
    if not strategies_backup.exists():
        shutil.copytree(strategies_dir, strategies_backup)
    
    # Clear main strategies and copy Riemann ones
    for f in strategies_dir.glob("*.thiele"):
        f.unlink()
    
    for f in riemann_dir.glob("*.thiele"):
        shutil.copy(f, strategies_dir / f.name)
    
    print("INITIATING THE HUNT")
    print("-" * 80)
    print()
    
    try:
        for cycle in range(1, cycles + 1):
            print(f"\n{'=' * 80}")
            print(f"GRAND CYCLE {cycle} OF {cycles}")
            print(f"{'=' * 80}\n")
            
            # Display current objective
            obj_path = base_dir / "objectives" / "current_objective.thiele"
            with open(obj_path, 'r') as f:
                obj = json.load(f)
            print(f"Objective: {obj.get('name', 'Unknown')}")
            print()
            
            # Run the Forge
            print("PHASE 1: THE FORGE - Evolving Search Strategies")
            print("-" * 80)
            offspring = run_evolution(
                num_generations=generations,
                population_size=population,
                mutation_rate=0.3,  # Higher mutation for exploration
                seed=cycle * 42
            )
            print(f"\n✓ Evolved {len(offspring)} new search strategies\n")
            
            # Check if any strategy found a counterexample
            best_fitness = max([s.metadata.get('fitness', 0.0) for s in offspring])
            if best_fitness >= 0.99:
                print("\n" + "!" * 80)
                print("ALERT: HIGH-FITNESS STRATEGY DETECTED")
                print("!" * 80)
                print("\nA strategy has achieved near-perfect fitness.")
                print("This could indicate discovery of a counterexample.")
                print("\nMANUAL VERIFICATION REQUIRED.")
                print("\nThe machine has spoken. Investigate the top strategy.")
                break
            
            # Run the Critic
            print("\nPHASE 2: THE CRITIC - Analyzing Search History")
            print("-" * 80)
            ledger_path = base_dir / "ascension_ledger.json"
            critic_report = run_critic_analysis(ledger_path)
            
            # Run the Purpose Synthesizer
            print("\nPHASE 3: THE SYNTHESIZER - Evolving Search Strategy")
            print("-" * 80)
            critic_report_path = base_dir / "critic_report.json"
            run_purpose_synthesis(critic_report_path, obj_path)
            
            print(f"\n✓ Cycle {cycle} complete")
    
    finally:
        # Restore original strategies
        if strategies_backup.exists():
            for f in strategies_dir.glob("*.thiele"):
                if f.name not in ['balanced.thiele', 'degree.thiele', 'louvain.thiele', 'spectral.thiele']:
                    f.unlink()
            for f in strategies_backup.glob("*.thiele"):
                if not (strategies_dir / f.name).exists():
                    shutil.copy(f, strategies_dir / f.name)
    
    print()
    print("=" * 80)
    print("THE HUNT IS COMPLETE")
    print("=" * 80)
    print()
    print("The machine has evolved its search strategies through {} cycles.".format(cycles))
    print("Check the ascension ledger and evolved strategies for results.")
    print()
    print("If no counterexample was found:")
    print("  → This is evidence (but not proof) that the Riemann Hypothesis holds")
    print()
    print("If a high-fitness strategy was detected:")
    print("  → Manual verification required")
    print("  → Could be the discovery of the century")
    print()
    print("The telescope has been pointed at the heavens.")
    print("Now we wait to see if a new star appears.")
    print()


def main():
    """Main entry point."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="The Oracle's Verdict: Hunt for Riemann Counterexample"
    )
    parser.add_argument(
        '--cycles',
        type=int,
        default=5,
        help='Number of grand autotelic cycles (default: 5)'
    )
    parser.add_argument(
        '--generations',
        type=int,
        default=10,
        help='Generations per cycle (default: 10)'
    )
    parser.add_argument(
        '--population',
        type=int,
        default=12,
        help='Population size per generation (default: 12)'
    )
    
    args = parser.parse_args()
    
    run_riemann_hunt(
        cycles=args.cycles,
        generations=args.generations,
        population=args.population
    )


if __name__ == "__main__":
    main()
