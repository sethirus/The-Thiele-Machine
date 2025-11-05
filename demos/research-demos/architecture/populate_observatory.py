#!/usr/bin/env python3
"""
Observatory Population Script - The Data Factory

This script generates comprehensive sight log datasets for both:
1. Structured problems (Tseitin UNSAT instances)
2. Chaotic problems (Random 3-SAT at phase transition)

It orchestrates the experiment harness to create the raw data,
then uses sight_logging to produce and save the final sight logs.
"""

import argparse
import sys
import time
from pathlib import Path
from typing import List, Optional

# Add repo root to path
repo_root = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(repo_root))
# Add problem-solving demos directory for attempt.py import
sys.path.insert(0, str(repo_root / "demos" / "research-demos" / "problem-solving"))

from tools.sight_logging import assemble_log, save_log, update_index, append_progress_entry


def generate_structured_dataset(
    n_values: List[int],
    seeds: List[int],
    output_dir: Path = Path("sight_logs")
):
    """
    Generate sight logs for structured (Tseitin) problems.
    
    Args:
        n_values: List of problem sizes (n parameter for Tseitin)
        seeds: List of random seeds
        output_dir: Directory to save sight logs
    """
    from attempt import generate_tseitin_expander
    
    total = len(n_values) * len(seeds)
    count = 0
    
    print(f"\n{'='*60}")
    print("GENERATING STRUCTURED DATASET (Tseitin UNSAT Instances)")
    print(f"{'='*60}")
    print(f"Problem sizes (n): {n_values}")
    print(f"Seeds: {seeds}")
    print(f"Total instances: {total}")
    print(f"{'='*60}\n")
    
    append_progress_entry(f"Starting structured dataset generation: {total} instances")
    
    for n in n_values:
        if n % 2 != 0:
            print(f"⚠️  Skipping n={n}: Tseitin requires even n")
            continue
        
        for seed in seeds:
            count += 1
            problem_name = f"tseitin_n{n}_seed{seed}"
            
            print(f"[{count}/{total}] Generating {problem_name}...")
            
            try:
                # Generate Tseitin instance
                instance = generate_tseitin_expander(
                    n=n,
                    seed=seed,
                    global_seed=123456789,
                    verbose=False,
                    hb_period=3600  # Disable heartbeat for batch
                )
                
                # Extract CNF clauses
                clauses = instance.get("cnf_clauses", [])
                
                if not clauses:
                    print(f"  ⚠️  No clauses generated, skipping")
                    continue
                
                # Assemble sight log
                log = assemble_log(
                    clauses=clauses,
                    problem_name=problem_name,
                    n=n,
                    seed=seed,
                    verdict="CONSISTENT",  # Tseitin instances are structured UNSAT
                    metadata={
                        "problem_type": "tseitin",
                        "num_nodes": n,
                        "num_edges": len(instance.get("edges", [])),
                        "is_structured": True
                    }
                )
                
                # Save log
                log_path = save_log(log, output_dir)
                update_index(log_path, output_dir / "INDEX.json")
                
                print(f"  ✓ Saved to {log_path.name}")
                
            except Exception as e:
                print(f"  ✗ Error: {e}")
                continue
    
    append_progress_entry(f"Completed structured dataset: {count} instances")
    print(f"\n✓ Structured dataset complete: {count} sight logs generated\n")


def generate_chaotic_dataset(
    n_values: List[int],
    seeds: List[int],
    ratio: float = 4.26,
    output_dir: Path = Path("sight_logs")
):
    """
    Generate sight logs for chaotic (random 3-SAT) problems at phase transition.
    
    Args:
        n_values: List of problem sizes (number of variables)
        seeds: List of random seeds
        ratio: Clause-to-variable ratio (4.26 is the phase transition)
        output_dir: Directory to save sight logs
    """
    import random
    import numpy as np
    
    total = len(n_values) * len(seeds)
    count = 0
    
    print(f"\n{'='*60}")
    print("GENERATING CHAOTIC DATASET (Random 3-SAT at Phase Transition)")
    print(f"{'='*60}")
    print(f"Problem sizes (n): {n_values}")
    print(f"Seeds: {seeds}")
    print(f"Clause-to-variable ratio: {ratio}")
    print(f"Total instances: {total}")
    print(f"{'='*60}\n")
    
    append_progress_entry(f"Starting chaotic dataset generation: {total} instances")
    
    for n_vars in n_values:
        for seed in seeds:
            count += 1
            problem_name = f"random3sat_n{n_vars}_r{ratio}_seed{seed}"
            
            print(f"[{count}/{total}] Generating {problem_name}...")
            
            try:
                # Set random seed
                random.seed(seed)
                np.random.seed(seed)
                
                # Generate random 3-SAT instance
                num_clauses = int(n_vars * ratio)
                clauses = []
                
                for _ in range(num_clauses):
                    # Pick 3 distinct variables
                    vars_in_clause = random.sample(range(1, n_vars + 1), 3)
                    # Randomly negate each literal
                    clause = [v if random.random() < 0.5 else -v for v in vars_in_clause]
                    clauses.append(clause)
                
                # Assemble sight log
                log = assemble_log(
                    clauses=clauses,
                    problem_name=problem_name,
                    n=n_vars,
                    seed=seed,
                    verdict="SPURIOUS",  # Random 3-SAT at phase transition is chaotic
                    metadata={
                        "problem_type": "random_3sat",
                        "num_variables": n_vars,
                        "num_clauses": num_clauses,
                        "clause_to_var_ratio": ratio,
                        "is_structured": False,
                        "phase_transition": True
                    }
                )
                
                # Save log
                log_path = save_log(log, output_dir)
                update_index(log_path, output_dir / "INDEX.json")
                
                print(f"  ✓ Saved to {log_path.name}")
                
            except Exception as e:
                print(f"  ✗ Error: {e}")
                continue
    
    append_progress_entry(f"Completed chaotic dataset: {count} instances")
    print(f"\n✓ Chaotic dataset complete: {count} sight logs generated\n")


def main():
    parser = argparse.ArgumentParser(
        description="Populate the Observatory with sight logs for structured and chaotic problems"
    )
    parser.add_argument(
        "--mode",
        choices=["structured", "chaotic", "both"],
        default="both",
        help="Which dataset to generate"
    )
    parser.add_argument(
        "--n-start",
        type=int,
        default=4,
        help="Starting problem size"
    )
    parser.add_argument(
        "--n-end",
        type=int,
        default=20,
        help="Ending problem size"
    )
    parser.add_argument(
        "--n-step",
        type=int,
        default=2,
        help="Problem size step"
    )
    parser.add_argument(
        "--seeds",
        type=str,
        default="0,1,2",
        help="Comma-separated list of seeds"
    )
    parser.add_argument(
        "--ratio",
        type=float,
        default=4.26,
        help="Clause-to-variable ratio for random 3-SAT (default: 4.26, phase transition)"
    )
    parser.add_argument(
        "--output-dir",
        type=str,
        default="sight_logs",
        help="Output directory for sight logs"
    )
    
    args = parser.parse_args()
    
    # Parse parameters
    n_values = list(range(args.n_start, args.n_end + 1, args.n_step))
    seeds = [int(s.strip()) for s in args.seeds.split(",")]
    output_dir = Path(args.output_dir)
    
    # Create output directory
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # Initialize progress log
    progress_path = output_dir / "PROGRESS.md"
    if not progress_path.exists():
        with open(progress_path, 'w') as f:
            f.write("# Observatory Population Progress\n\n")
    
    start_time = time.time()
    
    # Generate datasets
    if args.mode in ["structured", "both"]:
        generate_structured_dataset(n_values, seeds, output_dir)
    
    if args.mode in ["chaotic", "both"]:
        generate_chaotic_dataset(n_values, seeds, args.ratio, output_dir)
    
    elapsed = time.time() - start_time
    
    print(f"\n{'='*60}")
    print(f"OBSERVATORY POPULATION COMPLETE")
    print(f"{'='*60}")
    print(f"Time elapsed: {elapsed:.2f} seconds")
    print(f"Output directory: {output_dir}")
    print(f"{'='*60}\n")
    
    append_progress_entry(f"Observatory population complete in {elapsed:.2f}s")


if __name__ == "__main__":
    main()
