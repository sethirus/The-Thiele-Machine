#!/usr/bin/env python3
"""
Run Phase Tunneling Protocol Experiments

Generates SAT instances and runs comparative solving experiments:
- Random 3-SAT baseline (DPLL)
- Structured 3-SAT baseline (DPLL)
- Structured 3-SAT Thiele VM

Runs across α values from 3.0 to 6.0 with multiple trials per condition.
"""

import json
import subprocess
import time
import random
from pathlib import Path
from typing import List, Dict, Any
import sys

def run_single_experiment(generator_script: str, solver_script: str,
                         n_vars: int, alpha: float, seed: int,
                         timeout: float = 30.0) -> Dict[str, Any]:
    """
    Run a single experiment trial

    Args:
        generator_script: Path to SAT generator script
        solver_script: Path to solver script
        n_vars: Number of variables
        alpha: Clause-to-variable ratio
        seed: Random seed
        timeout: Solver timeout in seconds

    Returns:
        Trial result dictionary
    """
    try:
        # Generate instance
        gen_cmd = [
            sys.executable, str(Path(generator_script).resolve()),
            str(n_vars), str(alpha), str(seed)
        ]

        # Run in data directory
        data_dir = Path("experiments/phase_tunneling/data")
        data_dir.mkdir(parents=True, exist_ok=True)
        
        gen_result = subprocess.run(gen_cmd, capture_output=True, text=True, timeout=60, cwd=str(data_dir))
        if gen_result.returncode != 0:
            print(f"Generator failed: {gen_result.stderr}")
            return {"error": "generation_failed", "time": timeout}

        # Extract CNF filename from generator output
        cnf_file = None
        for line in gen_result.stdout.split('\n'):
            if line.startswith("Generated:"):
                cnf_file = line.split(": ")[1].strip()
                break

        if not cnf_file:
            print("Could not find CNF file in generator output")
            return {"error": "no_cnf_file", "time": timeout}

        # Run solver
        start_time = time.time()
        solve_cmd = [
            sys.executable, str(Path(solver_script).resolve()),
            cnf_file, str(timeout)
        ]

        # Run in data directory where CNF file was created
        data_dir = Path("experiments/phase_tunneling/data")
        solve_result = subprocess.run(solve_cmd, capture_output=True, text=True, timeout=timeout + 5, cwd=str(data_dir))
        elapsed = time.time() - start_time

        if solve_result.returncode != 0:
            print(f"Solver failed: {solve_result.stderr}")
            return {"error": "solver_failed", "time": elapsed}

        # Parse solver output
        result = {"time": elapsed, "error": None}

        for line in solve_result.stdout.split('\n'):
            line = line.strip()
            if line.startswith("Result:"):
                result["sat"] = "SAT" in line
            elif line.startswith("Time:"):
                # Extract time from solver output (more accurate)
                try:
                    result["time"] = float(line.split(": ")[1].rstrip('s'))
                except:
                    pass
            elif line.startswith("μ-cost:"):
                try:
                    result["mu_cost"] = float(line.split(": ")[1])
                except:
                    pass
            elif line.startswith("Separators found:"):
                try:
                    result["separators_found"] = int(line.split(": ")[1])
                except:
                    pass
            elif line.startswith("Subproblems solved:"):
                try:
                    result["subproblems_solved"] = int(line.split(": ")[1])
                except:
                    pass

        return result

    except subprocess.TimeoutExpired:
        return {"error": "timeout", "time": timeout}
    except Exception as e:
        print(f"Experiment error: {e}")
        return {"error": "exception", "time": timeout}

def run_experiment_set(experiment_type: str, generator_script: str, solver_script: str,
                      alphas: List[float], n_trials: int = 5, n_vars: int = 50) -> Dict[str, Any]:
    """
    Run a full experiment set across multiple α values

    Args:
        experiment_type: Type of experiment (random_baseline, structured_baseline, structured_thiele)
        generator_script: SAT generator script
        solver_script: Solver script
        alphas: List of α values to test
        n_trials: Number of trials per α
        n_vars: Number of variables per instance

    Returns:
        Experiment results dictionary
    """
    results = {
        "experiment_type": experiment_type,
        "n_vars": n_vars,
        "n_trials": n_trials,
        "timestamp": time.time(),
        "results": {}
    }

    for alpha in alphas:
        print(f"Running {experiment_type} at α={alpha}")
        alpha_results = []

        for trial in range(n_trials):
            seed = random.randint(0, 1000000)
            print(f"  Trial {trial + 1}/{n_trials} (seed={seed})")

            trial_result = run_single_experiment(
                generator_script, solver_script, n_vars, alpha, seed
            )
            alpha_results.append(trial_result)

            # Small delay between trials
            time.sleep(0.1)

        results["results"][alpha] = alpha_results

    return results

def save_results(results: Dict[str, Any], output_file: Path):
    """Save results to JSON file"""
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"Results saved to {output_file}")

def main():
    """Main experiment runner"""
    # Experiment parameters
    alphas = [3.0, 3.5, 4.0, 4.26, 4.5, 5.0, 5.5, 6.0]
    n_trials = 3  # Reduced for faster testing
    n_vars = 30   # Smaller instances for testing

    base_dir = Path("experiments/phase_tunneling")
    data_dir = base_dir / "data"
    data_dir.mkdir(parents=True, exist_ok=True)
    
    results_dir = base_dir / "results"
    results_dir.mkdir(parents=True, exist_ok=True)

    # Run random baseline experiments
    print("=== Running Random Baseline Experiments ===")
    random_results = run_experiment_set(
        "random_baseline",
        str(base_dir / "gen_random_3sat.py"),
        str(base_dir / "baseline_dpll_up.py"),
        alphas,
        n_trials,
        n_vars
    )
    save_results(random_results, results_dir / "random_baseline_results.json")

    # Run structured baseline experiments
    print("\n=== Running Structured Baseline Experiments ===")
    structured_baseline_results = run_experiment_set(
        "structured_baseline",
        str(base_dir / "gen_structured_3sat.py"),
        str(base_dir / "baseline_dpll_up.py"),
        alphas,
        n_trials,
        n_vars
    )
    save_results(structured_baseline_results, results_dir / "structured_baseline_results.json")

    # Run structured Thiele experiments
    print("\n=== Running Structured Thiele Experiments ===")
    structured_thiele_results = run_experiment_set(
        "structured_thiele",
        str(base_dir / "gen_structured_3sat.py"),
        str(base_dir / "thiele_driver.py"),
        alphas,
        n_trials,
        n_vars
    )
    save_results(structured_thiele_results, results_dir / "structured_thiele_results.json")

    print("\n=== Experiments Complete ===")
    print("Run 'python plot_results.py' to generate the phase tunneling plot.")

if __name__ == "__main__":
    main()