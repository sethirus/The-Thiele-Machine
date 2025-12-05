#!/usr/bin/env python3
"""
Batch SAT Benchmark Runner - B1.3 Implementation
=================================================

Run benchmarks on multiple CNF instances and collect results.

TASK: B1.3 from RESEARCH_PROGRAM_MASTER_PLAN.md
GOAL: Test H2 on 100+ instances to validate structural advantage hypothesis

USAGE:
    # Generate test instances and benchmark
    python tools/run_batch_benchmarks.py --generate --output benchmarks/sat_results.csv
    
    # Benchmark existing directory
    python tools/run_batch_benchmarks.py --input-dir benchmarks/instances/ --output benchmarks/sat_results.csv

OUTPUT:
    CSV file with columns:
    - instance, type, vars, clauses, density
    - baseline_time, sighted_time, speedup
    - baseline_mu, sighted_mu, mu_ratio
    - advantage, advantage_type
"""

import argparse
import csv
import subprocess
import sys
from pathlib import Path
from typing import List, Dict
import json
import time

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))


class BatchBenchmark:
    """Batch benchmark runner for SAT instances."""
    
    def __init__(self, timeout: int = 60, output_dir: Path = None):
        self.timeout = timeout
        self.output_dir = output_dir or Path("benchmarks/instances")
        self.output_dir.mkdir(parents=True, exist_ok=True)
    
    def generate_test_suite(self) -> List[Path]:
        """
        Generate diverse test suite for H2 validation.
        
        Returns:
            List of paths to generated CNF files
        """
        print("Generating test suite...")
        instances = []
        
        # Structured instances (should show H2 advantage)
        structured_configs = [
            # Modular instances (varying size and modules)
            ("modular", 20, 4, "modular_20v_4m"),
            ("modular", 30, 5, "modular_30v_5m"),
            ("modular", 40, 4, "modular_40v_4m"),
            ("modular", 50, 5, "modular_50v_5m"),
            ("modular", 60, 6, "modular_60v_6m"),
            ("modular", 80, 8, "modular_80v_8m"),
            ("modular", 100, 10, "modular_100v_10m"),
            
            # Chain instances
            ("chain", 20, None, "chain_20v"),
            ("chain", 30, None, "chain_30v"),
            ("chain", 40, None, "chain_40v"),
            ("chain", 50, None, "chain_50v"),
            
            # Tree instances
            ("tree", 20, None, "tree_20v"),
            ("tree", 30, None, "tree_30v"),
            ("tree", 40, None, "tree_40v"),
        ]
        
        for cfg in structured_configs:
            cnf_type, num_vars, modules, name = cfg
            output_path = self.output_dir / f"{name}.cnf"
            
            cmd = [
                "python3", "tools/generate_cnf_instances.py",
                "--type", cnf_type,
                "--vars", str(num_vars),
                "--output", str(output_path)
            ]
            
            if modules is not None:
                cmd.extend(["--modules", str(modules)])
            
            subprocess.run(cmd, check=True, capture_output=True)
            instances.append(output_path)
            print(f"  Generated: {output_path.name}")
        
        # Random instances (negative control - should show NO advantage)
        random_configs = [
            (20, "random_20v"),
            (30, "random_30v"),
            (40, "random_40v"),
            (50, "random_50v"),
        ]
        
        for num_vars, name in random_configs:
            output_path = self.output_dir / f"{name}.cnf"
            
            cmd = [
                "python3", "tools/generate_cnf_instances.py",
                "--type", "random",
                "--vars", str(num_vars),
                "--output", str(output_path)
            ]
            
            subprocess.run(cmd, check=True, capture_output=True)
            instances.append(output_path)
            print(f"  Generated: {output_path.name}")
        
        print(f"\nGenerated {len(instances)} test instances")
        return instances
    
    def run_benchmark(self, cnf_path: Path) -> Dict:
        """
        Run benchmark on single instance.
        
        Returns:
            Dictionary with results or None if failed
        """
        print(f"Benchmarking: {cnf_path.name}...", end=" ", flush=True)
        
        try:
            # Run sat_benchmark.py with JSON output
            temp_json = self.output_dir / f"temp_{cnf_path.stem}.json"
            
            cmd = [
                "python3", "tools/sat_benchmark.py",
                str(cnf_path),
                "--output", str(temp_json),
                "--timeout", str(self.timeout)
            ]
            
            result = subprocess.run(
                cmd,
                capture_output=True,
                timeout=self.timeout + 10,
                text=True
            )
            
            if result.returncode != 0:
                print(f"FAILED (exit code {result.returncode})")
                return None
            
            # Load results
            with open(temp_json) as f:
                data = json.load(f)
            
            # Clean up temp file
            temp_json.unlink()
            
            print("OK")
            return data
            
        except subprocess.TimeoutExpired:
            print("TIMEOUT")
            return None
        except Exception as e:
            print(f"ERROR: {e}")
            return None
    
    def run_batch(self, instances: List[Path], output_csv: Path):
        """
        Run benchmarks on all instances and save results.
        """
        print(f"\nRunning batch benchmark on {len(instances)} instances...")
        print(f"Timeout per instance: {self.timeout}s")
        print("=" * 60)
        
        results = []
        success_count = 0
        
        for i, cnf_path in enumerate(instances, 1):
            print(f"[{i}/{len(instances)}] ", end="")
            
            result = self.run_benchmark(cnf_path)
            if result:
                results.append(result)
                success_count += 1
        
        print("=" * 60)
        print(f"Completed: {success_count}/{len(instances)} successful")
        
        # Write to CSV
        if results:
            self.write_csv(results, output_csv)
            print(f"Results saved to: {output_csv}")
        else:
            print("No results to save")
    
    def write_csv(self, results: List[Dict], output_path: Path):
        """Write results to CSV file."""
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_path, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=[
                'instance', 'num_variables', 'num_clauses', 'interaction_density',
                'baseline_runtime', 'baseline_decisions', 'baseline_conflicts', 'baseline_mu_total',
                'sighted_runtime', 'sighted_decisions', 'sighted_conflicts', 'sighted_mu_total', 'sighted_modules',
                'speedup', 'mu_ratio', 'advantage', 'advantage_type'
            ])
            
            writer.writeheader()
            
            for result in results:
                row = {
                    'instance': result['instance_name'],
                    'num_variables': result['num_variables'],
                    'num_clauses': result['num_clauses'],
                    'interaction_density': result['interaction_density'],
                    'baseline_runtime': result['baseline_metrics']['runtime'],
                    'baseline_decisions': result['baseline_metrics']['decisions'],
                    'baseline_conflicts': result['baseline_metrics']['conflicts'],
                    'baseline_mu_total': result['baseline_metrics']['mu_total'],
                    'sighted_runtime': result['sighted_metrics']['runtime'],
                    'sighted_decisions': result['sighted_metrics']['decisions'],
                    'sighted_conflicts': result['sighted_metrics']['conflicts'],
                    'sighted_mu_total': result['sighted_metrics']['mu_total'],
                    'sighted_modules': result['sighted_metrics']['num_modules'],
                    'speedup': result['speedup'],
                    'mu_ratio': result['mu_ratio'],
                    'advantage': result['advantage'],
                    'advantage_type': result['advantage_type']
                }
                writer.writerow(row)


def main():
    parser = argparse.ArgumentParser(
        description="Batch SAT benchmark runner for H2 validation"
    )
    parser.add_argument('--generate', action='store_true', 
                       help='Generate test suite')
    parser.add_argument('--input-dir', type=Path,
                       help='Directory with existing CNF files')
    parser.add_argument('--output', type=Path, required=True,
                       help='Output CSV file')
    parser.add_argument('--timeout', type=int, default=60,
                       help='Timeout per instance (seconds)')
    
    args = parser.parse_args()
    
    benchmark = BatchBenchmark(timeout=args.timeout)
    
    if args.generate:
        # Generate test suite
        instances = benchmark.generate_test_suite()
    elif args.input_dir:
        # Use existing instances
        instances = list(args.input_dir.glob("*.cnf"))
        print(f"Found {len(instances)} CNF files in {args.input_dir}")
    else:
        print("Error: Must specify --generate or --input-dir")
        return 1
    
    if not instances:
        print("No instances to benchmark")
        return 1
    
    # Run batch benchmark
    benchmark.run_batch(instances, args.output)
    
    print("\n" + "=" * 60)
    print("BATCH BENCHMARK COMPLETE")
    print("=" * 60)
    print(f"Results: {args.output}")
    print("\nNext step (B1.4): Analyze results")
    print("  python tools/analyze_sat_results.py", args.output)
    
    return 0


if __name__ == '__main__':
    sys.exit(main())
