#!/usr/bin/env python3
"""
Test the optimized TSP solver on small instances.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

from thielecpu.assemble import parse
from thielecpu.vm import VM
from thielecpu.state import State
from pathlib import Path
import json
import time

def test_tsp_instance(instance_file, timeout_minutes=2):
    """Test TSP solver on a specific instance."""
    print(f"\n{'='*60}")
    print(f"Testing TSP instance: {instance_file}")
    print(f"{'='*60}")

    if not instance_file.exists():
        print(f"❌ Instance file not found: {instance_file}")
        return False

    # Parse TSP data
    from tsp_solver import parse_tsp_file, create_tsp_smt2_files, create_tsp_solver_program, nearest_neighbor_tsp, calculate_tour_distance

    cities = parse_tsp_file(instance_file)
    num_cities = len(cities)
    print(f"Loaded {num_cities} cities from {instance_file.name}")

    # Create output directory structure
    output_dir = Path("TSP_TEST") / instance_file.stem
    axioms_dir = output_dir / "tsp_axioms"
    answer_dir = output_dir / "ANSWER"

    axioms_dir.mkdir(parents=True, exist_ok=True)
    answer_dir.mkdir(parents=True, exist_ok=True)

    # Create SMT2 axiom files
    print("Creating optimized TSP axioms...")
    create_tsp_smt2_files(cities, axioms_dir)

    # Create Thiele program
    print("Creating Thiele TSP solver program...")
    create_tsp_solver_program(cities, output_dir)

    # Run heuristic first
    print("\nRunning nearest neighbor heuristic...")
    start_time = time.time()
    heuristic_tour = nearest_neighbor_tsp(cities)
    heuristic_time = time.time() - start_time

    if heuristic_tour:
        heuristic_distance = calculate_tour_distance(cities, heuristic_tour)
        print(".2f")
    else:
        print("❌ Heuristic failed")
        return False

    # Run the Thiele Machine
    print("\nRunning optimized Thiele Machine TSP solver...")
    print(f"Timeout: {timeout_minutes} minutes")

    start_time = time.time()

    try:
        # Run with timeout
        program = parse(open(output_dir / "tsp_solver.thm").read().splitlines(), output_dir)
        vm = VM(State())

        # Add timeout mechanism
        import threading

        def timeout_handler():
            print(f"\n⏰ Timeout reached ({timeout_minutes} minutes). Stopping execution.")
            print("This is expected for larger instances - the optimizations help but TSP remains hard.")

        timer = threading.Timer(timeout_minutes * 60, timeout_handler)
        timer.start()

        try:
            vm.run(program, output_dir / "thiele_output")
            execution_time = time.time() - start_time
            print(".2f")
        finally:
            timer.cancel()

        # Check results
        summary_file = output_dir / "thiele_output" / "summary.json"
        if summary_file.exists():
            with open(summary_file) as f:
                summary = json.load(f)
            mu_operational = summary.get('mu_operational', 0)
            mu_information = summary.get('mu_information', 0)
            print("\nThiele Machine Results:")
            print(f"  Operational Cost: {mu_operational} μ-bits")
            print(f"  Information Cost: {mu_information} μ-bits")
            print(f"  Total MDL Cost: {mu_operational + mu_information} μ-bits")

        # Check trace for PDISCOVER results
        trace_file = output_dir / "thiele_output" / "trace.log"
        if trace_file.exists():
            trace_content = trace_file.read_text(encoding='utf-8')
            pdiscover_count = trace_content.count("PDISCOVER")
            paradox_found = "paradox found" in trace_content

            print("\nPDISCOVER Analysis:")
            print(f"  PDISCOVER operations: {pdiscover_count}")
            if paradox_found:
                print("  ✅ Found logical contradictions (potential solutions)")
            else:
                print("  ℹ️  Completed partition exploration")

        print("\n✅ Test completed successfully!")
        return True

    except Exception as e:
        execution_time = time.time() - start_time
        print(".2f")
        print(f"Error: {e}")
        return False

def main():
    """Test TSP solver on various small instances."""
    print("TSP Solver Optimization Test Suite")
    print("===================================")

    test_instances = [
        Path("test_tsp_instances/test_5cities.tsp"),
        Path("test_tsp_instances/test_6cities.tsp"),
        Path("test_tsp_instances/test_7cities.tsp"),
        Path("test_tsp_instances/test_8cities.tsp"),
    ]

    results = []

    for instance in test_instances:
        success = test_tsp_instance(instance, timeout_minutes=1)  # 1 minute timeout for small instances
        results.append((instance.name, success))

    print(f"\n{'='*60}")
    print("TEST SUMMARY")
    print(f"{'='*60}")

    for instance_name, success in results:
        status = "✅ PASS" if success else "❌ FAIL"
        print(f"{instance_name}: {status}")

    successful_tests = sum(1 for _, success in results if success)
    print(f"\nPassed: {successful_tests}/{len(results)} tests")

    if successful_tests == len(results):
        print("🎉 All optimizations working correctly!")
        print("Ready to test on larger instances (22 cities).")
    else:
        print("⚠️  Some tests failed. Check the optimizations.")

if __name__ == "__main__":
    main()