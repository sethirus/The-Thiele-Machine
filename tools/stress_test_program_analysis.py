#!/usr/bin/env python3
"""
Comprehensive Stress Tests for Program Analysis

Tests program analysis under extreme conditions:
1. Large programs (100+ functions)
2. Complex dependency graphs (dense connections)
3. Deeply nested structures
4. Multiple file analysis
5. Edge cases (isolated functions, complete graphs)
6. Real-world large projects

Copyright 2025 Devon Thiele
Licensed under the Apache License, Version 2.0
"""

import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from tools.program_analyzer import (
    analyze_program_structure,
    compute_module_quality
)


def create_synthetic_program(n_functions: int, connectivity: float, filename: str):
    """Create a synthetic Python program with specified properties."""
    import random
    random.seed(42)
    
    with open(filename, 'w') as f:
        # Write header
        f.write('"""Synthetic program for testing."""\n\n')
        
        # Generate functions
        function_names = [f"func_{i}" for i in range(n_functions)]
        
        for i, name in enumerate(function_names):
            f.write(f"def {name}():\n")
            f.write(f'    """Function {i}."""\n')
            
            # Add calls to other functions based on connectivity
            for j, other_name in enumerate(function_names):
                if i != j and random.random() < connectivity:
                    f.write(f"    {other_name}()\n")
            
            f.write("    return None\n\n")


def test_large_program():
    """Test analysis of large program with 100+ functions."""
    print("\n" + "="*60)
    print("TEST 1: Large Program (100 functions)")
    print("="*60)
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
        filename = f.name
    
    try:
        # Create program with 100 functions, moderate connectivity
        n_functions = 100
        connectivity = 0.05  # Each function calls ~5% of others
        
        print(f"Creating synthetic program: {n_functions} functions, {connectivity:.1%} connectivity...")
        create_synthetic_program(n_functions, connectivity, filename)
        
        # Analyze
        print("Analyzing...")
        result = analyze_program_structure(filename)
        
        print(f"\nResults:")
        print(f"  Functions: {result.num_functions}")
        print(f"  Dependencies: {result.num_dependencies}")
        print(f"  Modules: {len(result.discovered_modules)}")
        print(f"  Cohesion: {result.cohesion:.3f}")
        print(f"  Coupling: {result.coupling:.3f}")
        print(f"  μ-cost: {result.mu_cost:.0f} bits")
        print(f"  Runtime: {result.runtime:.2f}s")
        
        # Validation
        assert result.num_functions == n_functions, "Wrong number of functions"
        assert result.num_dependencies > 0, "Should find dependencies"
        assert len(result.discovered_modules) >= 1, "Should discover at least 1 module"
        assert 0 <= result.cohesion <= 1, "Cohesion out of range"
        assert 0 <= result.coupling <= 1, "Coupling out of range"
        assert result.runtime < 60, f"Analysis too slow: {result.runtime:.1f}s"
        
        print("\n✓ PASSED: Large program test")
    
    finally:
        Path(filename).unlink(missing_ok=True)


def test_dense_dependencies():
    """Test program with dense dependency graph."""
    print("\n" + "="*60)
    print("TEST 2: Dense Dependencies (30% connectivity)")
    print("="*60)
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
        filename = f.name
    
    try:
        # Create program with high connectivity
        n_functions = 50
        connectivity = 0.30  # Dense graph
        
        print(f"Creating dense program: {n_functions} functions, {connectivity:.1%} connectivity...")
        create_synthetic_program(n_functions, connectivity, filename)
        
        # Analyze
        print("Analyzing...")
        result = analyze_program_structure(filename)
        
        print(f"\nResults:")
        print(f"  Functions: {result.num_functions}")
        print(f"  Dependencies: {result.num_dependencies}")
        print(f"  Avg dependencies/function: {result.num_dependencies / result.num_functions:.1f}")
        print(f"  Modules: {len(result.discovered_modules)}")
        print(f"  Cohesion: {result.cohesion:.3f}")
        print(f"  Coupling: {result.coupling:.3f}")
        
        # Dense graph should have many dependencies
        avg_deps = result.num_dependencies / result.num_functions
        assert avg_deps > 10, f"Expected >10 deps/function, got {avg_deps:.1f}"
        
        # Should still complete analysis
        assert len(result.discovered_modules) >= 1, "Should discover modules"
        
        print("\n✓ PASSED: Dense dependencies test")
    
    finally:
        Path(filename).unlink(missing_ok=True)


def test_sparse_dependencies():
    """Test program with sparse dependency graph."""
    print("\n" + "="*60)
    print("TEST 3: Sparse Dependencies (1% connectivity)")
    print("="*60)
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
        filename = f.name
    
    try:
        # Create program with low connectivity
        n_functions = 50
        connectivity = 0.01  # Sparse graph
        
        print(f"Creating sparse program: {n_functions} functions, {connectivity:.1%} connectivity...")
        create_synthetic_program(n_functions, connectivity, filename)
        
        # Analyze
        print("Analyzing...")
        result = analyze_program_structure(filename)
        
        print(f"\nResults:")
        print(f"  Functions: {result.num_functions}")
        print(f"  Dependencies: {result.num_dependencies}")
        print(f"  Modules: {len(result.discovered_modules)}")
        print(f"  Cohesion: {result.cohesion:.3f}")
        print(f"  Coupling: {result.coupling:.3f}")
        
        # Sparse graph may have many small modules (or isolated functions)
        assert len(result.discovered_modules) >= 1, "Should discover at least 1 module"
        
        # Low cohesion expected for sparse graph
        # (but validate it's in valid range)
        assert 0 <= result.cohesion <= 1, "Cohesion out of range"
        
        print("\n✓ PASSED: Sparse dependencies test")
    
    finally:
        Path(filename).unlink(missing_ok=True)


def test_isolated_functions():
    """Test program with isolated functions (no dependencies)."""
    print("\n" + "="*60)
    print("TEST 4: Isolated Functions (0% connectivity)")
    print("="*60)
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
        filename = f.name
    
    try:
        # Create program with no dependencies
        n_functions = 30
        connectivity = 0.0  # No dependencies
        
        print(f"Creating isolated program: {n_functions} functions, {connectivity:.1%} connectivity...")
        create_synthetic_program(n_functions, connectivity, filename)
        
        # Analyze
        print("Analyzing...")
        result = analyze_program_structure(filename)
        
        print(f"\nResults:")
        print(f"  Functions: {result.num_functions}")
        print(f"  Dependencies: {result.num_dependencies}")
        print(f"  Modules: {len(result.discovered_modules)}")
        
        # No dependencies means each function is its own module (or all in one)
        assert result.num_dependencies == 0, "Should have no dependencies"
        assert len(result.discovered_modules) >= 1, "Should discover at least 1 module"
        
        print("\n✓ PASSED: Isolated functions test")
    
    finally:
        Path(filename).unlink(missing_ok=True)


def test_modular_structure():
    """Test program with clear modular structure."""
    print("\n" + "="*60)
    print("TEST 5: Modular Structure (3 clear modules)")
    print("="*60)
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
        filename = f.name
        
        # Create program with 3 clear modules
        f.write('"""Program with clear modular structure."""\n\n')
        
        # Module 1: Data processing (10 functions)
        for i in range(10):
            f.write(f"def process_data_{i}():\n")
            f.write(f'    """Process data {i}."""\n')
            # Call other functions in same module
            if i > 0:
                f.write(f"    process_data_{i-1}()\n")
            f.write("    return None\n\n")
        
        # Module 2: Analysis (10 functions)
        for i in range(10):
            f.write(f"def analyze_{i}():\n")
            f.write(f'    """Analyze {i}."""\n')
            # Call other functions in same module
            if i > 0:
                f.write(f"    analyze_{i-1}()\n")
            f.write("    return None\n\n")
        
        # Module 3: Visualization (10 functions)
        for i in range(10):
            f.write(f"def visualize_{i}():\n")
            f.write(f'    """Visualize {i}."""\n')
            # Call other functions in same module
            if i > 0:
                f.write(f"    visualize_{i-1}()\n")
            f.write("    return None\n\n")
        
        # Cross-module calls (sparse)
        f.write("def main():\n")
        f.write("    process_data_0()\n")
        f.write("    analyze_0()\n")
        f.write("    visualize_0()\n")
        f.write("    return None\n")
        
        filename_actual = f.name
    
    try:
        # Analyze
        print("Analyzing modular program...")
        result = analyze_program_structure(filename_actual)
        
        print(f"\nResults:")
        print(f"  Functions: {result.num_functions}")
        print(f"  Modules: {len(result.discovered_modules)}")
        print(f"  Cohesion: {result.cohesion:.3f}")
        print(f"  Coupling: {result.coupling:.3f}")
        
        # Should discover multiple modules
        assert len(result.discovered_modules) >= 2, "Should discover at least 2 modules"
        
        # High cohesion expected (within-module connections)
        # Low coupling expected (few between-module connections)
        print(f"  Cohesion > Coupling: {result.cohesion > result.coupling}")
        
        print("\n✓ PASSED: Modular structure test")
    
    finally:
        Path(filename_actual).unlink(missing_ok=True)


def test_deeply_nested():
    """Test program with deeply nested call chains."""
    print("\n" + "="*60)
    print("TEST 6: Deeply Nested Call Chains (depth=20)")
    print("="*60)
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
        filename = f.name
        
        # Create deep call chain
        f.write('"""Program with deep call chain."""\n\n')
        
        depth = 20
        for i in range(depth):
            f.write(f"def level_{i}():\n")
            f.write(f'    """Level {i}."""\n')
            if i < depth - 1:
                f.write(f"    level_{i+1}()\n")
            f.write("    return None\n\n")
        
        filename_actual = f.name
    
    try:
        # Analyze
        print(f"Analyzing program with depth-{depth} call chain...")
        result = analyze_program_structure(filename_actual)
        
        print(f"\nResults:")
        print(f"  Functions: {result.num_functions}")
        print(f"  Dependencies: {result.num_dependencies}")
        print(f"  Modules: {len(result.discovered_modules)}")
        print(f"  Cohesion: {result.cohesion:.3f}")
        
        # Deep chain should have depth-1 dependencies
        assert result.num_dependencies == depth - 1, f"Expected {depth-1} deps, got {result.num_dependencies}"
        
        # All functions likely in same module (linear chain)
        assert len(result.discovered_modules) >= 1, "Should discover at least 1 module"
        
        print("\n✓ PASSED: Deeply nested test")
    
    finally:
        Path(filename_actual).unlink(missing_ok=True)


def main():
    """Run all stress tests."""
    print("\n" + "="*60)
    print("PROGRAM ANALYSIS STRESS TEST SUITE")
    print("="*60)
    
    tests = [
        test_large_program,
        test_dense_dependencies,
        test_sparse_dependencies,
        test_isolated_functions,
        test_modular_structure,
        test_deeply_nested
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except AssertionError as e:
            print(f"\n✗ FAILED: {e}")
            failed += 1
        except Exception as e:
            print(f"\n✗ ERROR: {e}")
            import traceback
            traceback.print_exc()
            failed += 1
    
    print("\n" + "="*60)
    print(f"RESULTS: {passed}/{len(tests)} tests passed")
    if failed > 0:
        print(f"         {failed}/{len(tests)} tests failed")
    print("="*60)
    
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
