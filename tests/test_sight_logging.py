#!/usr/bin/env python3
"""
Integration test for the sight logging system.

This test validates the complete pipeline:
1. Generate sight logs for both structured and chaotic problems
2. Extract geometric signatures
3. Verify classification works

This is a minimal test to ensure the system is working correctly.
"""

import sys
import json
import shutil
from pathlib import Path
import tempfile

# Add repo root to path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from tools.sight_logging import assemble_log, save_log, update_index
from tools.cartographer import generate_atlas
from tools.meta_analyzer import load_atlas, prepare_dataset
import numpy as np


def test_sight_logging():
    """Test that sight logging works for simple problems."""
    print("Testing sight_logging.py...")
    
    # Create a simple SAT problem
    test_clauses = [
        [1, 2, 3],
        [-1, 2],
        [-2, 3],
        [-1, -3]
    ]
    
    log = assemble_log(
        clauses=test_clauses,
        problem_name="test_simple",
        n=3,
        seed=0,
        verdict="CONSISTENT",
        metadata={"test": True}
    )
    
    # Verify log structure
    assert "problem_name" in log
    assert "partitions" in log
    assert "consistency_analysis" in log
    assert "louvain" in log["partitions"]
    assert "spectral" in log["partitions"]
    assert "degree" in log["partitions"]
    assert "balanced" in log["partitions"]
    assert "vi_matrix" in log["consistency_analysis"]
    
    print("  ✓ Sight log structure valid")
    print("  ✓ All four partitioning strategies present")
    print("  ✓ VI matrix computed")


def test_cartographer():
    """Test that cartographer extracts geometric metrics correctly."""
    print("\nTesting cartographer.py...")
    
    # Create a temporary directory for test
    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir_path = Path(tmpdir)
        logs_dir = tmpdir_path / "sight_logs"
        logs_dir.mkdir()
        
        # Generate some test logs
        sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "demos" / "research-demos" / "problem-solving"))
        from attempt import generate_tseitin_expander
        
        for n in [4, 6]:
            for seed in [0, 1]:
                instance = generate_tseitin_expander(n, seed, 123456789, verbose=False, hb_period=3600)
                log = assemble_log(
                    clauses=instance.get("cnf_clauses", []),
                    problem_name=f"test_n{n}_s{seed}",
                    n=n,
                    seed=seed,
                    verdict="CONSISTENT"
                )
                save_log(log, logs_dir)
        
        # Generate atlas
        atlas_path = logs_dir / "atlas" / "phase2_metrics.json"
        atlas = generate_atlas(logs_dir, atlas_path)
        
        # Verify atlas
        assert atlas is not None
        assert "entries" in atlas
        assert len(atlas["entries"]) > 0
        
        # Verify each entry has geometric metrics
        for entry in atlas["entries"]:
            assert "geometric_metrics" in entry
            metrics = entry["geometric_metrics"]
            assert "average_edge_weight" in metrics
            assert "max_edge_weight" in metrics
            assert "edge_weight_stddev" in metrics
            assert "min_spanning_tree_weight" in metrics
            assert "thresholded_density" in metrics
        
        print("  ✓ Atlas generated successfully")
        print(f"  ✓ {len(atlas['entries'])} entries with geometric metrics")


def test_meta_analyzer():
    """Test that meta-analyzer can prepare dataset correctly."""
    print("\nTesting meta_analyzer.py...")
    
    # Create a mock atlas
    mock_atlas = {
        "entries": [
            {
                "problem_name": "test1",
                "verdict": "CONSISTENT",
                "geometric_metrics": {
                    "average_edge_weight": 0.1,
                    "max_edge_weight": 0.2,
                    "edge_weight_stddev": 0.05,
                    "min_spanning_tree_weight": 0.3,
                    "thresholded_density": 0.5
                }
            },
            {
                "problem_name": "test2",
                "verdict": "SPURIOUS",
                "geometric_metrics": {
                    "average_edge_weight": 0.8,
                    "max_edge_weight": 0.9,
                    "edge_weight_stddev": 0.3,
                    "min_spanning_tree_weight": 2.5,
                    "thresholded_density": 0.9
                }
            }
        ]
    }
    
    # Prepare dataset
    features, labels, names = prepare_dataset(mock_atlas)
    
    # Verify
    assert features.shape[0] == 2
    assert features.shape[1] == 5  # Five metrics
    assert len(labels) == 2
    assert len(names) == 2
    assert labels[0] == 1  # CONSISTENT
    assert labels[1] == 0  # SPURIOUS
    
    print("  ✓ Dataset preparation works")
    print(f"  ✓ Feature shape: {features.shape}")
    print(f"  ✓ Labels: {labels}")


def test_complete_pipeline():
    """Test the complete pipeline end-to-end."""
    print("\nTesting complete pipeline...")
    
    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir_path = Path(tmpdir)
        logs_dir = tmpdir_path / "sight_logs"
        logs_dir.mkdir()
        
        # Generate mixed dataset
        sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "demos" / "research-demos" / "problem-solving"))
        from attempt import generate_tseitin_expander
        import random
        
        print("  Generating test dataset...")
        
        # Structured problems
        for n in [4, 6, 8]:
            for seed in [0, 1]:
                instance = generate_tseitin_expander(n, seed, 123456789, verbose=False, hb_period=3600)
                log = assemble_log(
                    clauses=instance.get("cnf_clauses", []),
                    problem_name=f"tseitin_n{n}_s{seed}",
                    n=n,
                    seed=seed,
                    verdict="CONSISTENT"
                )
                save_log(log, logs_dir)
        
        # Chaotic problems
        for n_vars in [10, 15, 20]:
            for seed in [0, 1]:
                random.seed(seed)
                num_clauses = int(n_vars * 4.26)
                clauses = []
                for _ in range(num_clauses):
                    vars_in_clause = random.sample(range(1, n_vars + 1), 3)
                    clause = [v if random.random() < 0.5 else -v for v in vars_in_clause]
                    clauses.append(clause)
                
                log = assemble_log(
                    clauses=clauses,
                    problem_name=f"random3sat_n{n_vars}_s{seed}",
                    n=n_vars,
                    seed=seed,
                    verdict="SPURIOUS"
                )
                save_log(log, logs_dir)
        
        # Generate atlas
        atlas_path = logs_dir / "atlas" / "phase2_metrics.json"
        atlas = generate_atlas(logs_dir, atlas_path)
        
        # Prepare dataset
        features, labels, names = prepare_dataset(atlas)
        
        # Verify we have both classes
        assert 1 in labels  # CONSISTENT
        assert 0 in labels  # SPURIOUS
        assert features.shape[0] == len(labels)
        assert features.shape[1] == 5
        
        # Check that features vary
        assert np.std(features) > 0
        
        print(f"  ✓ Complete pipeline works")
        print(f"  ✓ Generated {len(features)} samples")
        print(f"  ✓ CONSISTENT: {np.sum(labels == 1)}")
        print(f"  ✓ SPURIOUS: {np.sum(labels == 0)}")


def main():
    """Run all tests."""
    print("="*70)
    print("SIGHT LOGGING SYSTEM - Integration Tests")
    print("="*70)
    
    try:
        test_sight_logging()
        test_cartographer()
        test_meta_analyzer()
        test_complete_pipeline()
        
        print("\n" + "="*70)
        print("✓ ALL TESTS PASSED")
        print("="*70)
        return 0
        
    except Exception as e:
        print(f"\n✗ TEST FAILED: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
