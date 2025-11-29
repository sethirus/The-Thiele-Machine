# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
Test Suite for Practical Examples

Validates that all demonstrations:
1. Run without errors
2. Produce verifiable results
3. Show isomorphism between Standard Python and Thiele VM
"""

import pytest
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))

from demos.practical_examples.run_all_demonstrations import (
    run_search_demonstration,
    run_sorting_demonstration,
    run_fibonacci_demonstration,
    run_prime_demonstration,
    analyze_all_results,
    DemonstrationResult,
)


class TestSearchDemonstration:
    """Test search algorithms demonstration."""
    
    def test_runs_without_error(self):
        """Demonstration executes successfully."""
        result = run_search_demonstration()
        assert isinstance(result, DemonstrationResult)
        assert result.name == "Search Algorithms"
    
    def test_produces_measurements(self):
        """Produces non-empty measurements."""
        result = run_search_demonstration()
        assert len(result.measurements) > 0
        assert len(result.comparisons) > 0
    
    def test_all_values_match(self):
        """All values match between environments."""
        result = run_search_demonstration()
        assert result.derived_metrics['all_values_match'] == True
    
    def test_all_ops_match(self):
        """All operation counts match between environments."""
        result = run_search_demonstration()
        assert result.derived_metrics['all_ops_match'] == True
    
    def test_binary_faster_than_linear(self):
        """Binary search uses fewer operations than linear."""
        result = run_search_demonstration()
        ratio = result.derived_metrics['ops_ratio']
        assert ratio > 1, f"Expected binary to be faster, got ratio {ratio}"


class TestSortingDemonstration:
    """Test sorting algorithms demonstration."""
    
    def test_runs_without_error(self):
        """Demonstration executes successfully."""
        result = run_sorting_demonstration()
        assert isinstance(result, DemonstrationResult)
        assert result.name == "Sorting Algorithms"
    
    def test_produces_measurements(self):
        """Produces non-empty measurements."""
        result = run_sorting_demonstration()
        assert len(result.measurements) > 0
        assert len(result.comparisons) > 0
    
    def test_all_values_match(self):
        """All values match between environments."""
        result = run_sorting_demonstration()
        assert result.derived_metrics['all_values_match'] == True
    
    def test_all_ops_match(self):
        """All operation counts match between environments."""
        result = run_sorting_demonstration()
        assert result.derived_metrics['all_ops_match'] == True


class TestFibonacciDemonstration:
    """Test Fibonacci demonstration."""
    
    def test_runs_without_error(self):
        """Demonstration executes successfully."""
        result = run_fibonacci_demonstration()
        assert isinstance(result, DemonstrationResult)
        assert result.name == "Fibonacci"
    
    def test_produces_measurements(self):
        """Produces non-empty measurements."""
        result = run_fibonacci_demonstration()
        assert len(result.measurements) > 0
        assert len(result.comparisons) > 0
    
    def test_all_values_match(self):
        """All values match between environments."""
        result = run_fibonacci_demonstration()
        assert result.derived_metrics['all_values_match'] == True
    
    def test_all_ops_match(self):
        """All operation counts match between environments."""
        result = run_fibonacci_demonstration()
        assert result.derived_metrics['all_ops_match'] == True
    
    def test_ops_linear_in_n(self):
        """Operations are linear in n for DP approach."""
        result = run_fibonacci_demonstration()
        assert result.derived_metrics['ops_linear_in_n'] == True


class TestPrimeDemonstration:
    """Test prime generation demonstration."""
    
    def test_runs_without_error(self):
        """Demonstration executes successfully."""
        result = run_prime_demonstration()
        assert isinstance(result, DemonstrationResult)
        assert result.name == "Prime Generation"
    
    def test_produces_measurements(self):
        """Produces non-empty measurements."""
        result = run_prime_demonstration()
        assert len(result.measurements) > 0
        assert len(result.comparisons) > 0
    
    def test_all_values_match(self):
        """All values match between environments."""
        result = run_prime_demonstration()
        assert result.derived_metrics['all_values_match'] == True
    
    def test_all_ops_match(self):
        """All operation counts match between environments."""
        result = run_prime_demonstration()
        assert result.derived_metrics['all_ops_match'] == True


class TestAggregateAnalysis:
    """Test aggregate analysis across all demonstrations."""
    
    def test_analysis_runs(self):
        """Analysis completes without error."""
        results = [
            run_search_demonstration(),
            run_sorting_demonstration(),
            run_fibonacci_demonstration(),
            run_prime_demonstration(),
        ]
        analysis = analyze_all_results(results)
        assert 'aggregate' in analysis
        assert 'derived_conclusions' in analysis
    
    def test_full_isomorphism(self):
        """Full isomorphism rate is 100%."""
        results = [
            run_search_demonstration(),
            run_sorting_demonstration(),
            run_fibonacci_demonstration(),
            run_prime_demonstration(),
        ]
        analysis = analyze_all_results(results)
        assert analysis['aggregate']['full_isomorphism_rate'] == 1.0
    
    def test_mu_tracking(self):
        """μ-cost is tracked for all VM executions."""
        results = [
            run_search_demonstration(),
            run_sorting_demonstration(),
            run_fibonacci_demonstration(),
            run_prime_demonstration(),
        ]
        analysis = analyze_all_results(results)
        
        # Find μ tracking conclusion
        mu_conclusions = [c for c in analysis['derived_conclusions'] if c['type'] == 'MU_TRACKING']
        assert len(mu_conclusions) > 0
        assert mu_conclusions[0]['falsified'] == False
    
    def test_conclusions_are_falsifiable(self):
        """All conclusions are marked as falsifiable."""
        results = [
            run_search_demonstration(),
            run_sorting_demonstration(),
            run_fibonacci_demonstration(),
            run_prime_demonstration(),
        ]
        analysis = analyze_all_results(results)
        
        for conclusion in analysis['derived_conclusions']:
            assert conclusion['falsifiable'] == True


class TestMeasurementIntegrity:
    """Test measurement data integrity."""
    
    def test_all_measurements_have_operations(self):
        """All measurements include operation counts."""
        results = [
            run_search_demonstration(),
            run_sorting_demonstration(),
            run_fibonacci_demonstration(),
            run_prime_demonstration(),
        ]
        
        for result in results:
            for m in result.measurements:
                assert m.operations >= 0, f"Missing operations for {m.algorithm}"
    
    def test_vm_measurements_have_mu_cost(self):
        """Thiele VM measurements include μ-cost."""
        results = [
            run_search_demonstration(),
            run_sorting_demonstration(),
            run_fibonacci_demonstration(),
            run_prime_demonstration(),
        ]
        
        for result in results:
            for m in result.measurements:
                if m.runtime == "Thiele VM":
                    assert m.mu_cost > 0, f"Missing μ-cost for {m.algorithm}"
    
    def test_standard_python_no_mu_cost(self):
        """Standard Python measurements don't have μ-cost."""
        results = [
            run_search_demonstration(),
            run_sorting_demonstration(),
            run_fibonacci_demonstration(),
            run_prime_demonstration(),
        ]
        
        for result in results:
            for m in result.measurements:
                if m.runtime == "Standard Python":
                    assert m.mu_cost == 0, f"Unexpected μ-cost for {m.algorithm}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
