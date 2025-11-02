#!/usr/bin/env python3
"""
Tests for the Autotelic Engine components.

These tests validate the three phases:
- Phase 15: Objective genome loading and evaluation
- Phase 16: Critic analysis
- Phase 17: Purpose synthesis
"""

import json
import tempfile
import pytest
from pathlib import Path
from tools.evaluation_functions import (
    evaluate_classification_accuracy,
    evaluate_strategy_complexity,
    weighted_sum,
    get_evaluation_function,
    evaluate_strategy_with_objective
)
from tools.critic import (
    analyze_value_discovery,
    analyze_bias_detection,
    analyze_stagnation,
    run_critic_analysis
)
from tools.purpose_synthesizer import synthesize_new_objective


class TestPhase15ObjectiveGenome:
    """Test Phase 15: The Genome of Purpose"""
    
    def test_load_objective_genome(self):
        """Test that objective genome can be loaded."""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.thiele', delete=False) as f:
            objective = {
                "name": "Test Objective",
                "function": "evaluate_classification_accuracy",
                "parameters": {"model": "SVM"}
            }
            json.dump(objective, f)
            temp_path = Path(f.name)
        
        try:
            # Evaluate with this objective
            strategy_code = "# Test strategy\nprim_get_nodes()"
            fitness = evaluate_strategy_with_objective(
                strategy_code,
                "test_strategy",
                temp_path
            )
            
            assert isinstance(fitness, float)
            assert 0.0 <= fitness <= 1.0
        finally:
            temp_path.unlink()
    
    def test_evaluation_function_registry(self):
        """Test that evaluation functions can be retrieved by name."""
        func = get_evaluation_function("evaluate_classification_accuracy")
        assert callable(func)
        
        func = get_evaluation_function("evaluate_strategy_complexity")
        assert callable(func)
        
        with pytest.raises(ValueError):
            get_evaluation_function("nonexistent_function")
    
    def test_complexity_evaluation(self):
        """Test strategy complexity evaluation."""
        simple_code = "prim_get_nodes()"
        complex_code = "\n".join([f"prim_step_{i}()" for i in range(30)])
        
        simple_fitness = evaluate_strategy_complexity(
            simple_code, "simple", {"method": "inverse_primitive_count"}
        )
        complex_fitness = evaluate_strategy_complexity(
            complex_code, "complex", {"method": "inverse_primitive_count"}
        )
        
        # Simpler strategies should have higher elegance scores
        assert simple_fitness > complex_fitness
    
    def test_weighted_sum_evaluation(self):
        """Test weighted sum of multiple objectives."""
        strategy_code = "prim_get_nodes()\nprim_kmeans()"
        
        parameters = {
            "components": {
                "accuracy": {
                    "weight": 0.7,
                    "function": "evaluate_classification_accuracy",
                    "parameters": {}
                },
                "elegance": {
                    "weight": 0.3,
                    "function": "evaluate_strategy_complexity",
                    "parameters": {"method": "inverse_primitive_count"}
                }
            }
        }
        
        fitness = weighted_sum(strategy_code, "test", parameters)
        assert isinstance(fitness, float)
        assert 0.0 <= fitness <= 1.0


class TestPhase16Critic:
    """Test Phase 16: The Engine of Introspection"""
    
    def create_sample_ledger(self, size=10):
        """Create a sample ascension ledger for testing."""
        ledger = []
        for i in range(size):
            entry = {
                "timestamp": f"2024-01-01T00:00:{i:02d}",
                "strategy_name": f"strategy_{i}",
                "strategy_dna": [
                    "GET_NODES = prim_get_nodes(G)",
                    "LAPLACIAN = prim_laplacian_matrix(G, nodes)"
                ],
                "generation": i // 3,
                "parent_strategies": [f"parent_{i-1}"] if i > 0 else [],
                "objective_genome": {
                    "name": "Test Objective",
                    "function": "evaluate_classification_accuracy"
                },
                "fitness_score": 0.5 + (i * 0.03),  # Gradually improving
                "primitive_count": 5,
                "metadata": {"mutation_type": "replace" if i % 2 else "insert"}
            }
            ledger.append(entry)
        return ledger
    
    def test_value_discovery(self):
        """Test that value discovery identifies top primitives."""
        ledger = self.create_sample_ledger(20)
        
        result = analyze_value_discovery(ledger, top_n=3)
        
        assert "primitives" in result
        assert isinstance(result["primitives"], list)
        assert "insight" in result
        assert "high_fitness_threshold" in result
    
    def test_bias_detection(self):
        """Test that bias detection finds dead ends."""
        ledger = self.create_sample_ledger(20)
        
        result = analyze_bias_detection(ledger)
        
        assert "dead_ends" in result
        assert isinstance(result["dead_ends"], list)
        assert "insight" in result
        assert "avg_parent_child_change" in result
    
    def test_stagnation_detection_progressive(self):
        """Test stagnation detection with improving fitness."""
        ledger = []
        for i in range(20):
            entry = {
                "strategy_name": f"strategy_{i}",
                "strategy_dna": [],
                "fitness_score": 0.5 + (i * 0.02),  # Steadily improving
                "generation": i,
                "parent_strategies": [],
                "primitive_count": 5,
                "metadata": {}
            }
            ledger.append(entry)
        
        result = analyze_stagnation(ledger, window_size=10)
        
        assert "stagnation_detected" in result
        assert "improvement_rate" in result
        # Should not detect stagnation when fitness is improving
        assert result["improvement_rate"] > 0
    
    def test_stagnation_detection_flat(self):
        """Test stagnation detection with flat fitness."""
        ledger = []
        for i in range(20):
            entry = {
                "strategy_name": f"strategy_{i}",
                "strategy_dna": [],
                "fitness_score": 0.8,  # Flat fitness
                "generation": i,
                "parent_strategies": [],
                "primitive_count": 5,
                "metadata": {}
            }
            ledger.append(entry)
        
        result = analyze_stagnation(ledger, window_size=10)
        
        # Should detect stagnation when fitness is flat
        assert result["stagnation_detected"] or result["at_local_max"]
        assert result["recommended_action"] is not None


class TestPhase17PurposeSynthesis:
    """Test Phase 17: The Metamorphosis"""
    
    def test_synthesize_new_objective_no_stagnation(self):
        """Test that objective remains unchanged when no stagnation."""
        critic_report = {
            "stagnation_analysis": {
                "stagnation_detected": False,
                "at_local_max": False,
                "improvement_rate": 0.05
            }
        }
        
        current_objective = {
            "name": "Test v1.0",
            "function": "evaluate_classification_accuracy",
            "parameters": {}
        }
        
        new_objective = synthesize_new_objective(critic_report, current_objective)
        
        # Should return unchanged objective
        assert new_objective == current_objective
    
    def test_synthesize_new_objective_with_stagnation(self):
        """Test that new objective is created when stagnation detected."""
        critic_report = {
            "stagnation_analysis": {
                "stagnation_detected": True,
                "at_local_max": True,
                "improvement_rate": 0.0001,
                "recommended_action": {
                    "action": "introduce_new_metric",
                    "suggested_metric": "elegance"
                }
            }
        }
        
        current_objective = {
            "name": "Accuracy v1.0",
            "function": "evaluate_classification_accuracy",
            "parameters": {"model": "SVM"}
        }
        
        new_objective = synthesize_new_objective(critic_report, current_objective, version=2)
        
        # Should create weighted sum objective
        assert new_objective["function"] == "weighted_sum"
        assert "components" in new_objective["parameters"]
        assert "accuracy" in new_objective["parameters"]["components"]
        assert "elegance" in new_objective["parameters"]["components"]
    
    def test_synthesize_adds_to_existing_weighted_sum(self):
        """Test that synthesis can add components to existing weighted sum."""
        critic_report = {
            "stagnation_analysis": {
                "stagnation_detected": True,
                "recommended_action": {
                    "action": "introduce_new_metric",
                    "suggested_metric": "elegance"
                }
            }
        }
        
        current_objective = {
            "name": "Multi v1.0",
            "function": "weighted_sum",
            "parameters": {
                "components": {
                    "accuracy": {
                        "weight": 1.0,
                        "function": "evaluate_classification_accuracy"
                    }
                }
            }
        }
        
        new_objective = synthesize_new_objective(critic_report, current_objective, version=2)
        
        # Should add elegance to existing components
        components = new_objective["parameters"]["components"]
        assert "accuracy" in components
        assert "elegance" in components
        # Weights should be rebalanced
        assert components["accuracy"]["weight"] < 1.0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
