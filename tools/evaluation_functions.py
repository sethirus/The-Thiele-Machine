#!/usr/bin/env python3
"""
Evaluation Functions for the Autotelic Engine

This module defines the evaluation functions that can be used to judge
evolved strategies. These functions are referenced by the objective genome.
"""

import networkx as nx
import numpy as np
from typing import Dict, Any, Callable
from pathlib import Path


def evaluate_classification_accuracy(
    strategy_code: str,
    strategy_name: str,
    parameters: Dict[str, Any]
) -> float:
    """
    Evaluate a strategy's classification accuracy.
    
    This is a placeholder implementation that simulates evaluation.
    In a full implementation, this would:
    1. Load test graphs
    2. Run the strategy on them
    3. Measure classification accuracy
    
    Args:
        strategy_code: The Python code of the strategy
        strategy_name: Name of the strategy
        parameters: Parameters from objective genome (model, kernel, etc.)
    
    Returns:
        Fitness score (0.0 to 1.0)
    """
    # Placeholder: randomly evaluate based on strategy complexity
    # In reality, this would run actual classification tests
    
    # Count number of primitives used (simpler = potentially better)
    primitive_count = strategy_code.count('prim_')
    
    # Random base score with some bias toward simpler strategies
    base_score = np.random.random() * 0.5 + 0.3
    
    # Penalize extremely complex strategies
    if primitive_count > 20:
        complexity_penalty = (primitive_count - 20) * 0.01
        base_score = max(0.1, base_score - complexity_penalty)
    
    # Add some variance based on strategy name hash (deterministic)
    name_seed = sum(ord(c) for c in strategy_name) % 100
    variance = (name_seed / 100.0) * 0.2 - 0.1
    
    final_score = np.clip(base_score + variance, 0.0, 1.0)
    
    return final_score


def evaluate_strategy_complexity(
    strategy_code: str,
    strategy_name: str,
    parameters: Dict[str, Any]
) -> float:
    """
    Evaluate strategy complexity (inverse complexity = elegance).
    
    Lower complexity (higher elegance) is better.
    
    Args:
        strategy_code: The Python code of the strategy
        strategy_name: Name of the strategy
        parameters: Parameters including method (e.g., "inverse_primitive_count")
    
    Returns:
        Fitness score (0.0 to 1.0), where 1.0 = most elegant
    """
    method = parameters.get('method', 'inverse_primitive_count')
    
    if method == 'inverse_primitive_count':
        # Count primitives in the code
        primitive_count = strategy_code.count('prim_') + strategy_code.count('PRIMITIVES')
        
        if primitive_count == 0:
            return 0.0  # Degenerate case
        
        # Normalize: fewer primitives = higher score
        # Use logarithmic scale to avoid extreme values
        normalized_count = min(primitive_count, 50)  # Cap at 50
        elegance = 1.0 - (normalized_count / 50.0)
        
        return max(0.0, elegance)
    
    elif method == 'code_length':
        # Measure by lines of code
        lines = strategy_code.split('\n')
        meaningful_lines = [l for l in lines if l.strip() and not l.strip().startswith('#')]
        
        line_count = len(meaningful_lines)
        normalized = min(line_count, 100) / 100.0
        
        return 1.0 - normalized
    
    else:
        # Default: return moderate score
        return 0.5


def weighted_sum(
    strategy_code: str,
    strategy_name: str,
    parameters: Dict[str, Any]
) -> float:
    """
    Evaluate using a weighted sum of multiple component functions.
    
    Args:
        strategy_code: The Python code of the strategy
        strategy_name: Name of the strategy
        parameters: Dict with 'components' key containing weighted sub-objectives
    
    Returns:
        Weighted fitness score (0.0 to 1.0)
    """
    components = parameters.get('components', {})
    
    if not components:
        return 0.0
    
    total_score = 0.0
    total_weight = 0.0
    
    for component_name, component_config in components.items():
        weight = component_config.get('weight', 1.0)
        func_name = component_config.get('function')
        func_params = component_config.get('parameters', {})
        
        if func_name in EVALUATION_FUNCTIONS:
            eval_func = EVALUATION_FUNCTIONS[func_name]
            score = eval_func(strategy_code, strategy_name, func_params)
            total_score += weight * score
            total_weight += weight
    
    if total_weight == 0:
        return 0.0
    
    return total_score / total_weight


# Registry of all evaluation functions
EVALUATION_FUNCTIONS: Dict[str, Callable] = {
    'evaluate_classification_accuracy': evaluate_classification_accuracy,
    'evaluate_strategy_complexity': evaluate_strategy_complexity,
    'weighted_sum': weighted_sum,
}


def get_evaluation_function(name: str) -> Callable:
    """
    Get an evaluation function by name.
    
    Args:
        name: Name of the evaluation function
    
    Returns:
        Evaluation function callable
    
    Raises:
        ValueError: If function name is not recognized
    """
    if name not in EVALUATION_FUNCTIONS:
        raise ValueError(f"Unknown evaluation function: {name}")
    
    return EVALUATION_FUNCTIONS[name]


def evaluate_strategy_with_objective(
    strategy_code: str,
    strategy_name: str,
    objective_genome_path: Path
) -> float:
    """
    Evaluate a strategy using the specified objective genome.
    
    This is the main entry point that the Oracle of Judgment uses.
    
    Args:
        strategy_code: The Python code of the strategy
        strategy_name: Name of the strategy
        objective_genome_path: Path to the objective genome file
    
    Returns:
        Fitness score (0.0 to 1.0)
    """
    import json
    
    # Load objective genome
    with open(objective_genome_path, 'r') as f:
        objective = json.load(f)
    
    # Extract function name and parameters
    func_name = objective.get('function')
    parameters = objective.get('parameters', {})
    
    # Get the evaluation function
    eval_func = get_evaluation_function(func_name)
    
    # Execute evaluation
    fitness = eval_func(strategy_code, strategy_name, parameters)
    
    return fitness
