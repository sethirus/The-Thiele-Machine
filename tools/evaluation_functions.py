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


def evaluate_riemann_search(
    strategy_code: str,
    strategy_name: str,
    parameters: Dict[str, Any]
) -> float:
    """
    Evaluate a strategy's ability to find counterexamples to the Riemann Hypothesis.
    
    This is THE objective: find a zero of the Riemann zeta function that is
    NOT on the critical line Re(s) = 0.5.
    
    Fitness is based on:
    - Finding points with low |ζ(s)| (potential zeros)
    - Deviation from critical line
    - Computational efficiency (μ-cost proxy)
    
    Args:
        strategy_code: The search strategy code
        strategy_name: Name of the strategy
        parameters: Search parameters (im_range_start, im_range_end, etc.)
    
    Returns:
        Fitness score (0.0 to 1.0), where 1.0 = found counterexample
    """
    from thielecpu.riemann_primitives import (
        prim_structured_search,
        prim_verify_counterexample,
        ComplexPoint
    )
    
    # Extract search parameters
    im_start = parameters.get('im_range_start', 14.0)
    im_end = parameters.get('im_range_end', 50.0)
    off_line_sigma = parameters.get('off_line_sigma', 0.51)
    
    # Simulate the search based on strategy characteristics
    # In a full implementation, we would execute the strategy code
    # For now, we evaluate based on strategy properties
    
    # Count search-related primitives
    search_prims = strategy_code.count('STRUCTURED_SEARCH') + \
                   strategy_code.count('ADAPTIVE_SEARCH') + \
                   strategy_code.count('GRID_SEARCH')
    
    refinement_prims = strategy_code.count('REFINE_ZERO')
    verification_prims = strategy_code.count('VERIFY_COUNTEREXAMPLE')
    
    # Base score on having appropriate search primitives
    base_score = 0.3
    
    if search_prims > 0:
        base_score += 0.2
    if refinement_prims > 0:
        base_score += 0.2
    if verification_prims > 0:
        base_score += 0.1
    
    # Penalize overly complex strategies (want efficient search)
    complexity = strategy_code.count('prim_')
    if complexity > 15:
        base_score *= 0.8
    
    # Add variance based on strategy name (deterministic but varied)
    name_seed = sum(ord(c) for c in strategy_name) % 100
    variance = (name_seed / 100.0) * 0.2 - 0.1
    
    final_score = np.clip(base_score + variance, 0.0, 0.95)
    
    # Note: A score of 1.0 would mean a verified counterexample found
    # We cap at 0.95 for simulation, as finding a real counterexample
    # would be a monumental discovery
    
    return final_score


def evaluate_strategy_minimality(
    strategy_code: str,
    strategy_name: str,
    parameters: Dict[str, Any]
) -> float:
    """
    Evaluate a strategy's minimality - the simplest form that retains power.
    
    This is the "Minimize Self" objective - find the genesis axiom.
    The goal is to discover the irreducible core algorithm.
    
    Args:
        strategy_code: The Python code of the strategy
        strategy_name: Name of the strategy
        parameters: Parameters including preserve_effectiveness flag
    
    Returns:
        Fitness score (0.0 to 1.0), where 1.0 = maximally minimal
    """
    preserve_effectiveness = parameters.get('preserve_effectiveness', True)
    
    # Count various complexity metrics
    lines = strategy_code.split('\n')
    meaningful_lines = [l for l in lines if l.strip() and not l.strip().startswith('#')]
    line_count = len(meaningful_lines)
    
    # Count primitives
    primitive_count = strategy_code.count('prim_') + strategy_code.count('PRIMITIVES')
    
    # Count control structures (if, for, while)
    control_count = sum([
        strategy_code.count('if '),
        strategy_code.count('for '),
        strategy_code.count('while ')
    ])
    
    # Total complexity score
    total_complexity = line_count + primitive_count * 2 + control_count * 3
    
    # Normalize (assuming 100 is a reasonable baseline)
    if total_complexity == 0:
        return 0.0  # Degenerate case
    
    minimality = 1.0 / (1.0 + np.log(total_complexity + 1))
    
    # If we need to preserve effectiveness, penalize if strategy seems too simple
    if preserve_effectiveness and line_count < 3:
        minimality *= 0.5  # Too simple to be effective
    
    return minimality


# Registry of all evaluation functions
EVALUATION_FUNCTIONS: Dict[str, Callable] = {
    'evaluate_classification_accuracy': evaluate_classification_accuracy,
    'evaluate_strategy_complexity': evaluate_strategy_complexity,
    'evaluate_strategy_minimality': evaluate_strategy_minimality,
    'weighted_sum': weighted_sum,
    'evaluate_riemann_search': evaluate_riemann_search,
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
