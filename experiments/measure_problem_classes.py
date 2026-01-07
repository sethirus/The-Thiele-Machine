#!/usr/bin/env python3
"""
Experimental Framework for Characterizing Problem Classes by μ-Cost

Goal: Discover which problems have intrinsic structural complexity.

Hypothesis: Problem classes cluster in μ-cost space, revealing a new
complexity hierarchy based on structural information rather than time.
"""

from typing import List, Dict, Any, Callable, Tuple
from dataclasses import dataclass
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).parent.parent))

from demos.structure_microscope import StructureMicroscope


@dataclass
class ProblemClass:
    """Definition of a computational problem class for measurement."""
    name: str
    generator: Callable[[int, Dict[str, Any]], Any]  # (size, params) -> instance
    classical_solver: Callable[[Any], Any]
    thiele_solver_template: str  # Code with INSTANCE_PLACEHOLDER
    feature_extractor: Callable[[Any], Dict[str, float]]  # Extract structural features
    size_range: List[int]
    parameter_space: Dict[str, List[Any]]


def generate_sorting_instance(size: int, params: Dict[str, Any]) -> List[int]:
    """Generate sorting instances with varying structure."""
    import random
    
    structure = params.get('structure', 'random')
    
    if structure == 'random':
        return [random.randint(1, size * 10) for _ in range(size)]
    elif structure == 'nearly_sorted':
        arr = list(range(1, size + 1))
        # Swap a few elements
        swaps = max(1, size // 10)
        for _ in range(swaps):
            i, j = random.randint(0, size - 1), random.randint(0, size - 1)
            arr[i], arr[j] = arr[j], arr[i]
        return arr
    elif structure == 'reversed':
        return list(range(size, 0, -1))
    elif structure == 'many_duplicates':
        return [random.randint(1, size // 3) for _ in range(size)]
    else:
        return list(range(1, size + 1))


def generate_sat_instance(size: int, params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate SAT instances with varying clause/variable ratios."""
    import random
    
    n_vars = size
    clause_ratio = params.get('clause_ratio', 4.3)  # Classic phase transition point
    n_clauses = int(n_vars * clause_ratio)
    
    clauses = []
    for _ in range(n_clauses):
        # Random 3-SAT clause
        variables = random.sample(range(1, n_vars + 1), 3)
        clause = [(v if random.random() > 0.5 else -v) for v in variables]
        clauses.append(clause)
    
    return {'n_vars': n_vars, 'clauses': clauses}


def generate_graph_instance(size: int, params: Dict[str, Any]) -> Dict[int, List[int]]:
    """Generate graphs with varying density and modularity."""
    import random
    
    n_nodes = size
    edge_prob = params.get('edge_prob', 0.3)
    modularity = params.get('modularity', 1)  # Number of modules
    
    # Divide nodes into modules
    module_size = n_nodes // modularity
    adj_list = {i: [] for i in range(n_nodes)}
    
    for i in range(n_nodes):
        for j in range(i + 1, n_nodes):
            # Higher probability for edges within same module
            same_module = (i // module_size) == (j // module_size)
            prob = edge_prob * 3 if same_module else edge_prob / 3
            
            if random.random() < prob:
                adj_list[i].append(j)
                adj_list[j].append(i)
    
    return adj_list


def extract_sorting_features(instance: List[int]) -> Dict[str, float]:
    """Extract structural features from sorting instance."""
    import math
    
    n = len(instance)
    
    # Count inversions
    inversions = sum(
        1 for i in range(n) for j in range(i + 1, n) 
        if instance[i] > instance[j]
    )
    
    # Count runs (sorted subsequences)
    runs = 1
    for i in range(1, n):
        if instance[i] < instance[i - 1]:
            runs += 1
    
    # Count unique values
    unique = len(set(instance))
    
    return {
        'size': n,
        'inversions': inversions,
        'inversion_ratio': inversions / (n * (n - 1) / 2) if n > 1 else 0,
        'runs': runs,
        'unique_ratio': unique / n,
        'entropy': math.log2(unique) if unique > 0 else 0
    }


def extract_graph_features(instance: Dict[int, List[int]]) -> Dict[str, float]:
    """Extract structural features from graph instance."""
    import math
    
    n_nodes = len(instance)
    n_edges = sum(len(neighbors) for neighbors in instance.values()) // 2
    
    # Calculate degree distribution
    degrees = [len(neighbors) for neighbors in instance.values()]
    avg_degree = sum(degrees) / n_nodes if n_nodes > 0 else 0
    max_degree = max(degrees) if degrees else 0
    
    # Density
    max_edges = n_nodes * (n_nodes - 1) / 2
    density = n_edges / max_edges if max_edges > 0 else 0
    
    # Clustering coefficient (simple approximation)
    # For each node, count triangles
    triangles = 0
    for node in instance:
        neighbors = set(instance[node])
        for n1 in neighbors:
            for n2 in neighbors:
                if n1 < n2 and n2 in instance.get(n1, []):
                    triangles += 1
    
    return {
        'size': n_nodes,
        'edges': n_edges,
        'density': density,
        'avg_degree': avg_degree,
        'max_degree': max_degree,
        'triangles': triangles,
        'clustering': triangles / n_edges if n_edges > 0 else 0
    }


# Define problem classes to measure
PROBLEM_CLASSES = {
    'Sorting': ProblemClass(
        name='Sorting',
        generator=generate_sorting_instance,
        classical_solver=lambda arr: sorted(arr),
        thiele_solver_template="""
import math
arr = INSTANCE_PLACEHOLDER
inversions = sum(1 for i in range(len(arr)) for j in range(i+1, len(arr)) if arr[i] > arr[j])
mu_discovery = math.log2(inversions + 1)
result = sorted(arr)
""",
        feature_extractor=extract_sorting_features,
        size_range=[10, 20, 50, 100],
        parameter_space={
            'structure': ['random', 'nearly_sorted', 'reversed', 'many_duplicates']
        }
    ),
    
    'Graph_BFS': ProblemClass(
        name='Graph_BFS',
        generator=generate_graph_instance,
        classical_solver=lambda g: len(set(g.keys())),  # Simplified
        thiele_solver_template="""
import math
adj_list = INSTANCE_PLACEHOLDER
n_nodes = len(adj_list)
n_edges = sum(len(neighbors) for neighbors in adj_list.values()) // 2
mu_discovery = math.log2(n_nodes) + math.log2(n_edges + 1)
result = n_nodes
""",
        feature_extractor=extract_graph_features,
        size_range=[10, 20, 50],
        parameter_space={
            'edge_prob': [0.1, 0.3, 0.5, 0.8],
            'modularity': [1, 2, 4]
        }
    )
}


def run_problem_class_experiment(
    problem_class: ProblemClass,
    n_instances_per_config: int = 5
) -> Dict[str, Any]:
    """
    Measure μ-cost distribution for a problem class.
    
    Returns comprehensive measurements for later analysis.
    """
    microscope = StructureMicroscope()
    measurements = []
    
    print(f"\n{'=' * 80}")
    print(f"MEASURING: {problem_class.name}")
    print(f"{'=' * 80}")
    
    # Generate parameter combinations
    import itertools
    param_keys = list(problem_class.parameter_space.keys())
    param_values = [problem_class.parameter_space[k] for k in param_keys]
    param_combinations = list(itertools.product(*param_values))
    
    total_configs = len(problem_class.size_range) * len(param_combinations) * n_instances_per_config
    current = 0
    
    for size in problem_class.size_range:
        for param_combo in param_combinations:
            params = dict(zip(param_keys, param_combo))
            
            for instance_num in range(n_instances_per_config):
                current += 1
                
                # Generate instance
                instance = problem_class.generator(size, params)
                features = problem_class.feature_extractor(instance)
                
                # Inject instance into solver code
                thiele_code = problem_class.thiele_solver_template.replace(
                    'INSTANCE_PLACEHOLDER', 
                    repr(instance)
                )
                
                # Measure
                measurement = microscope.measure_problem(
                    problem_class.name,
                    instance,
                    problem_class.classical_solver,
                    thiele_code,
                    {**features, **params, 'instance_num': instance_num}
                )
                
                measurements.append(measurement)
                
                # Progress
                print(f"[{current}/{total_configs}] "
                      f"size={size}, params={params}, "
                      f"μ={measurement['mu_discovery']:.2f}")
    
    return {
        'problem_class': problem_class.name,
        'measurements': measurements,
        'summary': microscope.analyze_problem_class(problem_class.name)
    }


def analyze_correlations(results: Dict[str, Any]) -> Dict[str, Any]:
    """
    Find correlations between problem features and μ-cost.
    
    This answers: "Can we predict μ from problem structure?"
    """
    measurements = results['measurements']
    
    if not measurements:
        return {'error': 'No measurements to analyze'}
    
    # Extract features and μ-costs
    import numpy as np
    
    # Collect all feature names
    feature_names = set()
    for m in measurements:
        feature_names.update(m['features'].keys())
    
    # Build feature matrix
    feature_matrix = []
    mu_costs = []
    
    for m in measurements:
        features = m['features']
        row = [features.get(fname, 0) for fname in sorted(feature_names)]
        feature_matrix.append(row)
        mu_costs.append(m['mu_discovery'])
    
    X = np.array(feature_matrix)
    y = np.array(mu_costs)
    
    # Calculate correlation coefficients
    correlations = {}
    for i, fname in enumerate(sorted(feature_names)):
        if len(set(X[:, i])) > 1:  # Skip constant features
            corr = np.corrcoef(X[:, i], y)[0, 1]
            if not np.isnan(corr):
                correlations[fname] = corr
    
    # Sort by absolute correlation
    sorted_corr = sorted(
        correlations.items(), 
        key=lambda x: abs(x[1]), 
        reverse=True
    )
    
    return {
        'correlations': dict(sorted_corr),
        'n_samples': len(measurements),
        'feature_names': sorted(feature_names)
    }


def main():
    """Run the complete experimental suite."""
    print("=" * 80)
    print("PROBLEM CLASS CHARACTERIZATION EXPERIMENTS")
    print("Goal: Discover μ-cost signatures for different computational problems")
    print("=" * 80)
    
    all_results = {}
    
    for problem_name, problem_class in PROBLEM_CLASSES.items():
        results = run_problem_class_experiment(problem_class, n_instances_per_config=3)
        all_results[problem_name] = results
        
        # Analyze correlations
        correlations = analyze_correlations(results)
        
        print(f"\n{'─' * 80}")
        print(f"CORRELATIONS for {problem_name}:")
        print(f"{'─' * 80}")
        
        if 'correlations' in correlations:
            for feature, corr in list(correlations['correlations'].items())[:5]:
                print(f"  {feature:20s}: r = {corr:+.3f}")
        
        print(f"\nSUMMARY:")
        summary = results['summary']
        if 'error' not in summary:
            print(f"  Mean μ: {summary['mu_discovery']['mean']:.2f} "
                  f"± {summary['mu_discovery']['stdev']:.2f}")
            print(f"  Range: [{summary['mu_discovery']['min']:.2f}, "
                  f"{summary['mu_discovery']['max']:.2f}]")
    
    # Save results
    output_path = Path(__file__).parent.parent / 'results' / 'problem_class_measurements.json'
    output_path.parent.mkdir(exist_ok=True)
    
    # Convert to JSON-serializable format
    json_results = {
        name: {
            'problem_class': r['problem_class'],
            'summary': r['summary'],
            'n_measurements': len(r['measurements'])
        }
        for name, r in all_results.items()
    }
    
    with open(output_path, 'w') as f:
        json.dump(json_results, f, indent=2)
    
    print(f"\n{'=' * 80}")
    print(f"Results saved to: {output_path}")
    print(f"{'=' * 80}")
    print("\nNEXT STEPS:")
    print("1. Look for problem classes that cluster in μ-cost space")
    print("2. Find features that predict μ (structure → complexity)")
    print("3. Search for phase transitions (sudden μ changes)")
    print("4. Compare to classical complexity classes (P, NP, etc.)")


if __name__ == '__main__':
    main()
