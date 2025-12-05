#!/usr/bin/env python3
"""
Program Analysis via Thiele Machine Partition Discovery

This module applies partition discovery to program dependency graphs to find
natural module boundaries. It analyzes Python programs and compares the
discovered structure with manual decompositions.

The goal is to validate H2 (Structural Advantage) in the program analysis domain
by showing that μ-minimization discovers meaningful program structure.

Metrics:
- Module quality: Cohesion within modules, coupling between modules
- Similarity to manual decomposition: How well auto-discovered matches human design
- μ-cost: Information-theoretic cost of discovery

Copyright 2025 Devon Thiele
Licensed under the Apache License, Version 2.0
"""

from __future__ import annotations

import argparse
import ast
import csv
import json
import os
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

import networkx as nx

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from thielecpu.discovery import Problem, EfficientPartitionDiscovery


@dataclass
class ProgramModule:
    """A module in the program structure."""
    name: str
    functions: Set[str]
    
    def __hash__(self):
        return hash(self.name)


@dataclass
class ProgramAnalysisResult:
    """Result of program analysis."""
    program_name: str
    num_functions: int
    num_dependencies: int
    discovered_modules: List[Set[str]]
    manual_modules: Optional[List[Set[str]]]
    cohesion: float
    coupling: float
    similarity: Optional[float]  # Similarity to manual decomposition
    mu_cost: float
    runtime: float
    
    def to_dict(self) -> Dict:
        """Convert to dictionary for CSV export."""
        return {
            'program': self.program_name,
            'num_functions': self.num_functions,
            'num_dependencies': self.num_dependencies,
            'num_modules': len(self.discovered_modules),
            'cohesion': self.cohesion,
            'coupling': self.coupling,
            'similarity': self.similarity if self.similarity is not None else float('nan'),
            'mu_cost': self.mu_cost,
            'runtime': self.runtime
        }


class ProgramDependencyExtractor(ast.NodeVisitor):
    """Extract function call dependencies from Python AST."""
    
    def __init__(self):
        self.functions: Set[str] = set()
        self.dependencies: List[Tuple[str, str]] = []
        self.current_function: Optional[str] = None
    
    def visit_FunctionDef(self, node: ast.FunctionDef):
        """Visit function definition."""
        self.functions.add(node.name)
        old_function = self.current_function
        self.current_function = node.name
        self.generic_visit(node)
        self.current_function = old_function
    
    def visit_Call(self, node: ast.Call):
        """Visit function call."""
        if self.current_function is not None:
            # Extract called function name
            if isinstance(node.func, ast.Name):
                called = node.func.id
                if called != self.current_function:  # Avoid self-loops
                    self.dependencies.append((self.current_function, called))
        self.generic_visit(node)


def extract_dependencies(file_path: Path) -> Tuple[Set[str], List[Tuple[str, str]]]:
    """
    Extract function call dependencies from a Python file.
    
    Returns:
        (functions, dependencies) where dependencies are (caller, callee) pairs
    """
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            source = f.read()
        
        tree = ast.parse(source, filename=str(file_path))
        extractor = ProgramDependencyExtractor()
        extractor.visit(tree)
        
        return extractor.functions, extractor.dependencies
    except (SyntaxError, UnicodeDecodeError) as e:
        print(f"Warning: Could not parse {file_path}: {e}")
        return set(), []


def build_dependency_graph(
    functions: Set[str],
    dependencies: List[Tuple[str, str]]
) -> nx.DiGraph:
    """Build directed dependency graph."""
    G = nx.DiGraph()
    G.add_nodes_from(functions)
    
    # Only add edges between functions that exist
    for caller, callee in dependencies:
        if caller in functions and callee in functions:
            G.add_edge(caller, callee)
    
    return G


def compute_cohesion_coupling(
    G: nx.DiGraph,
    modules: List[Set[str]]
) -> Tuple[float, float]:
    """
    Compute cohesion (within-module edges) and coupling (between-module edges).
    
    Cohesion: Ratio of internal edges to possible internal edges
    Coupling: Ratio of external edges to possible external edges
    """
    # Build module membership
    func_to_module = {}
    for module_id, module in enumerate(modules):
        for func in module:
            func_to_module[func] = module_id
    
    internal_edges = 0
    external_edges = 0
    possible_internal = 0
    possible_external = 0
    
    for module_id, module in enumerate(modules):
        module_list = list(module)
        n = len(module_list)
        if n > 1:
            possible_internal += n * (n - 1)
        
        for other_id, other_module in enumerate(modules):
            if other_id != module_id:
                possible_external += len(module) * len(other_module)
    
    for u, v in G.edges():
        if u in func_to_module and v in func_to_module:
            if func_to_module[u] == func_to_module[v]:
                internal_edges += 1
            else:
                external_edges += 1
    
    cohesion = internal_edges / possible_internal if possible_internal > 0 else 0.0
    coupling = external_edges / possible_external if possible_external > 0 else 0.0
    
    return cohesion, coupling


def compute_similarity_to_manual(
    discovered: List[Set[str]],
    manual: List[Set[str]]
) -> float:
    """
    Compute similarity between discovered and manual decompositions.
    
    Uses Jaccard similarity averaged over all pairs.
    """
    if not manual or not discovered:
        return 0.0
    
    # Compute best matching for each discovered module
    similarities = []
    for disc_module in discovered:
        best_sim = 0.0
        for manual_module in manual:
            intersection = len(disc_module & manual_module)
            union = len(disc_module | manual_module)
            if union > 0:
                sim = intersection / union
                best_sim = max(best_sim, sim)
        similarities.append(best_sim)
    
    return sum(similarities) / len(similarities) if similarities else 0.0


def analyze_program(
    file_path: Path,
    manual_modules: Optional[List[Set[str]]] = None
) -> ProgramAnalysisResult:
    """
    Analyze a Python program to discover module structure.
    """
    import time
    start_time = time.time()
    
    # Extract dependencies
    functions, dependencies = extract_dependencies(file_path)
    
    if len(functions) < 2:
        # Too small to analyze
        return ProgramAnalysisResult(
            program_name=file_path.name,
            num_functions=len(functions),
            num_dependencies=len(dependencies),
            discovered_modules=[functions] if functions else [],
            manual_modules=manual_modules,
            cohesion=0.0,
            coupling=0.0,
            similarity=None,
            mu_cost=0.0,
            runtime=time.time() - start_time
        )
    
    # Build dependency graph
    G = build_dependency_graph(functions, dependencies)
    
    # Convert to undirected for partition discovery
    G_undirected = G.to_undirected()
    
    # Map function names to indices
    func_list = list(functions)
    func_to_idx = {func: idx for idx, func in enumerate(func_list)}
    
    # Create Problem for partition discovery
    interactions = []
    for u, v in G_undirected.edges():
        if u in func_to_idx and v in func_to_idx:
            interactions.append((func_to_idx[u], func_to_idx[v]))
    
    problem = Problem(
        num_variables=len(func_list),
        interactions=interactions,
        name=file_path.stem
    )
    
    # Discover partition
    discovery = EfficientPartitionDiscovery()
    candidate = discovery.discover_partition(problem, max_mu_budget=1000.0)
    
    # Convert indices back to function names
    discovered_modules = []
    for module in candidate.modules:
        func_module = {func_list[idx] for idx in module if idx < len(func_list)}
        if func_module:
            discovered_modules.append(func_module)
    
    runtime = time.time() - start_time
    
    # Compute metrics
    cohesion, coupling = compute_cohesion_coupling(G, discovered_modules)
    mu_cost = candidate.mdl_cost + candidate.discovery_cost_mu
    similarity = None
    if manual_modules is not None:
        similarity = compute_similarity_to_manual(discovered_modules, manual_modules)
    
    return ProgramAnalysisResult(
        program_name=file_path.name,
        num_functions=len(functions),
        num_dependencies=len(dependencies),
        discovered_modules=discovered_modules,
        manual_modules=manual_modules,
        cohesion=cohesion,
        coupling=coupling,
        similarity=similarity,
        mu_cost=mu_cost,
        runtime=runtime
    )


def analyze_directory(
    directory: Path,
    output_file: Path,
    manual_decompositions: Optional[Dict[str, List[Set[str]]]] = None
):
    """
    Analyze all Python files in a directory.
    """
    print("="*60)
    print("PROGRAM ANALYSIS BENCHMARKS")
    print("="*60)
    
    results = []
    
    # Find all Python files
    python_files = list(directory.rglob("*.py"))
    
    # Filter out test files and __init__.py
    python_files = [
        f for f in python_files
        if not f.name.startswith("test_") and f.name != "__init__.py"
    ]
    
    print(f"\nFound {len(python_files)} Python files to analyze")
    
    for file_path in python_files[:10]:  # Limit to first 10 for speed
        print(f"\n{'='*60}")
        print(f"Analyzing: {file_path.relative_to(directory)}")
        print(f"{'='*60}")
        
        # Get manual decomposition if available
        manual = None
        if manual_decompositions and file_path.name in manual_decompositions:
            manual = manual_decompositions[file_path.name]
        
        result = analyze_program(file_path, manual)
        
        print(f"Functions: {result.num_functions}")
        print(f"Dependencies: {result.num_dependencies}")
        print(f"Discovered modules: {len(result.discovered_modules)}")
        print(f"Cohesion: {result.cohesion:.4f}")
        print(f"Coupling: {result.coupling:.4f}")
        if result.similarity is not None:
            print(f"Similarity to manual: {result.similarity:.4f}")
        print(f"μ-cost: {result.mu_cost:.2f} bits")
        print(f"Runtime: {result.runtime:.4f}s")
        
        results.append(result)
    
    # Save results
    output_file.parent.mkdir(parents=True, exist_ok=True)
    with open(output_file, 'w', newline='') as f:
        if results:
            fieldnames = list(results[0].to_dict().keys())
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            for result in results:
                writer.writerow(result.to_dict())
    
    print(f"\n{'='*60}")
    print(f"Results saved to: {output_file}")
    print(f"{'='*60}")
    
    # Summary statistics
    if results:
        print("\nSUMMARY STATISTICS")
        print("="*60)
        
        avg_cohesion = sum(r.cohesion for r in results) / len(results)
        avg_coupling = sum(r.coupling for r in results) / len(results)
        avg_mu = sum(r.mu_cost for r in results) / len(results)
        
        print(f"Average cohesion: {avg_cohesion:.4f}")
        print(f"Average coupling: {avg_coupling:.4f}")
        print(f"Average μ-cost: {avg_mu:.2f} bits")
        
        # Similarity stats (if any)
        results_with_sim = [r for r in results if r.similarity is not None]
        if results_with_sim:
            avg_sim = sum(r.similarity for r in results_with_sim) / len(results_with_sim)
            print(f"Average similarity to manual: {avg_sim:.4f}")


def main():
    parser = argparse.ArgumentParser(description='Program analysis benchmarks')
    parser.add_argument(
        '--directory',
        type=Path,
        default=Path('thielecpu'),
        help='Directory containing Python files to analyze'
    )
    parser.add_argument(
        '--output',
        type=Path,
        default=Path('benchmarks/program_analysis_results.csv'),
        help='Output CSV file for results'
    )
    
    args = parser.parse_args()
    
    # For demonstration, we don't have manual decompositions
    # In practice, these would be provided by domain experts
    manual_decompositions = None
    
    analyze_directory(args.directory, args.output, manual_decompositions)


if __name__ == '__main__':
    main()
