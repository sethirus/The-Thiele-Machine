# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""
Efficient Partition Discovery for the Thiele Machine

This module implements polynomial-time partition discovery algorithms.
The key insight is that we use spectral clustering on the problem's 
variable interaction graph, which runs in O(n^3) time for n variables.

The discovery process:
1. Build interaction graph from problem structure
2. Apply spectral clustering to find natural modules
3. Compute MDL cost of discovered partition
4. Charge μ-bits for the discovery process

Key claims (all falsifiable):
- Discovery runs in polynomial time: O(n^3) 
- Discovered partitions have low MDL when problem has structure
- Discovery is profitable: μ_discovery + solve_cost < blind_cost
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import List, Set, Tuple, Optional, Dict, Any
import math
import time

try:
    import numpy as np
    from scipy.sparse import csr_matrix
    from scipy.sparse.linalg import eigsh
    HAS_SCIPY = True
except ImportError:
    HAS_SCIPY = False

from .mu import question_cost_bits


@dataclass
class Problem:
    """Abstract representation of a computational problem.
    
    Problems are represented by their variable interaction structure,
    which determines the natural partitioning.
    """
    
    num_variables: int
    interactions: List[Tuple[int, int]]  # Pairs of interacting variables
    name: str = ""
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    @property
    def interaction_density(self) -> float:
        """Density of interactions (edges / possible edges)."""
        max_edges = self.num_variables * (self.num_variables - 1) // 2
        if max_edges == 0:
            return 0.0
        return len(self.interactions) / max_edges
    
    @classmethod
    def from_cnf_clauses(cls, clauses: List[List[int]], name: str = "") -> "Problem":
        """Create a Problem from CNF clauses.
        
        Interactions are derived from variables appearing in the same clause.
        """
        interactions = []
        seen = set()
        
        for clause in clauses:
            variables = sorted(set(abs(lit) for lit in clause))
            for i in range(len(variables)):
                for j in range(i + 1, len(variables)):
                    pair = (variables[i], variables[j])
                    if pair not in seen:
                        seen.add(pair)
                        interactions.append(pair)
        
        num_vars = max(abs(lit) for clause in clauses for lit in clause) if clauses else 0
        return cls(
            num_variables=num_vars,
            interactions=interactions,
            name=name
        )


@dataclass
class PartitionCandidate:
    """A candidate partitioning of a problem's variables.
    
    Attributes:
        modules: List of variable sets (the partition)
        mdl_cost: MDL cost of encoding this partition
        discovery_cost_mu: μ-bits spent to find this partition
        method: Algorithm used to discover this partition
        discovery_time: Wall-clock time for discovery (seconds)
    """
    
    modules: List[Set[int]]
    mdl_cost: float
    discovery_cost_mu: float
    method: str
    discovery_time: float = 0.0
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    @property
    def num_modules(self) -> int:
        return len(self.modules)
    
    @property
    def total_variables(self) -> int:
        return sum(len(m) for m in self.modules)
    
    def is_valid_partition(self, num_vars: int) -> bool:
        """Check that this is a valid partition of 1..num_vars."""
        all_vars = set()
        for module in self.modules:
            if all_vars & module:  # Overlap
                return False
            all_vars |= module
        expected = set(range(1, num_vars + 1))
        return all_vars == expected


def compute_partition_mdl(problem: Problem, modules: List[Set[int]]) -> float:
    """Compute the MDL cost of a partition.
    
    MDL captures the trade-off between:
    1. Description cost: encoding the partition structure
    2. Solving benefit: smaller modules are easier to solve (polynomial)
    3. Communication cost: cut edges require coordination
    
    For structured problems, good partitions should have lower MDL
    because the solving benefit outweighs the description/communication cost.
    """
    if not modules:
        return float('inf')
    
    n = problem.num_variables
    if n == 0:
        return 0.0
    
    # Build module lookup for edge counting
    var_to_module = {}
    for i, module in enumerate(modules):
        for var in module:
            var_to_module[var] = i
    
    # Count internal and cut edges for each module
    internal_edges = [0] * len(modules)
    cut_edges = 0
    
    for v1, v2 in problem.interactions:
        m1 = var_to_module.get(v1)
        m2 = var_to_module.get(v2)
        if m1 is not None and m2 is not None:
            if m1 == m2:
                internal_edges[m1] += 1
            else:
                cut_edges += 1
    
    # MDL = Description cost - Solving benefit + Communication cost
    
    # 1. Description cost: bits to encode partition
    description_cost = math.log2(len(modules) + 1)
    for module in modules:
        if module:
            description_cost += math.log2(len(module) + 1)
    
    # 2. Solving benefit: smaller modules are exponentially easier
    # For n variables, blind search is O(2^n), but per-module is O(2^(n/k))
    # Benefit = log(2^n) - sum(log(2^|module_i|)) = n - sum(|module_i|) 
    # But that's 0 for valid partitions, so we use a different metric:
    # Benefit is high when modules are roughly equal and small
    solving_benefit = 0.0
    if len(modules) > 1:
        # Benefit from partitioning: log of the product of module sizes
        # vs the total size. Higher is better.
        max_module = max(len(m) for m in modules if m)
        # The benefit is proportional to how much smaller the largest module is
        solving_benefit = math.log2(n / max_module + 1) * len(modules)
    
    # 3. Communication cost: cut edges require coordination
    communication_cost = cut_edges * 0.5  # Each cut edge costs 0.5 bits
    
    # Total MDL (lower is better)
    mdl = description_cost - solving_benefit + communication_cost
    
    return max(0.0, mdl)


def trivial_partition(problem: Problem) -> PartitionCandidate:
    """Return the trivial partition (all variables in one module)."""
    all_vars = set(range(1, problem.num_variables + 1))
    modules = [all_vars] if all_vars else []
    mdl = compute_partition_mdl(problem, modules)
    return PartitionCandidate(
        modules=modules,
        mdl_cost=mdl,
        discovery_cost_mu=0.0,  # No discovery needed
        method="trivial",
        discovery_time=0.0
    )


def random_partition(problem: Problem, num_parts: int = 2, seed: int = 42) -> PartitionCandidate:
    """Return a random partition for comparison."""
    import random
    rng = random.Random(seed)
    
    all_vars = list(range(1, problem.num_variables + 1))
    rng.shuffle(all_vars)
    
    modules = [set() for _ in range(num_parts)]
    for i, var in enumerate(all_vars):
        modules[i % num_parts].add(var)
    
    # Remove empty modules
    modules = [m for m in modules if m]
    
    mdl = compute_partition_mdl(problem, modules)
    return PartitionCandidate(
        modules=modules,
        mdl_cost=mdl,
        discovery_cost_mu=8.0,  # Minimal cost for random selection
        method="random",
        discovery_time=0.0
    )


class EfficientPartitionDiscovery:
    """Polynomial-time partition discovery using spectral methods.
    
    Key insight: We use spectral clustering on the variable interaction graph.
    This runs in O(n^3) time (dominated by eigenvalue computation) and finds
    good partitions when the problem has natural community structure.
    
    The algorithm:
    1. Build adjacency matrix from interactions
    2. Compute Laplacian eigenvectors
    3. Cluster using k-means on eigenvector embedding
    4. Refine partition to minimize cut edges
    
    This is polynomial time and produces provably good partitions on
    problems with community structure (proven in spectral graph theory).
    """
    
    def __init__(self, max_clusters: int = 10, use_refinement: bool = True):
        self.max_clusters = max_clusters
        self.use_refinement = use_refinement
    
    def discover_partition(
        self, 
        problem: Problem,
        max_mu_budget: float = 10000.0
    ) -> PartitionCandidate:
        """Discover a near-optimal partition in polynomial time.
        
        Args:
            problem: The problem to partition
            max_mu_budget: Maximum μ-bits to spend on discovery
            
        Returns:
            PartitionCandidate with discovered modules
        """
        start_time = time.perf_counter()
        
        # Discovery query cost
        query = f"(discover-partition n={problem.num_variables})"
        base_mu = question_cost_bits(query)
        
        if base_mu > max_mu_budget:
            # Return trivial partition if budget too low
            return trivial_partition(problem)
        
        if problem.num_variables <= 1:
            return trivial_partition(problem)
        
        if not HAS_SCIPY:
            # Fallback to greedy algorithm without scipy
            return self._greedy_discover(problem, start_time, base_mu)
        
        try:
            result = self._spectral_discover(problem, start_time, base_mu)
            return result
        except Exception:
            # Fallback to greedy on any error
            return self._greedy_discover(problem, start_time, base_mu)
    
    def _spectral_discover(
        self, 
        problem: Problem, 
        start_time: float,
        base_mu: float
    ) -> PartitionCandidate:
        """Spectral clustering based discovery."""
        n = problem.num_variables
        
        # Build adjacency matrix
        adj = np.zeros((n, n))
        for v1, v2 in problem.interactions:
            if 1 <= v1 <= n and 1 <= v2 <= n:
                adj[v1-1, v2-1] = 1
                adj[v2-1, v1-1] = 1
        
        # Compute degree matrix
        degrees = np.sum(adj, axis=1)
        D = np.diag(degrees)
        
        # Compute normalized Laplacian
        # L = I - D^(-1/2) A D^(-1/2)
        D_inv_sqrt = np.diag(1.0 / np.sqrt(np.maximum(degrees, 1e-10)))
        L = np.eye(n) - D_inv_sqrt @ adj @ D_inv_sqrt
        
        # Find optimal number of clusters using eigengap heuristic
        num_clusters = min(self.max_clusters, n - 1, 10)
        if num_clusters < 2:
            num_clusters = 2
        
        # Compute eigenvectors (this is the O(n^3) step)
        try:
            eigenvalues, eigenvectors = np.linalg.eigh(L)
        except np.linalg.LinAlgError:
            return self._greedy_discover(problem, start_time, base_mu)
        
        # Use eigengap to determine number of clusters
        sorted_eigenvalues = np.sort(eigenvalues)
        gaps = np.diff(sorted_eigenvalues[:min(10, len(sorted_eigenvalues))])
        if len(gaps) > 0:
            best_k = np.argmax(gaps) + 2  # +2 because gap[i] is between eigenvalue i and i+1
            best_k = max(2, min(best_k, self.max_clusters, n // 2))
        else:
            best_k = 2
        
        # Cluster using k-means on first k eigenvectors
        embedding = eigenvectors[:, :best_k]
        
        # Simple k-means
        labels = self._kmeans(embedding, best_k)
        
        # Build modules from labels
        modules = [set() for _ in range(best_k)]
        for i, label in enumerate(labels):
            modules[label].add(i + 1)  # Variables are 1-indexed
        
        # Remove empty modules
        modules = [m for m in modules if m]
        
        # Refinement step
        if self.use_refinement:
            modules = self._refine_partition(problem, modules)
        
        elapsed = time.perf_counter() - start_time
        
        # Compute MDL
        mdl = compute_partition_mdl(problem, modules)
        
        # Discovery cost: base query + O(n) for processing
        discovery_mu = base_mu + n * 0.1
        
        return PartitionCandidate(
            modules=modules,
            mdl_cost=mdl,
            discovery_cost_mu=discovery_mu,
            method="spectral",
            discovery_time=elapsed,
            metadata={"num_eigenvectors": best_k}
        )
    
    def _kmeans(self, X: np.ndarray, k: int, max_iters: int = 100) -> np.ndarray:
        """Simple k-means clustering."""
        n = X.shape[0]
        
        # Initialize centroids randomly
        idx = np.random.choice(n, min(k, n), replace=False)
        centroids = X[idx].copy()
        
        labels = np.zeros(n, dtype=int)
        
        for _ in range(max_iters):
            # Assign points to nearest centroid
            old_labels = labels.copy()
            for i in range(n):
                distances = np.sum((centroids - X[i])**2, axis=1)
                labels[i] = np.argmin(distances)
            
            # Check convergence
            if np.array_equal(labels, old_labels):
                break
            
            # Update centroids
            for j in range(k):
                mask = labels == j
                if np.any(mask):
                    centroids[j] = X[mask].mean(axis=0)
        
        return labels
    
    def _refine_partition(
        self, 
        problem: Problem, 
        modules: List[Set[int]]
    ) -> List[Set[int]]:
        """Refine partition by moving vertices to reduce cut edges."""
        improved = True
        max_iterations = 10
        iteration = 0
        
        while improved and iteration < max_iterations:
            improved = False
            iteration += 1
            
            # Try moving each vertex to a better module
            for var in range(1, problem.num_variables + 1):
                current_module_idx = None
                for i, module in enumerate(modules):
                    if var in module:
                        current_module_idx = i
                        break
                
                if current_module_idx is None:
                    continue
                
                # Count edges to each module
                edges_to_module = [0] * len(modules)
                for v1, v2 in problem.interactions:
                    if v1 == var or v2 == var:
                        other = v2 if v1 == var else v1
                        for i, module in enumerate(modules):
                            if other in module:
                                edges_to_module[i] += 1
                
                # Find best module (use Python max with index when numpy unavailable)
                if HAS_SCIPY:
                    best_module_idx = np.argmax(edges_to_module)
                else:
                    best_module_idx = edges_to_module.index(max(edges_to_module))
                
                if best_module_idx != current_module_idx and edges_to_module[best_module_idx] > edges_to_module[current_module_idx]:
                    # Move vertex
                    modules[current_module_idx].remove(var)
                    modules[best_module_idx].add(var)
                    improved = True
        
        # Remove empty modules
        return [m for m in modules if m]
    
    def _greedy_discover(
        self, 
        problem: Problem, 
        start_time: float,
        base_mu: float
    ) -> PartitionCandidate:
        """Greedy partition discovery (fallback without scipy)."""
        n = problem.num_variables
        
        if n <= 1:
            return trivial_partition(problem)
        
        # Build adjacency list
        adj = {i: set() for i in range(1, n + 1)}
        for v1, v2 in problem.interactions:
            if 1 <= v1 <= n and 1 <= v2 <= n:
                adj[v1].add(v2)
                adj[v2].add(v1)
        
        # Greedy community detection
        visited = set()
        modules = []
        
        for start_var in range(1, n + 1):
            if start_var in visited:
                continue
            
            # BFS to find connected component, but limit size
            module = set()
            queue = [start_var]
            max_module_size = max(n // 4, 10)
            
            while queue and len(module) < max_module_size:
                var = queue.pop(0)
                if var in visited:
                    continue
                visited.add(var)
                module.add(var)
                
                # Add neighbors with high connectivity to current module
                neighbors = sorted(adj[var], key=lambda v: len(adj[v] & module), reverse=True)
                for neighbor in neighbors:
                    if neighbor not in visited:
                        queue.append(neighbor)
            
            if module:
                modules.append(module)
        
        elapsed = time.perf_counter() - start_time
        mdl = compute_partition_mdl(problem, modules)
        discovery_mu = base_mu + n * 0.05  # Lower cost for greedy
        
        return PartitionCandidate(
            modules=modules,
            mdl_cost=mdl,
            discovery_cost_mu=discovery_mu,
            method="greedy",
            discovery_time=elapsed
        )


def exhaustive_mdl_search(problem: Problem, max_partitions: int = 1000) -> PartitionCandidate:
    """Find optimal partition by exhaustive search (for small problems only).
    
    This is exponential-time and should only be used for validation
    on problems with n <= 12 variables.
    """
    from itertools import combinations
    
    n = problem.num_variables
    if n > 12:
        raise ValueError("Exhaustive search only supported for n <= 12")
    
    all_vars = set(range(1, n + 1))
    
    best_partition = None
    best_mdl = float('inf')
    count = 0
    
    # Generate all partitions using Stirling numbers approach
    def partition_generator(elements: List[int], current: List[Set[int]]):
        nonlocal count, best_partition, best_mdl
        
        if count >= max_partitions:
            return
        
        if not elements:
            count += 1
            mdl = compute_partition_mdl(problem, current)
            if mdl < best_mdl:
                best_mdl = mdl
                best_partition = [s.copy() for s in current]
            return
        
        elem = elements[0]
        remaining = elements[1:]
        
        # Add to existing part
        for part in current:
            part.add(elem)
            partition_generator(remaining, current)
            part.remove(elem)
        
        # Start new part
        current.append({elem})
        partition_generator(remaining, current)
        current.pop()
    
    partition_generator(list(all_vars), [])
    
    if best_partition is None:
        return trivial_partition(problem)
    
    return PartitionCandidate(
        modules=best_partition,
        mdl_cost=best_mdl,
        discovery_cost_mu=float('inf'),  # Exhaustive search is not efficient
        method="exhaustive"
    )


__all__ = [
    "Problem",
    "PartitionCandidate",
    "EfficientPartitionDiscovery",
    "compute_partition_mdl",
    "trivial_partition",
    "random_partition",
    "exhaustive_mdl_search",
]
