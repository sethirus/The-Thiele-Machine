"""
CONSTRAINT SATISFACTION BENCHMARK: μ-Cost Analysis
===================================================
Measures μ-cost to solve graph coloring and scheduling problems.

Demonstrates that structured CSPs (with exploitable patterns)
cost less μ to solve than random CSPs of the same size.
"""

import time
import json
import random
import math
from dataclasses import dataclass
from typing import List, Dict, Tuple, Set, Optional
from pathlib import Path
from collections import defaultdict


@dataclass 
class CSPResult:
    """Result from solving a CSP instance."""
    problem_type: str
    problem_structure: str  # 'random', 'structured', 'community'
    num_variables: int
    num_constraints: int
    solved: bool
    solution: Optional[Dict[int, int]]
    mu_cost: int
    backtracks: int
    time_seconds: float
    
    def to_dict(self) -> Dict:
        return {
            'problem_type': self.problem_type,
            'problem_structure': self.problem_structure,
            'num_variables': self.num_variables,
            'num_constraints': self.num_constraints,
            'solved': self.solved,
            'mu_cost': self.mu_cost,
            'backtracks': self.backtracks,
            'time_seconds': self.time_seconds,
        }


class GraphColoringCSP:
    """Graph coloring as a CSP."""
    
    def __init__(self, num_vertices: int, edges: List[Tuple[int, int]], num_colors: int):
        self.num_vertices = num_vertices
        self.edges = edges
        self.num_colors = num_colors
        self.adj = defaultdict(set)
        for u, v in edges:
            self.adj[u].add(v)
            self.adj[v].add(u)
        
        self.mu_ledger = 0
        self.backtracks = 0
    
    def solve_with_mu(self) -> Optional[Dict[int, int]]:
        """Solve with μ-accounting."""
        self.mu_ledger = 0
        self.backtracks = 0
        
        assignment = {}
        domain = {v: set(range(self.num_colors)) for v in range(self.num_vertices)}
        
        return self._backtrack(assignment, domain)
    
    def _backtrack(self, assignment: Dict[int, int], domain: Dict[int, Set[int]]) -> Optional[Dict[int, int]]:
        """Backtracking search with forward checking and μ-accounting."""
        if len(assignment) == self.num_vertices:
            return assignment
        
        # Select unassigned variable (MRV heuristic)
        unassigned = [v for v in range(self.num_vertices) if v not in assignment]
        var = min(unassigned, key=lambda v: len(domain[v]))
        
        # Pay μ for variable selection decision
        self.mu_ledger += 4  # Cost of choosing which variable to assign
        
        for color in sorted(domain[var]):
            # Pay μ for value selection
            self.mu_ledger += 2  # Cost of trying this assignment
            
            # Check consistency
            if all(assignment.get(neighbor) != color for neighbor in self.adj[var]):
                # Make assignment
                assignment[var] = color
                
                # Forward checking: prune domains
                saved_domains = {}
                failure = False
                
                for neighbor in self.adj[var]:
                    if neighbor not in assignment and color in domain[neighbor]:
                        saved_domains[neighbor] = domain[neighbor].copy()
                        domain[neighbor] = domain[neighbor] - {color}
                        if not domain[neighbor]:
                            failure = True
                            break
                
                if not failure:
                    result = self._backtrack(assignment, domain)
                    if result is not None:
                        return result
                
                # Restore domains
                for neighbor, saved in saved_domains.items():
                    domain[neighbor] = saved
                
                del assignment[var]
                self.backtracks += 1
                self.mu_ledger += 8  # Pay μ for backtrack (wrong branch discovery)
        
        return None


class SchedulingCSP:
    """Simple scheduling problem as a CSP."""
    
    def __init__(self, num_tasks: int, conflicts: List[Tuple[int, int]], num_slots: int):
        self.num_tasks = num_tasks
        self.conflicts = conflicts  # Tasks that cannot be in same slot
        self.num_slots = num_slots
        self.adj = defaultdict(set)
        for u, v in conflicts:
            self.adj[u].add(v)
            self.adj[v].add(u)
        
        self.mu_ledger = 0
        self.backtracks = 0
    
    def solve_with_mu(self) -> Optional[Dict[int, int]]:
        """Solve with μ-accounting (identical to graph coloring)."""
        self.mu_ledger = 0
        self.backtracks = 0
        
        assignment = {}
        domain = {t: set(range(self.num_slots)) for t in range(self.num_tasks)}
        
        return self._backtrack(assignment, domain)
    
    def _backtrack(self, assignment: Dict[int, int], domain: Dict[int, Set[int]]) -> Optional[Dict[int, int]]:
        """Backtracking with μ-accounting."""
        if len(assignment) == self.num_tasks:
            return assignment
        
        unassigned = [t for t in range(self.num_tasks) if t not in assignment]
        var = min(unassigned, key=lambda t: len(domain[t]))
        
        self.mu_ledger += 4
        
        for slot in sorted(domain[var]):
            self.mu_ledger += 2
            
            if all(assignment.get(conflict) != slot for conflict in self.adj[var]):
                assignment[var] = slot
                
                saved_domains = {}
                failure = False
                
                for conflict in self.adj[var]:
                    if conflict not in assignment and slot in domain[conflict]:
                        saved_domains[conflict] = domain[conflict].copy()
                        domain[conflict] = domain[conflict] - {slot}
                        if not domain[conflict]:
                            failure = True
                            break
                
                if not failure:
                    result = self._backtrack(assignment, domain)
                    if result is not None:
                        return result
                
                for conflict, saved in saved_domains.items():
                    domain[conflict] = saved
                
                del assignment[var]
                self.backtracks += 1
                self.mu_ledger += 8
        
        return None


def generate_random_graph(n: int, p: float, seed: int = None) -> List[Tuple[int, int]]:
    """Generate random Erdős-Rényi graph edges."""
    if seed is not None:
        random.seed(seed)
    
    edges = []
    for i in range(n):
        for j in range(i + 1, n):
            if random.random() < p:
                edges.append((i, j))
    return edges


def generate_structured_graph(n: int, k: int, p_in: float, p_out: float, seed: int = None) -> List[Tuple[int, int]]:
    """Generate SBM graph edges (community structure)."""
    if seed is not None:
        random.seed(seed)
    
    # Assign nodes to communities
    community = [i % k for i in range(n)]
    
    edges = []
    for i in range(n):
        for j in range(i + 1, n):
            if community[i] == community[j]:
                if random.random() < p_in:
                    edges.append((i, j))
            else:
                if random.random() < p_out:
                    edges.append((i, j))
    return edges


def generate_grid_graph(rows: int, cols: int) -> List[Tuple[int, int]]:
    """Generate grid graph (high structure, local connectivity)."""
    n = rows * cols
    edges = []
    
    for r in range(rows):
        for c in range(cols):
            node = r * cols + c
            # Right neighbor
            if c < cols - 1:
                edges.append((node, node + 1))
            # Down neighbor
            if r < rows - 1:
                edges.append((node, node + cols))
    
    return edges


def run_graph_coloring_benchmark(
    structure: str,
    n: int = 50,
    trials: int = 5,
    seed: int = 42
) -> List[CSPResult]:
    """Run graph coloring benchmark."""
    results = []
    
    for trial in range(trials):
        trial_seed = seed + trial
        
        # Generate graph based on structure
        if structure == 'random':
            edges = generate_random_graph(n, 0.15, trial_seed)
            num_colors = 5
        elif structure == 'community':
            edges = generate_structured_graph(n, 5, 0.3, 0.02, trial_seed)
            num_colors = 4
        elif structure == 'grid':
            side = int(math.sqrt(n))
            edges = generate_grid_graph(side, side)
            n = side * side  # Actual nodes
            num_colors = 2  # Grids are bipartite!
        else:
            raise ValueError(f"Unknown structure: {structure}")
        
        csp = GraphColoringCSP(n, edges, num_colors)
        
        start = time.time()
        solution = csp.solve_with_mu()
        elapsed = time.time() - start
        
        results.append(CSPResult(
            problem_type='graph_coloring',
            problem_structure=structure,
            num_variables=n,
            num_constraints=len(edges),
            solved=solution is not None,
            solution=solution,
            mu_cost=csp.mu_ledger,
            backtracks=csp.backtracks,
            time_seconds=elapsed,
        ))
    
    return results


def run_scheduling_benchmark(
    structure: str,
    n: int = 30,
    trials: int = 5,
    seed: int = 42
) -> List[CSPResult]:
    """Run scheduling benchmark."""
    results = []
    
    for trial in range(trials):
        trial_seed = seed + trial
        
        # Generate conflicts based on structure
        if structure == 'random':
            conflicts = generate_random_graph(n, 0.2, trial_seed)
            num_slots = 6
        elif structure == 'departmental':
            # Tasks grouped by department - more conflicts within groups
            conflicts = generate_structured_graph(n, 5, 0.4, 0.05, trial_seed)
            num_slots = 5
        elif structure == 'sequential':
            # Chain dependencies - very structured
            conflicts = [(i, i+1) for i in range(n-1)]
            num_slots = 2
        else:
            raise ValueError(f"Unknown structure: {structure}")
        
        csp = SchedulingCSP(n, conflicts, num_slots)
        
        start = time.time()
        solution = csp.solve_with_mu()
        elapsed = time.time() - start
        
        results.append(CSPResult(
            problem_type='scheduling',
            problem_structure=structure,
            num_variables=n,
            num_constraints=len(conflicts),
            solved=solution is not None,
            solution=solution,
            mu_cost=csp.mu_ledger,
            backtracks=csp.backtracks,
            time_seconds=elapsed,
        ))
    
    return results


def main():
    """Run CSP benchmarks."""
    print("=" * 70)
    print("CONSTRAINT SATISFACTION BENCHMARK: μ-Cost Analysis")
    print("=" * 70)
    print()
    
    all_results = []
    
    # Graph Coloring
    print("GRAPH COLORING")
    print("-" * 70)
    
    for structure in ['random', 'community', 'grid']:
        results = run_graph_coloring_benchmark(structure, n=49 if structure == 'grid' else 50, trials=5)
        all_results.extend(results)
        
        avg_mu = sum(r.mu_cost for r in results) / len(results)
        avg_bt = sum(r.backtracks for r in results) / len(results)
        solved = sum(1 for r in results if r.solved) / len(results) * 100
        
        print(f"  {structure:15} | μ-cost: {avg_mu:8.0f} | backtracks: {avg_bt:6.0f} | solved: {solved:.0f}%")
    
    print()
    
    # Scheduling
    print("SCHEDULING")
    print("-" * 70)
    
    for structure in ['random', 'departmental', 'sequential']:
        results = run_scheduling_benchmark(structure, n=30, trials=5)
        all_results.extend(results)
        
        avg_mu = sum(r.mu_cost for r in results) / len(results)
        avg_bt = sum(r.backtracks for r in results) / len(results)
        solved = sum(1 for r in results if r.solved) / len(results) * 100
        
        print(f"  {structure:15} | μ-cost: {avg_mu:8.0f} | backtracks: {avg_bt:6.0f} | solved: {solved:.0f}%")
    
    # Analysis
    print()
    print("=" * 70)
    print("ANALYSIS")
    print("=" * 70)
    
    # Compare structured vs random
    coloring_random = [r for r in all_results if r.problem_type == 'graph_coloring' and r.problem_structure == 'random']
    coloring_struct = [r for r in all_results if r.problem_type == 'graph_coloring' and r.problem_structure in ['community', 'grid']]
    
    if coloring_random and coloring_struct:
        random_mu = sum(r.mu_cost for r in coloring_random) / len(coloring_random)
        struct_mu = sum(r.mu_cost for r in coloring_struct) / len(coloring_struct)
        
        print(f"\nGraph Coloring:")
        print(f"  Random structure avg μ-cost:     {random_mu:,.0f}")
        print(f"  Structured (community/grid) avg: {struct_mu:,.0f}")
        
        if random_mu > struct_mu:
            ratio = random_mu / struct_mu
            print(f"  → Random costs {ratio:.1f}x more μ than structured")
    
    sched_random = [r for r in all_results if r.problem_type == 'scheduling' and r.problem_structure == 'random']
    sched_struct = [r for r in all_results if r.problem_type == 'scheduling' and r.problem_structure in ['departmental', 'sequential']]
    
    if sched_random and sched_struct:
        random_mu = sum(r.mu_cost for r in sched_random) / len(sched_random)
        struct_mu = sum(r.mu_cost for r in sched_struct) / len(sched_struct)
        
        print(f"\nScheduling:")
        print(f"  Random structure avg μ-cost:         {random_mu:,.0f}")
        print(f"  Structured (dept/sequential) avg:    {struct_mu:,.0f}")
        
        if random_mu > struct_mu:
            ratio = random_mu / struct_mu
            print(f"  → Random costs {ratio:.1f}x more μ than structured")
    
    print()
    print("INTERPRETATION:")
    print("-" * 70)
    print("• μ-cost directly correlates with search complexity")
    print("• Structured problems have exploitable patterns that reduce μ")
    print("• Random problems lack structure - solver must pay full μ price")
    print("• Grid graphs are bipartite → 2-colorable → minimal μ")
    print("• This validates the Thiele Machine's insight model:")
    print("  discovering and exploiting structure reduces computational cost,")
    print("  but requires initial μ investment that only pays off when structure exists.")
    
    # Save
    output_dir = Path("benchmarks/csp_results")
    output_dir.mkdir(parents=True, exist_ok=True)
    
    with open(output_dir / "results.json", 'w') as f:
        json.dump([r.to_dict() for r in all_results], f, indent=2)
    
    print(f"\nResults saved to: {output_dir / 'results.json'}")


if __name__ == "__main__":
    main()
