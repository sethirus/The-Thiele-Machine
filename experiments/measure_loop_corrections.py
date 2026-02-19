#!/usr/bin/env python3
"""
ALPHA DERIVATION EXPERIMENT: Loop Corrections in Partition Graph

HYPOTHESIS: α ≈ 1/137 emerges from loop-to-tree ratio in partition refinement graph.

THEORY:
- In QFT, α comes from loop diagrams (virtual corrections)
- In μ-theory, partitions form a refinement graph
- Loops = alternative refinement paths that return to start
- α = lim(n→∞) [loops at depth n] / [total paths at depth n]

THIS EXPERIMENT:
1. Build partition refinement trees to various depths
2. Count closed loops (paths that return to starting partition)
3. Measure loop/tree ratio
4. Check if converges to 1/137.036 ≈ 0.00729927
"""

import sys
from pathlib import Path
REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

import math
import numpy as np
import matplotlib.pyplot as plt
from dataclasses import dataclass
from typing import List, Set, Tuple, Dict
from collections import defaultdict

# Target value
ALPHA_EM = 1 / 137.035999084  # ≈ 0.00729927


@dataclass(frozen=True)
class Partition:
    """A partition of integers 0..n-1 into equivalence classes."""
    classes: Tuple[Tuple[int, ...], ...]  # Sorted tuple of sorted tuples
    
    @staticmethod
    def identity(n: int) -> 'Partition':
        """Each element in its own class."""
        return Partition(tuple((i,) for i in range(n)))
    
    @staticmethod
    def trivial(n: int) -> 'Partition':
        """All elements in one class."""
        return Partition((tuple(range(n)),))
    
    def split(self, class_idx: int) -> List['Partition']:
        """Split a class into all possible ways of dividing it."""
        if class_idx >= len(self.classes):
            return []
        
        target_class = list(self.classes[class_idx])
        if len(target_class) <= 1:
            return []  # Can't split singleton
        
        # Generate all non-trivial partitions of target_class
        # For simplicity, just split into 2 groups
        results = []
        for size1 in range(1, len(target_class)):
            # Take first size1 elements as group1, rest as group2
            group1 = tuple(sorted(target_class[:size1]))
            group2 = tuple(sorted(target_class[size1:]))
            
            new_classes = list(self.classes)
            new_classes[class_idx:class_idx+1] = [group1, group2]
            new_classes = tuple(sorted(new_classes))
            results.append(Partition(new_classes))
        
        return results
    
    def merge(self, idx1: int, idx2: int) -> 'Partition':
        """Merge two classes."""
        if idx1 >= len(self.classes) or idx2 >= len(self.classes):
            return self
        if idx1 == idx2:
            return self
        
        merged = tuple(sorted(set(self.classes[idx1]) | set(self.classes[idx2])))
        new_classes = [c for i, c in enumerate(self.classes) if i != idx1 and i != idx2]
        new_classes.append(merged)
        return Partition(tuple(sorted(new_classes)))
    
    def __hash__(self):
        return hash(self.classes)
    
    def __eq__(self, other):
        return isinstance(other, Partition) and self.classes == other.classes


@dataclass
class RefinementPath:
    """A sequence of partition transformations."""
    steps: List[Tuple[str, int, int]]  # (operation, arg1, arg2)
    
    def __hash__(self):
        return hash(tuple(self.steps))


def generate_paths(start: Partition, depth: int, max_paths: int = 10000) -> Dict[int, List[RefinementPath]]:
    """
    Generate all refinement paths up to given depth from start partition.
    
    Returns: {depth: [paths at that depth]}
    """
    paths_by_depth = defaultdict(list)
    paths_by_depth[0] = [RefinementPath([])]
    
    # Track (partition, path) pairs to avoid redundant exploration
    visited = {(start, RefinementPath([]))}
    
    for d in range(1, depth + 1):
        print(f"  Generating depth {d} paths...", end=" ", flush=True)
        
        for prev_path in paths_by_depth[d - 1]:
            # Apply prev_path to start to get current partition
            current = start
            for op, a1, a2 in prev_path.steps:
                if op == 'split':
                    splits = current.split(a1)
                    if a2 < len(splits):
                        current = splits[a2]
                elif op == 'merge':
                    current = current.merge(a1, a2)
            
            # Try all possible next operations
            # Splits
            for class_idx in range(len(current.classes)):
                splits = current.split(class_idx)
                for split_idx, next_partition in enumerate(splits):
                    new_path = RefinementPath(prev_path.steps + [('split', class_idx, split_idx)])
                    if (next_partition, new_path) not in visited:
                        visited.add((next_partition, new_path))
                        paths_by_depth[d].append(new_path)
                        if len(paths_by_depth[d]) >= max_paths:
                            print(f"reached max paths ({max_paths})")
                            return paths_by_depth
            
            # Merges
            for i in range(len(current.classes)):
                for j in range(i + 1, len(current.classes)):
                    next_partition = current.merge(i, j)
                    new_path = RefinementPath(prev_path.steps + [('merge', i, j)])
                    if (next_partition, new_path) not in visited:
                        visited.add((next_partition, new_path))
                        paths_by_depth[d].append(new_path)
                        if len(paths_by_depth[d]) >= max_paths:
                            print(f"reached max paths ({max_paths})")
                            return paths_by_depth
        
        print(f"{len(paths_by_depth[d])} paths")
    
    return paths_by_depth


def count_loops(start: Partition, paths_by_depth: Dict[int, List[RefinementPath]]) -> Dict[int, int]:
    """
    Count how many paths at each depth return to the starting partition (loops).
    """
    loops_by_depth = {}
    
    for depth, paths in paths_by_depth.items():
        if depth == 0:
            loops_by_depth[0] = 0
            continue
        
        loop_count = 0
        for path in paths:
            # Apply path to start
            current = start
            for op, a1, a2 in path.steps:
                if op == 'split':
                    splits = current.split(a1)
                    if a2 < len(splits):
                        current = splits[a2]
                    else:
                        current = None
                        break
                elif op == 'merge':
                    current = current.merge(a1, a2)
            
            if current == start:
                loop_count += 1
        
        loops_by_depth[depth] = loop_count
    
    return loops_by_depth


def measure_loop_ratio(n_elements: int, max_depth: int):
    """
    Measure loop-to-path ratio for partitions of n_elements up to max_depth.
    """
    print(f"\n{'='*80}")
    print(f"MEASURING LOOP CORRECTIONS: {n_elements} elements, depth {max_depth}")
    print(f"{'='*80}\n")
    
    # Start from identity partition (most refined)
    start = Partition.identity(n_elements)
    print(f"Starting partition: {start}")
    print(f"Classes: {len(start.classes)}")
    print()
    
    # Generate all paths
    print("Generating refinement paths...")
    paths = generate_paths(start, max_depth, max_paths=50000)
    
    print(f"\nPath counts by depth:")
    for d in sorted(paths.keys()):
        print(f"  Depth {d}: {len(paths[d])} paths")
    print()
    
    # Count loops
    print("Counting loops (paths that return to start)...")
    loops = count_loops(start, paths)
    
    print(f"\nLoop counts by depth:")
    for d in sorted(loops.keys()):
        print(f"  Depth {d}: {loops[d]} loops")
    print()
    
    # Compute ratios
    print(f"{'Depth':<8} {'Paths':<10} {'Loops':<10} {'Ratio':<12} {'α_em':<12} {'Error':<12}")
    print("-" * 80)
    
    ratios = []
    depths = []
    
    for d in sorted(paths.keys()):
        if d == 0:
            continue
        
        path_count = len(paths[d])
        loop_count = loops[d]
        ratio = loop_count / path_count if path_count > 0 else 0
        error = abs(ratio - ALPHA_EM) / ALPHA_EM * 100 if ALPHA_EM > 0 else 0
        
        print(f"{d:<8} {path_count:<10} {loop_count:<10} {ratio:<12.6f} {ALPHA_EM:<12.6f} {error:<12.1f}%")
        
        ratios.append(ratio)
        depths.append(d)
    
    return depths, ratios


def plot_convergence(all_results: List[Tuple[int, List[int], List[float]]]):
    """Plot loop ratios vs depth for different n_elements."""
    
    plt.figure(figsize=(12, 8))
    
    for n_elem, depths, ratios in all_results:
        plt.plot(depths, ratios, 'o-', alpha=0.7, label=f'n={n_elem} elements')
    
    # Target line
    plt.axhline(y=ALPHA_EM, color='red', linestyle='--', linewidth=2, label='α ≈ 1/137')
    
    plt.xlabel('Refinement Depth', fontsize=12)
    plt.ylabel('Loop/Path Ratio', fontsize=12)
    plt.title('Loop Corrections in Partition Graph\nHypothesis: Ratio → α as depth → ∞', fontsize=14)
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.yscale('log')
    
    plt.tight_layout()
    plt.savefig('results/alpha_loop_corrections.png', dpi=150)
    print(f"\nPlot saved to: results/alpha_loop_corrections.png")
    plt.close()


def main():
    """Run the loop correction experiment."""
    
    print("="*80)
    print("ALPHA DERIVATION EXPERIMENT")
    print("Loop Corrections in Partition Graph")
    print("="*80)
    print()
    print(f"Target: α_em = 1/137.036 ≈ {ALPHA_EM:.8f}")
    print()
    print("Hypothesis: Loop-to-path ratio converges to α as depth → ∞")
    print()
    
    # Create results directory
    Path('results').mkdir(exist_ok=True)
    
    # Test for different partition sizes
    all_results = []
    
    for n_elements in [3, 4, 5]:
        depths, ratios = measure_loop_ratio(n_elements, max_depth=6)
        all_results.append((n_elements, depths, ratios))
    
    # Plot results
    plot_convergence(all_results)
    
    print("\n" + "="*80)
    print("CONCLUSION")
    print("="*80)
    print()
    
    # Check if any series converges to α
    converged = False
    for n_elem, depths, ratios in all_results:
        if len(ratios) > 0:
            last_ratio = ratios[-1]
            error = abs(last_ratio - ALPHA_EM) / ALPHA_EM * 100
            if error < 10:  # Within 10%
                print(f"✓ n={n_elem}: Final ratio = {last_ratio:.6f}, error = {error:.1f}%")
                converged = True
            else:
                print(f"✗ n={n_elem}: Final ratio = {last_ratio:.6f}, error = {error:.1f}%")
    
    print()
    if converged:
        print("STATUS: PROMISING - Some series show convergence toward α")
        print("NEXT: Extend to higher depths, derive analytical formula")
    else:
        print("STATUS: NO CONVERGENCE - Loop correction hypothesis may be wrong")
        print("NEXT: Try alternative approaches (μ-optimal, RG, geometric)")
    print()


if __name__ == '__main__':
    main()
