#!/usr/bin/env python3
"""
Thermodynamic Factoring Experiment

The hypothesis: If μ = entropy, and paying entropy reveals structure,
then there should exist an encoding where factorization becomes VISIBLE
as partition structure after paying sufficient μ-cost.

This experiment tests several encodings to see if any make factors
"pop out" as graph structure that PDISCOVER can detect.

Author: Devon Thiele / Claude
Date: February 2026
"""

import math
import random
import numpy as np
import networkx as nx
from typing import List, Tuple, Dict, Optional, Set
from dataclasses import dataclass
import time


@dataclass
class FactoringResult:
    """Result of a factoring attempt."""
    n: int
    factors: Tuple[int, int]
    mu_cost: float
    method: str
    success: bool
    details: Dict


def is_prime(n: int) -> bool:
    """Quick primality check."""
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(math.sqrt(n)) + 1, 2):
        if n % i == 0:
            return False
    return True


def generate_semiprime(bits: int) -> Tuple[int, int, int]:
    """Generate a semiprime N = p * q where p, q are roughly bits/2 each."""
    while True:
        p = random.getrandbits(bits // 2) | 1  # Ensure odd
        if is_prime(p) and p > 3:
            break
    while True:
        q = random.getrandbits(bits // 2) | 1
        if is_prime(q) and q > 3 and q != p:
            break
    return p * q, min(p, q), max(p, q)


# =============================================================================
# ENCODING 1: Residue Graph
# =============================================================================
# Build a graph where structure reflects multiplicative residues mod N.
# If N = pq, the residue structure should have p and q "visible".

def build_residue_graph(n: int, sample_size: int = 1000) -> nx.Graph:
    """
    Build a graph from residue structure of Z_n^*.
    
    Nodes: random elements of Z_n^*
    Edges: connect a,b if their "multiplicative distance" is small
    
    Hypothesis: If N = pq, the graph should have 2 clusters
    corresponding to residue classes.
    """
    G = nx.Graph()
    
    # Sample random coprime elements
    nodes = []
    attempts = 0
    while len(nodes) < sample_size and attempts < sample_size * 10:
        x = random.randint(2, n - 1)
        if math.gcd(x, n) == 1:
            nodes.append(x)
        attempts += 1
    
    if len(nodes) < 10:
        return G
    
    G.add_nodes_from(nodes)
    
    # Connect nodes based on multiplicative structure
    # Key insight: a ≡ b (mod p) means a*b^(-1) ≡ 1 (mod p)
    # We can't compute this without knowing p, BUT
    # if we look at a*b mod n, elements in same residue class mod p
    # will have different behavior than cross-class products
    
    for i, a in enumerate(nodes):
        for b in nodes[i+1:]:
            # Compute "multiplicative similarity"
            # product mod n
            prod = (a * b) % n
            
            # Check if product shares structure with N
            g = math.gcd(prod - 1, n)
            
            # If gcd is non-trivial, these nodes are "close"
            if 1 < g < n:
                G.add_edge(a, b, weight=1.0 / g)
    
    return G


def analyze_residue_graph(G: nx.Graph, n: int) -> Dict:
    """Analyze the residue graph for factor signatures."""
    if len(G.nodes()) < 2:
        return {"verdict": "TOO_SMALL", "factor_hint": None}
    
    # Look for community structure
    try:
        import community as community_louvain
        partition = community_louvain.best_partition(G)
        n_communities = len(set(partition.values()))
    except ImportError:
        # Fallback: connected components
        n_communities = nx.number_connected_components(G)
    
    # Check edge density for factor hints
    factor_hints = set()
    for u, v, data in G.edges(data=True):
        prod = (u * v) % n
        g = math.gcd(prod - 1, n)
        if 1 < g < n:
            factor_hints.add(g)
    
    return {
        "verdict": "STRUCTURED" if n_communities > 1 else "CHAOTIC",
        "n_communities": n_communities,
        "factor_hints": list(factor_hints)[:5],
        "nodes": len(G.nodes()),
        "edges": len(G.edges())
    }


# =============================================================================
# ENCODING 2: Fermat Difference Graph
# =============================================================================
# N = a² - b² = (a-b)(a+b)
# Build a graph over candidate (a,b) pairs

def build_fermat_graph(n: int, search_radius: int = 1000) -> nx.Graph:
    """
    Build graph from Fermat's difference-of-squares approach.
    
    Nodes: candidate pairs (a, a² - n) where a > sqrt(n)
    Edges: connect pairs with similar b² values
    
    Hypothesis: The true factorization appears as a special node
    where b² is a perfect square.
    """
    G = nx.Graph()
    
    sqrt_n = int(math.isqrt(n))
    
    # Generate candidate a values
    candidates = []
    for a in range(sqrt_n + 1, sqrt_n + search_radius + 1):
        b_squared = a * a - n
        if b_squared > 0:
            b = int(math.isqrt(b_squared))
            is_perfect = (b * b == b_squared)
            candidates.append({
                'a': a,
                'b_squared': b_squared,
                'b': b,
                'is_perfect': is_perfect,
                'residual': b_squared - b * b
            })
    
    if not candidates:
        return G
    
    # Add nodes
    for i, c in enumerate(candidates):
        G.add_node(i, **c)
    
    # Connect nodes with similar residuals
    for i, c1 in enumerate(candidates):
        for j, c2 in enumerate(candidates[i+1:], i+1):
            # Similarity based on residual proximity
            diff = abs(c1['residual'] - c2['residual'])
            if diff < n // 100:  # Close residuals
                G.add_edge(i, j, weight=1.0 / (diff + 1))
    
    return G


def analyze_fermat_graph(G: nx.Graph, n: int) -> Dict:
    """Look for perfect square nodes (actual factors)."""
    perfect_nodes = [
        node for node, data in G.nodes(data=True)
        if data.get('is_perfect', False)
    ]
    
    if perfect_nodes:
        # Found a factorization!
        node_data = G.nodes[perfect_nodes[0]]
        a = node_data['a']
        b = node_data['b']
        factor1 = a - b
        factor2 = a + b
        return {
            "verdict": "FACTOR_FOUND",
            "factors": (factor1, factor2),
            "a": a,
            "b": b
        }
    
    # No perfect squares found - look at graph structure
    # Perfect squares might be in a special position
    
    # Find nodes with lowest residuals
    residuals = [(node, data['residual']) for node, data in G.nodes(data=True)]
    residuals.sort(key=lambda x: x[1])
    
    return {
        "verdict": "NO_PERFECT_SQUARE",
        "closest_residuals": residuals[:5],
        "nodes": len(G.nodes()),
        "edges": len(G.edges())
    }


# =============================================================================
# ENCODING 3: Thermodynamic Annealing
# =============================================================================
# Frame factoring as finding ground state of energy function
# E(d) = 0 if d divides N, else positive
# Use simulated annealing - heat dissipated = μ-cost

def thermodynamic_factor(n: int, max_iterations: int = 10000, 
                        initial_temp: float = 1.0,
                        cooling_rate: float = 0.9995) -> FactoringResult:
    """
    Factor N using simulated annealing.
    
    Energy function: E(d) = min(N mod d, d - (N mod d)) / d
    This is 0 exactly when d divides N.
    
    μ-cost = total entropy dissipated during annealing
    """
    sqrt_n = int(math.isqrt(n)) + 1
    
    # Energy function
    def energy(d: int) -> float:
        if d < 2 or d >= n:
            return float('inf')
        remainder = n % d
        return min(remainder, d - remainder) / d
    
    # Start with random divisor candidate
    current = random.randint(2, sqrt_n)
    current_energy = energy(current)
    
    best = current
    best_energy = current_energy
    
    temperature = initial_temp
    mu_cost = 0.0
    
    for iteration in range(max_iterations):
        # Check if we found a factor
        if current_energy == 0:
            return FactoringResult(
                n=n,
                factors=(current, n // current),
                mu_cost=mu_cost,
                method="thermodynamic_annealing",
                success=True,
                details={"iterations": iteration, "final_temp": temperature}
            )
        
        # Generate neighbor
        delta = random.choice([-2, -1, 1, 2])
        neighbor = current + delta
        if neighbor < 2:
            neighbor = 2
        if neighbor > sqrt_n:
            neighbor = sqrt_n
        
        neighbor_energy = energy(neighbor)
        
        # Accept or reject
        if neighbor_energy < current_energy:
            # Always accept improvement
            current = neighbor
            current_energy = neighbor_energy
            # μ-cost: we dissipated energy
            mu_cost += (current_energy - neighbor_energy) * temperature
        else:
            # Maybe accept worse solution (exploration)
            delta_e = neighbor_energy - current_energy
            acceptance_prob = math.exp(-delta_e / temperature)
            if random.random() < acceptance_prob:
                current = neighbor
                current_energy = neighbor_energy
                # μ-cost: entropy of random decision
                mu_cost += math.log2(1.0 / acceptance_prob) if acceptance_prob > 0 else 0
        
        if current_energy < best_energy:
            best = current
            best_energy = current_energy
        
        # Cool down
        temperature *= cooling_rate
        
        # Track entropy from cooling
        mu_cost += (1 - cooling_rate) * temperature
    
    # Didn't find exact factor, return best candidate
    return FactoringResult(
        n=n,
        factors=(best, n // best if n % best == 0 else -1),
        mu_cost=mu_cost,
        method="thermodynamic_annealing",
        success=(n % best == 0),
        details={"iterations": max_iterations, "best_energy": best_energy}
    )


# =============================================================================
# ENCODING 4: Partition Revelation
# =============================================================================
# The Thiele hypothesis: structure can be REVEALED by paying μ
# What if we could "ask the universe" for the partition?

def partition_revelation_factor(n: int, mu_budget: float = 100.0) -> FactoringResult:
    """
    Attempt to factor by "revealing" partition structure.
    
    The idea: Instead of COMPUTING the factors, we PAY to REVEAL them.
    
    In the current implementation, this is simulated by random probing
    with μ-cost charged per probe. A real implementation would need
    a physical oracle.
    
    Key insight: If physics-logic isomorphism is real, then there exists
    a physical process where paying k_B T ln(2) × μ joules returns
    μ bits of structural information about N.
    """
    mu_spent = 0.0
    probes = []
    
    sqrt_n = int(math.isqrt(n)) + 1
    
    while mu_spent < mu_budget:
        # Each probe costs log2(sqrt(n)) bits (specifying a candidate)
        probe_cost = math.log2(sqrt_n)
        mu_spent += probe_cost
        
        # Generate probe based on "entropy payment"
        # In a real system, this would use physical randomness
        probe = random.randint(2, sqrt_n)
        probes.append(probe)
        
        if n % probe == 0:
            # Found a factor!
            return FactoringResult(
                n=n,
                factors=(probe, n // probe),
                mu_cost=mu_spent,
                method="partition_revelation",
                success=True,
                details={"probes": len(probes), "winning_probe": probe}
            )
    
    return FactoringResult(
        n=n,
        factors=(-1, -1),
        mu_cost=mu_spent,
        method="partition_revelation",
        success=False,
        details={"probes": len(probes)}
    )


# =============================================================================
# ENCODING 5: The Key Insight Encoding
# =============================================================================
# What if the factors are visible in the SYMMETRY of N's representation?

def symmetry_encoding_factor(n: int) -> FactoringResult:
    """
    Look for factors in the SYMMETRY structure of N.
    
    Key insight: If N = pq, then the multiplicative group Z_N* has
    a product structure Z_(p-1) × Z_(q-1). This symmetry IS the factors.
    
    We look for "order anomalies" - elements whose order reveals the structure.
    """
    mu_cost = 0.0
    
    # Find the order of random elements
    # Order of g mod N divides lcm(p-1, q-1)
    # By Chinese Remainder Theorem, different primes give different orders
    
    orders = []
    for _ in range(100):
        g = random.randint(2, n - 1)
        if math.gcd(g, n) != 1:
            # Found a factor directly!
            factor = math.gcd(g, n)
            return FactoringResult(
                n=n,
                factors=(factor, n // factor),
                mu_cost=mu_cost + 1,
                method="symmetry_encoding",
                success=True,
                details={"method": "gcd_lucky", "g": g}
            )
        
        # Compute order (expensive but informative)
        mu_cost += math.log2(n)  # Cost of probing
        
        order = 1
        current = g
        max_order = min(n, 10000)  # Cap order search
        while current != 1 and order < max_order:
            current = (current * g) % n
            order += 1
        
        if order < max_order:
            orders.append(order)
    
    if not orders:
        return FactoringResult(
            n=n, factors=(-1, -1), mu_cost=mu_cost,
            method="symmetry_encoding", success=False,
            details={"reason": "no_orders_found"}
        )
    
    # The GCD of orders might reveal structure
    # gcd(order1, order2) often relates to (p-1) or (q-1)
    from functools import reduce
    order_gcd = reduce(math.gcd, orders)
    
    # Try divisors of order_gcd
    for d in range(2, min(order_gcd + 1, 10000)):
        if order_gcd % d == 0:
            # Check if 2^d ≡ 1 mod p for some factor p
            candidate = pow(2, d, n)
            g = math.gcd(candidate - 1, n)
            if 1 < g < n:
                return FactoringResult(
                    n=n,
                    factors=(g, n // g),
                    mu_cost=mu_cost,
                    method="symmetry_encoding",
                    success=True,
                    details={"order_gcd": order_gcd, "d": d}
                )
    
    return FactoringResult(
        n=n, factors=(-1, -1), mu_cost=mu_cost,
        method="symmetry_encoding", success=False,
        details={"orders": orders[:10], "order_gcd": order_gcd}
    )


# =============================================================================
# MAIN EXPERIMENT
# =============================================================================

def run_factoring_experiment(bits: int = 20, num_trials: int = 10):
    """
    Run the thermodynamic factoring experiment.
    
    Test whether any encoding allows polynomial-time factoring
    with μ-cost as the only "payment".
    """
    print("=" * 70)
    print("THERMODYNAMIC FACTORING EXPERIMENT")
    print("=" * 70)
    print(f"Testing {num_trials} semiprimes of ~{bits} bits")
    print()
    
    results = {
        "residue_graph": [],
        "fermat_graph": [],
        "thermodynamic": [],
        "partition_revelation": [],
        "symmetry": []
    }
    
    for trial in range(num_trials):
        n, p, q = generate_semiprime(bits)
        print(f"\nTrial {trial + 1}: N = {n} = {p} × {q}")
        print("-" * 50)
        
        # Test each method
        
        # 1. Residue Graph
        print("  [Residue Graph] Building...")
        G = build_residue_graph(n, sample_size=500)
        analysis = analyze_residue_graph(G, n)
        success = p in analysis.get('factor_hints', []) or q in analysis.get('factor_hints', [])
        results["residue_graph"].append({
            "n": n, "success": success, 
            "mu_cost": len(G.nodes()) * math.log2(n),
            "details": analysis
        })
        print(f"    Verdict: {analysis['verdict']}, Factor hints: {analysis.get('factor_hints', [])[:3]}")
        
        # 2. Fermat Graph
        print("  [Fermat Graph] Building...")
        G = build_fermat_graph(n, search_radius=500)
        analysis = analyze_fermat_graph(G, n)
        success = analysis["verdict"] == "FACTOR_FOUND"
        results["fermat_graph"].append({
            "n": n, "success": success,
            "mu_cost": len(G.nodes()) * math.log2(n),
            "details": analysis
        })
        print(f"    Verdict: {analysis['verdict']}")
        if success:
            print(f"    FACTORS FOUND: {analysis['factors']}")
        
        # 3. Thermodynamic Annealing
        print("  [Thermodynamic] Annealing...")
        result = thermodynamic_factor(n, max_iterations=5000)
        results["thermodynamic"].append({
            "n": n, "success": result.success,
            "mu_cost": result.mu_cost,
            "details": result.details
        })
        print(f"    Success: {result.success}, μ-cost: {result.mu_cost:.2f}")
        if result.success:
            print(f"    FACTORS FOUND: {result.factors}")
        
        # 4. Partition Revelation
        print("  [Partition Revelation] Probing...")
        result = partition_revelation_factor(n, mu_budget=100.0)
        results["partition_revelation"].append({
            "n": n, "success": result.success,
            "mu_cost": result.mu_cost,
            "details": result.details
        })
        print(f"    Success: {result.success}, μ-cost: {result.mu_cost:.2f}, Probes: {result.details['probes']}")
        
        # 5. Symmetry Encoding
        print("  [Symmetry Encoding] Analyzing...")
        result = symmetry_encoding_factor(n)
        results["symmetry"].append({
            "n": n, "success": result.success,
            "mu_cost": result.mu_cost,
            "details": result.details
        })
        print(f"    Success: {result.success}, μ-cost: {result.mu_cost:.2f}")
        if result.success:
            print(f"    FACTORS FOUND: {result.factors}")
    
    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    
    for method, data in results.items():
        successes = sum(1 for d in data if d["success"])
        avg_mu = sum(d["mu_cost"] for d in data) / len(data) if data else 0
        print(f"  {method:25s}: {successes}/{num_trials} success, avg μ-cost: {avg_mu:.2f}")
    
    print()
    print("KEY QUESTION: Did any method achieve polynomial μ-cost factoring?")
    print()
    
    # Analyze if μ-cost scales polynomially with bit size
    print("To answer this, we need to test larger bit sizes...")
    
    return results


if __name__ == "__main__":
    random.seed(42)
    results = run_factoring_experiment(bits=30, num_trials=5)
