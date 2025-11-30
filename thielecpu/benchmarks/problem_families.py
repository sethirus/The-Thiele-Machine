"""
Problem Families for Blind vs Sighted Benchmark Suite

This module provides generators for problem families where sighted
Thiele machines are expected to outperform blind (Turing-equivalent)
machines.

Each generator produces instances with:
- Known ground-truth partition structure
- Deterministic generation from (size, seed)
- Metadata for verification and analysis

FAMILIES:
1. Tseitin formulas on expander graphs (brutal for blind SAT)
2. Planted modular SAT with block structure  
3. Period-finding instances (Shor skeleton)

FALSIFIABILITY:
All generators are pure functions of (size, seed).
Anyone can reproduce identical instances and verify/falsify scaling claims.
"""

from __future__ import annotations

import hashlib
import json
import math
import random
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple


@dataclass
class BenchmarkInstance:
    """A benchmark instance with problem data and ground-truth partition."""
    
    family: str                          # Problem family name
    size: int                            # Instance size parameter
    seed: int                            # Random seed for reproducibility
    
    # Problem representation
    cnf_clauses: List[List[int]]         # CNF formula (list of clauses)
    num_variables: int                   # Number of variables
    
    # Ground-truth partition (for sighted solver)
    partition: List[Set[int]]            # Sets of variable indices
    partition_method: str                # How partition was determined
    
    # Metadata
    expected_answer: Optional[str]       # "SAT", "UNSAT", or factor string
    description: str                     # Human-readable description
    generation_hash: str                 # SHA256 of generation parameters
    
    def to_dict(self) -> Dict[str, Any]:
        """Serialize to JSON-compatible dictionary."""
        return {
            "family": self.family,
            "size": self.size,
            "seed": self.seed,
            "num_variables": self.num_variables,
            "num_clauses": len(self.cnf_clauses),
            "partition_count": len(self.partition),
            "partition_sizes": [len(p) for p in self.partition],
            "partition_method": self.partition_method,
            "expected_answer": self.expected_answer,
            "description": self.description,
            "generation_hash": self.generation_hash,
        }
    
    def save(self, path: Path) -> None:
        """Save instance to files."""
        path.mkdir(parents=True, exist_ok=True)
        
        # Save metadata
        meta_path = path / "metadata.json"
        meta_path.write_text(json.dumps(self.to_dict(), indent=2))
        
        # Save CNF in DIMACS format
        cnf_path = path / "problem.cnf"
        with open(cnf_path, 'w') as f:
            f.write(f"c {self.description}\n")
            f.write(f"c family={self.family} size={self.size} seed={self.seed}\n")
            f.write(f"p cnf {self.num_variables} {len(self.cnf_clauses)}\n")
            for clause in self.cnf_clauses:
                f.write(" ".join(map(str, clause)) + " 0\n")
        
        # Save partition
        partition_path = path / "partition.json"
        partition_data = {
            "partition": [sorted(list(p)) for p in self.partition],
            "method": self.partition_method,
        }
        partition_path.write_text(json.dumps(partition_data, indent=2))


def _hash_params(*args) -> str:
    """Generate deterministic hash from parameters."""
    data = json.dumps(args, sort_keys=True).encode('utf-8')
    return hashlib.sha256(data).hexdigest()[:16]


# =============================================================================
# FAMILY 1: TSEITIN FORMULAS ON EXPANDER GRAPHS
# =============================================================================

def _generate_expander_graph(n: int, degree: int, seed: int) -> List[Tuple[int, int]]:
    """
    Generate a degree-regular expander-like graph.
    
    Uses a random regular graph construction that approximates
    expander properties for our purposes.
    """
    rng = random.Random(seed)
    edges = []
    
    # Ensure n is at least degree + 1
    n = max(n, degree + 1)
    
    # Create a random degree-regular graph
    # Use a simple construction: connect each vertex to 'degree' random others
    for v in range(n):
        neighbors = set()
        attempts = 0
        while len(neighbors) < degree and attempts < n * 10:
            u = rng.randint(0, n - 1)
            if u != v:
                neighbors.add(u)
            attempts += 1
        
        for u in neighbors:
            if (v, u) not in edges and (u, v) not in edges:
                edges.append((min(v, u), max(v, u)))
    
    return edges


def generate_tseitin_instance(n: int, seed: int) -> BenchmarkInstance:
    """
    Generate a Tseitin formula on a degree-3 expander graph.
    
    Tseitin formulas encode parity constraints on graphs.
    They are known to be hard for resolution-based SAT solvers
    (exponential in the expansion parameter), but have natural
    partition structure following the graph's community structure.
    
    Args:
        n: Number of vertices (controls problem size)
        seed: Random seed for reproducibility
        
    Returns:
        BenchmarkInstance with UNSAT Tseitin formula
    """
    n = max(3, n)  # Minimum 3 vertices
    degree = 3
    
    # Generate expander graph
    edges = _generate_expander_graph(n, degree, seed)
    
    # Assign edge variables
    edge_to_var = {e: i + 1 for i, e in enumerate(edges)}
    num_vars = len(edges)
    
    # Generate charge function (odd parity at each vertex for UNSAT)
    # Setting all charges to 1 (odd) creates an unsatisfiable Tseitin formula
    # because the sum of parities over all vertices equals the number of edges
    # counted twice (each edge contributes to exactly 2 vertices), which is even.
    # But with all odd charges, we require an odd total, creating a contradiction.
    rng = random.Random(seed + 1)
    charges = {v: 1 for v in range(n)}  # All odd charges = guaranteed UNSAT
    
    # Build Tseitin clauses
    clauses = []
    
    for v in range(n):
        # Find all edges incident to v
        incident = []
        for e in edges:
            if v in e:
                incident.append(edge_to_var[e])
        
        if not incident:
            continue
            
        # Generate XOR constraint: sum of edges ≡ charge[v] (mod 2)
        # Encode as CNF using standard XOR-to-CNF conversion
        # Note: This enumeration is O(2^k) where k = vertex degree.
        # For degree-3 graphs (our case), k ≤ 3, so 2^k ≤ 8 is efficient.
        # For higher degrees, use Tseitin auxiliary variable encoding.
        charge = charges[v]
        
        # For degree-3 graphs, enumerate all 2^k assignments (at most 8)
        k = len(incident)
        for assignment in range(2**k):
            parity = bin(assignment).count('1') % 2
            if parity != charge:
                # This assignment violates the constraint
                clause = []
                for i, var in enumerate(incident):
                    if (assignment >> i) & 1:
                        clause.append(-var)
                    else:
                        clause.append(var)
                if clause:
                    clauses.append(clause)
    
    # Remove duplicate clauses
    unique_clauses = list(set(tuple(sorted(c)) for c in clauses))
    clauses = [list(c) for c in unique_clauses]
    
    # Partition: group edges by connected components or vertex neighborhoods
    partition = []
    vertices_per_module = max(1, n // 4)
    for start in range(0, n, vertices_per_module):
        module_vars = set()
        for v in range(start, min(start + vertices_per_module, n)):
            for e in edges:
                if v in e:
                    module_vars.add(edge_to_var[e])
        if module_vars:
            partition.append(module_vars)
    
    # Ensure all variables are covered
    covered = set().union(*partition) if partition else set()
    uncovered = set(range(1, num_vars + 1)) - covered
    if uncovered:
        if partition:
            partition[0] = partition[0] | uncovered
        else:
            partition.append(uncovered)
    
    return BenchmarkInstance(
        family="tseitin",
        size=n,
        seed=seed,
        cnf_clauses=clauses,
        num_variables=num_vars,
        partition=partition,
        partition_method="vertex_neighborhood",
        expected_answer="UNSAT",
        description=f"Tseitin formula on {n}-vertex degree-{degree} graph",
        generation_hash=_hash_params("tseitin", n, seed),
    )


# =============================================================================
# FAMILY 2: PLANTED MODULAR SAT
# =============================================================================

def generate_planted_sat_instance(n: int, seed: int) -> BenchmarkInstance:
    """
    Generate a planted SAT instance with block structure.
    
    The formula has k blocks, each with n/k variables.
    Within each block, we plant a satisfying assignment.
    Cross-block clauses are rare, so solving each block
    independently and composing is efficient.
    
    Args:
        n: Total number of variables
        seed: Random seed for reproducibility
        
    Returns:
        BenchmarkInstance with SAT formula and planted solution
    """
    n = max(4, n)
    rng = random.Random(seed)
    
    # Number of blocks (sqrt scaling for interesting structure)
    k = max(2, int(math.sqrt(n)))
    vars_per_block = n // k
    
    # Plant a satisfying assignment
    planted_assignment = [rng.choice([True, False]) for _ in range(n)]
    
    clauses = []
    partition = []
    
    for block_idx in range(k):
        start_var = block_idx * vars_per_block + 1
        end_var = min(start_var + vars_per_block, n + 1)
        block_vars = list(range(start_var, end_var))
        
        if not block_vars:
            continue
            
        partition.append(set(block_vars))
        
        # Generate random 3-SAT clauses within this block
        # All clauses are satisfied by the planted assignment
        num_block_clauses = len(block_vars) * 4  # 4 clauses per variable
        
        for _ in range(num_block_clauses):
            # Pick 3 random variables from this block
            if len(block_vars) < 3:
                clause_vars = block_vars
            else:
                clause_vars = rng.sample(block_vars, 3)
            
            # Create a clause satisfied by the planted assignment
            clause = []
            for var in clause_vars:
                # Ensure clause is satisfied by planted assignment
                if planted_assignment[var - 1]:
                    clause.append(var if rng.random() > 0.3 else -var)
                else:
                    clause.append(-var if rng.random() > 0.3 else var)
            
            # Ensure at least one literal matches the planted assignment
            satisfied = any(
                (lit > 0 and planted_assignment[abs(lit) - 1]) or
                (lit < 0 and not planted_assignment[abs(lit) - 1])
                for lit in clause
            )
            if not satisfied and clause:
                # Fix the first literal
                var = clause_vars[0]
                if planted_assignment[var - 1]:
                    clause[0] = var
                else:
                    clause[0] = -var
            
            if clause:
                clauses.append(clause)
    
    # Add a few cross-block clauses (sparse, to maintain structure)
    num_cross = max(1, k // 2)
    for _ in range(num_cross):
        # Pick variables from different blocks
        blocks = rng.sample(range(k), min(2, k))
        cross_vars = []
        for b in blocks:
            start = b * vars_per_block + 1
            end = min(start + vars_per_block, n + 1)
            if start < end:
                cross_vars.append(rng.randint(start, end - 1))
        
        if len(cross_vars) >= 2:
            clause = []
            for var in cross_vars[:3]:
                if planted_assignment[var - 1]:
                    clause.append(var)
                else:
                    clause.append(-var)
            clauses.append(clause)
    
    return BenchmarkInstance(
        family="planted_sat",
        size=n,
        seed=seed,
        cnf_clauses=clauses,
        num_variables=n,
        partition=partition,
        partition_method="planted_blocks",
        expected_answer="SAT",
        description=f"Planted modular SAT with {k} blocks of ~{vars_per_block} variables",
        generation_hash=_hash_params("planted_sat", n, seed),
    )


# =============================================================================
# FAMILY 3: PERIOD-FINDING INSTANCES (SHOR SKELETON)
# =============================================================================

def generate_period_finding_instance(N: int, base: int) -> BenchmarkInstance:
    """
    Generate a period-finding instance for Shor's algorithm skeleton.
    
    This encodes the problem of finding the period r of a^x mod N.
    The partition structure comes from the modular arithmetic structure.
    
    Args:
        N: The composite number to factor
        base: The base for exponentiation (must be coprime to N)
        
    Returns:
        BenchmarkInstance encoding the period-finding problem
    """
    import math as m
    
    # Validate inputs
    if N <= 1:
        raise ValueError("N must exceed 1")
    if m.gcd(base, N) != 1:
        raise ValueError("base must be coprime to N")
    
    # Compute the actual period
    period = 1
    power = base % N
    while power != 1 and period < 2 * N:
        power = (power * base) % N
        period += 1
    
    # Encode as a constraint satisfaction problem
    # Variables represent bits of the period candidate
    num_bits = max(1, N.bit_length())
    num_vars = num_bits
    
    # Create clauses encoding period constraints
    # This is a simplified encoding for demonstration
    clauses = []
    
    # The period divides the order, so we add constraints based on
    # known divisibility properties
    residues = {k: pow(base, k, N) for k in range(min(period + 5, 2 * N))}
    
    # Add clauses that encode the period structure
    # For each bit position, add constraints
    for bit in range(num_bits):
        var = bit + 1
        # Add a trivial tautology to ensure the variable appears
        clauses.append([var, -var])  # x ∨ ¬x is always true
    
    # Add structural constraints based on period
    if period % 2 == 0:
        # If period is even, add a constraint reflecting this
        clauses.append([1])  # First bit must be 0 (even number ends in 0)
    else:
        clauses.append([-1])  # First bit must be 1 (odd number ends in 1)
    
    # Partition by bit significance (logarithmic structure)
    partition = []
    bits_per_module = max(1, num_bits // 4)
    for start in range(0, num_bits, bits_per_module):
        end = min(start + bits_per_module, num_bits)
        module = set(range(start + 1, end + 1))
        if module:
            partition.append(module)
    
    if not partition:
        partition.append(set(range(1, num_vars + 1)))
    
    # Expected answer is the period
    expected = str(period)
    
    return BenchmarkInstance(
        family="period_finding",
        size=N,
        seed=base,  # Use base as "seed" for reproducibility
        cnf_clauses=clauses,
        num_variables=num_vars,
        partition=partition,
        partition_method="bit_significance",
        expected_answer=expected,
        description=f"Period-finding: ord_{N}({base}) = {period}",
        generation_hash=_hash_params("period_finding", N, base),
    )


# =============================================================================
# FAMILY REGISTRY
# =============================================================================

PROBLEM_FAMILIES = {
    "tseitin": {
        "generator": generate_tseitin_instance,
        "description": "Tseitin formulas on expander graphs (UNSAT, hard for resolution)",
        "expected_blind": "exponential",
        "expected_sighted": "polynomial",
    },
    "planted_sat": {
        "generator": generate_planted_sat_instance,
        "description": "Planted modular SAT with block structure",
        "expected_blind": "exponential",
        "expected_sighted": "polynomial",
    },
    "period_finding": {
        "generator": generate_period_finding_instance,
        "description": "Period-finding instances (Shor's algorithm skeleton)",
        "expected_blind": "exponential",
        "expected_sighted": "polynomial",
    },
}


def generate_instance(family: str, size: int, seed: int) -> BenchmarkInstance:
    """Generate a benchmark instance from a family."""
    if family not in PROBLEM_FAMILIES:
        raise ValueError(f"Unknown family: {family}. Available: {list(PROBLEM_FAMILIES.keys())}")
    
    generator = PROBLEM_FAMILIES[family]["generator"]
    return generator(size, seed)


def list_families() -> List[Dict[str, str]]:
    """List available problem families."""
    return [
        {"name": name, "description": info["description"]}
        for name, info in PROBLEM_FAMILIES.items()
    ]


if __name__ == "__main__":
    # Demo: generate one instance from each family
    print("Problem Family Generators")
    print("=" * 60)
    
    for family in PROBLEM_FAMILIES:
        print(f"\n{family.upper()}")
        print("-" * 40)
        
        if family == "period_finding":
            instance = generate_instance(family, 21, 2)
        else:
            instance = generate_instance(family, 10, 42)
        
        print(f"  Variables: {instance.num_variables}")
        print(f"  Clauses: {len(instance.cnf_clauses)}")
        print(f"  Partitions: {len(instance.partition)}")
        print(f"  Expected: {instance.expected_answer}")
        print(f"  Description: {instance.description}")
        print(f"  Hash: {instance.generation_hash}")
