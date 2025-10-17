#!/usr/bin/env python3
"""
No-Hints Instance Generator for Computational Priced Sight Demonstration

This module generates unlabeled computational instances from random seeds,
enabling automatic structure discovery without human hints.
"""

import random
import hashlib
from typing import Dict, Any, List, Optional
import json


class InstanceGenerator:
    """Generates unlabeled computational instances from seeds."""

    def __init__(self, seed: Optional[int] = None):
        """Initialize with optional seed for reproducibility."""
        self.seed = seed or random.randint(0, 2**32 - 1)
        random.seed(self.seed)

    def generate_instance(self, difficulty: str = "medium") -> Dict[str, Any]:
        """
        Generate an unlabeled computational instance.

        The instance contains only raw data - no hints about which model
        should be used to solve it. The structure must be discovered via MDL.
        """
        instance_type = random.choice([
            "parity_check",      # GF(2) linear
            "permutation_game",  # Symmetry
            "factor_challenge",  # Modular arithmetic
            "pebble_puzzle",     # Pebbling
            "tseitin_expander",  # Tseitin on expander graphs
            "pigeonhole",        # Pigeonhole principle
            "mixed_constraints"  # Combination
        ])

        if instance_type == "parity_check":
            return self._generate_parity_instance(difficulty)
        elif instance_type == "permutation_game":
            return self._generate_symmetry_instance(difficulty)
        elif instance_type == "factor_challenge":
            return self._generate_modular_instance(difficulty)
        elif instance_type == "pebble_puzzle":
            return self._generate_pebbling_instance(difficulty)
        elif instance_type == "tseitin_expander":
            return self._generate_tseitin_expander_instance(difficulty)
        elif instance_type == "pigeonhole":
            return self._generate_pigeonhole_instance(difficulty)
        else:
            return self._generate_mixed_instance(difficulty)

    def _generate_parity_instance(self, difficulty: str) -> Dict[str, Any]:
        """Generate a GF(2) linear algebra instance."""
        sizes = {"easy": 8, "medium": 16, "hard": 32}
        n_vars = sizes[difficulty]

        # Generate a random GF(2) system
        matrix = []
        for _ in range(n_vars // 2):  # Half as many equations as variables
            equation = [random.choice([0, 1]) for _ in range(n_vars)]
            matrix.append(equation)

        # Random right-hand side
        rhs = [random.choice([0, 1]) for _ in range(len(matrix))]

        return {
            "seed": self.seed,
            "type": "unlabeled",
            "data": {
                "matrix": matrix,
                "rhs": rhs,
                "field": 2  # GF(2)
            }
            # No metadata for true no-hints discovery
        }

    def _generate_symmetry_instance(self, difficulty: str) -> Dict[str, Any]:
        """Generate a symmetry-based instance."""
        sizes = {"easy": 6, "medium": 10, "hard": 15}
        n_elements = sizes[difficulty]

        # Generate permutation group elements
        elements = list(range(n_elements))
        permutations = []

        # Generate some random permutations
        for _ in range(min(5, n_elements)):
            perm = elements.copy()
            random.shuffle(perm)
            permutations.append(perm)

        # Generate some invariant constraints
        constraints = []
        for _ in range(n_elements // 2):
            # Random invariant under the group
            constraint = {
                "type": "invariant",
                "elements": random.sample(elements, random.randint(2, 4)),
                "relation": random.choice(["sum", "product", "max"])
            }
            constraints.append(constraint)

        return {
            "seed": self.seed,
            "type": "unlabeled",
            "data": {
                "elements": elements,
                "permutations": permutations,
                "constraints": constraints
            }
            # No metadata for true no-hints discovery
        }

    def _generate_modular_instance(self, difficulty: str) -> Dict[str, Any]:
        """Generate a modular arithmetic instance."""
        moduli = {"easy": 100, "medium": 1000, "hard": 10000}
        modulus = moduli[difficulty]

        # Generate some numbers and operations
        numbers = [random.randint(0, modulus-1) for _ in range(10)]
        operations = []

        for _ in range(5):
            op = {
                "type": random.choice(["multiply", "add", "exponentiate"]),
                "operands": random.sample(numbers, 2),
                "modulus": modulus
            }
            operations.append(op)

        # Add a factoring challenge
        target = random.randint(2, modulus//2)
        # Mock factoring setup for demo

        return {
            "seed": self.seed,
            "type": "unlabeled",
            "data": {
                "numbers": numbers,
                "operations": operations,
                "factor_target": target,
                "modulus": modulus
            }
            # No metadata for true no-hints discovery
        }

    def _generate_tseitin_expander_instance(self, difficulty: str) -> Dict[str, Any]:
        """Generate Tseitin formula on an expander graph (known hard for resolution)."""
        sizes = {"easy": 10, "medium": 20, "hard": 30}
        n_vars = sizes[difficulty]

        # Create an expander graph (simplified random regular graph)
        degree = 3
        edges = []

        # Generate random regular graph
        for i in range(n_vars):
            for j in range(i+1, n_vars):
                if len([e for e in edges if i in e or j in e]) < degree and random.random() < 0.4:
                    edges.append((i, j))

        # Ensure minimum degree (add edges if needed)
        for i in range(n_vars):
            connected = [e for e in edges if i in e]
            while len(connected) < degree and len(edges) < n_vars * degree // 2:
                j = random.randint(0, n_vars-1)
                if i != j and (i, j) not in edges and (j, i) not in edges:
                    edges.append((i, j))
                    connected.append((i, j))

        # Tseitin variables: one per edge
        edge_vars = list(range(len(edges)))

        return {
            "seed": self.seed,
            "type": "unlabeled",
            "data": {
                "graph_type": "expander",
                "nodes": list(range(n_vars)),
                "edges": edges,
                "edge_variables": edge_vars,
                "degree": degree,
                "complexity_family": "tseitin_expander",
                "known_lower_bound": "exp(Ω(n^{1/2}))"  # Tree-like resolution lower bound
            }
        }

    def _generate_pigeonhole_instance(self, difficulty: str) -> Dict[str, Any]:
        """Generate Pigeonhole Principle formula (PHP_m^n for m > n)."""
        sizes = {"easy": (4, 3), "medium": (6, 5), "hard": (8, 7)}
        holes, pigeons = sizes[difficulty]

        # Variables: x_{p,h} = pigeon p in hole h
        variables = {}
        var_counter = 0

        for p in range(pigeons):
            for h in range(holes):
                variables[(p, h)] = var_counter
                var_counter += 1

        # Constraints:
        # 1. Each pigeon in exactly one hole (at least one, at most one)
        # 2. No hole has more than one pigeon (at most one per hole)

        constraints = []

        # Each pigeon in at least one hole
        for p in range(pigeons):
            clause = [variables[(p, h)] for h in range(holes)]
            constraints.append(clause)

        # Each pigeon in at most one hole (pairwise)
        for p in range(pigeons):
            for h1 in range(holes):
                for h2 in range(h1+1, holes):
                    clause = [-variables[(p, h1)], -variables[(p, h2)]]
                    constraints.append(clause)

        # No hole has more than one pigeon
        for h in range(holes):
            for p1 in range(pigeons):
                for p2 in range(p1+1, pigeons):
                    clause = [-variables[(p1, h)], -variables[(p2, h)]]
                    constraints.append(clause)

        return {
            "seed": self.seed,
            "type": "unlabeled",
            "data": {
                "pigeons": pigeons,
                "holes": holes,
                "variables": variables,
                "constraints": constraints,
                "complexity_family": "pigeonhole_principle",
                "known_lower_bound": "2^{Ω(n)}"  # Exponential lower bound for resolution
            }
        }

    def _generate_pebbling_instance(self, difficulty: str) -> Dict[str, Any]:
        """Generate a graph pebbling instance."""
        sizes = {"easy": 8, "medium": 12, "hard": 16}
        n_nodes = sizes[difficulty]

        # Generate a random graph
        edges = []
        for i in range(n_nodes):
            for j in range(i+1, n_nodes):
                if random.random() < 0.3:  # 30% edge probability
                    edges.append((i, j))

        # Generate pebbling constraints
        pebbles = random.randint(3, n_nodes//2)
        sources = random.sample(range(n_nodes), min(3, n_nodes//4))
        targets = random.sample([n for n in range(n_nodes) if n not in sources],
                               min(2, n_nodes//4))

        return {
            "seed": self.seed,
            "type": "unlabeled",
            "data": {
                "nodes": list(range(n_nodes)),
                "edges": edges,
                "pebbles": pebbles,
                "sources": sources,
                "targets": targets,
                "complexity_family": "graph_pebbling",
                "known_lower_bound": "n^{Ω(1)}"  # Polynomial lower bounds known
            }
        }

    def _generate_mixed_instance(self, difficulty: str) -> Dict[str, Any]:
        """Generate a mixed-constraints instance."""
        # Combine elements from different models
        base_instances = [
            self._generate_parity_instance(difficulty),
            self._generate_symmetry_instance(difficulty),
            self._generate_modular_instance(difficulty)
        ]

        # Merge them into one complex instance
        combined_data = {}
        for instance in base_instances:
            combined_data.update(instance["data"])

        return {
            "seed": self.seed,
            "type": "unlabeled",
            "data": combined_data
            # No metadata for true no-hints discovery
        }

    def get_commitment_hash(self, instance: Dict[str, Any]) -> str:
        """Generate cryptographic commitment hash for the instance."""
        # Canonical JSON representation
        canonical = json.dumps(instance, sort_keys=True, separators=(',', ':'))
        return hashlib.sha256(canonical.encode()).hexdigest()


def generate_demo_instances(n_instances: int = 5) -> List[Dict[str, Any]]:
    """Generate a set of demo instances for the computational priced sight demonstration."""
    instances = []
    generator = InstanceGenerator()

    for i in range(n_instances):
        generator.seed = i + 1000  # Deterministic seeds for demo
        instance = generator.generate_instance("medium")
        instance["commitment_hash"] = generator.get_commitment_hash(instance)
        instances.append(instance)

    return instances


if __name__ == "__main__":
    # Demo: generate and display some instances
    demo_instances = generate_demo_instances(3)

    for idx, inst in enumerate(demo_instances):
        print(f"\nInstance {idx+1}:")
        print(f"Type: {inst['type']}")
        print(f"Seed: {inst['seed']}")
        print(f"Commitment: {inst['commitment_hash'][:16]}...")
        print(f"Data keys: {list(inst['data'].keys())}")
        print(f"Metadata: {inst['metadata']}")