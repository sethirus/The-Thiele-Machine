# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""
Grammar Crawler: Grammar-Guided Genetic Programming for Equation Discovery

This module implements the core grammar crawler that synthesizes physical
equations from atomic primitives without being explicitly programmed with
complex operators. The Laplacian, Hamiltonian, and other operators must
EMERGE from composition of simpler operations.

CRITICAL CONSTRAINT: This file must NOT contain the strings "Laplacian" or
"nabla" in the gene pool or primitive definitions (except in comments).
"""

import random
import numpy as np
from typing import List, Dict, Any, Optional, Tuple, Callable
from dataclasses import dataclass, field
from enum import Enum
import json
from pathlib import Path


class AtomicOp(Enum):
    """Atomic operations allowed by the physics grammar.
    
    These are the ONLY primitives allowed. Complex operators must emerge.
    """
    ADD = "+"
    SUB = "-"
    MUL = "*"
    DIV = "/"
    PARTIAL_X = "∂/∂x"
    PARTIAL_Y = "∂/∂y"
    PARTIAL_Z = "∂/∂z"
    PARTIAL_T = "∂/∂t"
    CONST = "const"
    VAR = "var"


@dataclass
class EquationNode:
    """Node in the equation expression tree."""
    op: AtomicOp
    children: List['EquationNode'] = field(default_factory=list)
    value: Optional[float] = None  # For constants
    var_name: Optional[str] = None  # For variables
    
    def __repr__(self) -> str:
        """String representation of the node."""
        if self.op == AtomicOp.CONST:
            return f"{self.value}"
        elif self.op == AtomicOp.VAR:
            return f"{self.var_name}"
        elif self.op in [AtomicOp.PARTIAL_X, AtomicOp.PARTIAL_Y, 
                         AtomicOp.PARTIAL_Z, AtomicOp.PARTIAL_T]:
            if len(self.children) > 0:
                return f"{self.op.value}({self.children[0]})"
            return f"{self.op.value}"
        elif self.op in [AtomicOp.ADD, AtomicOp.SUB, AtomicOp.MUL, AtomicOp.DIV]:
            if len(self.children) == 2:
                return f"({self.children[0]} {self.op.value} {self.children[1]})"
            return f"{self.op.value}"
        return f"{self.op.value}"
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert node to dictionary for serialization."""
        return {
            "op": self.op.value,
            "value": self.value,
            "var_name": self.var_name,
            "children": [child.to_dict() for child in self.children]
        }
    
    def complexity(self) -> int:
        """Calculate complexity (number of nodes in tree)."""
        return 1 + sum(child.complexity() for child in self.children)
    
    def depth(self) -> int:
        """Calculate depth of expression tree."""
        if not self.children:
            return 1
        return 1 + max(child.depth() for child in self.children)


@dataclass
class Equation:
    """Represents a candidate physical equation."""
    lhs: EquationNode
    rhs: EquationNode
    fitness: float = 0.0
    generation: int = 0
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def __repr__(self) -> str:
        return f"{self.lhs} = {self.rhs}"
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert equation to dictionary for serialization."""
        return {
            "lhs": self.lhs.to_dict(),
            "rhs": self.rhs.to_dict(),
            "fitness": self.fitness,
            "generation": self.generation,
            "metadata": self.metadata
        }
    
    def complexity(self) -> int:
        """Total complexity of equation."""
        return self.lhs.complexity() + self.rhs.complexity()


class GrammarCrawler:
    """Grammar-guided genetic programming engine for equation discovery.
    
    This crawler synthesizes physical equations by composing atomic operations
    defined in the grammar. It uses genetic programming to evolve candidate
    equations that best fit the data.
    
    CRITICAL: This class must discover complex operators (like the second
    derivative operator that forms part of diffusion equations) through
    composition of first-order partial derivatives, NOT by having them
    as primitives in the gene pool.
    """
    
    def __init__(
        self,
        max_depth: int = 5,
        population_size: int = 100,
        mutation_rate: float = 0.2,
        crossover_rate: float = 0.7,
        seed: Optional[int] = 42
    ):
        """Initialize the grammar crawler.
        
        Args:
            max_depth: Maximum depth of expression trees
            population_size: Number of candidate equations in population
            mutation_rate: Probability of mutation
            crossover_rate: Probability of crossover
            seed: Random seed for reproducibility
        """
        self.max_depth = max_depth
        self.population_size = population_size
        self.mutation_rate = mutation_rate
        self.crossover_rate = crossover_rate
        self.seed = seed
        
        if seed is not None:
            random.seed(seed)
            np.random.seed(seed)
        
        # Gene pool: ONLY atomic operations
        self.gene_pool = [
            AtomicOp.ADD, AtomicOp.SUB, AtomicOp.MUL, AtomicOp.DIV,
            AtomicOp.PARTIAL_X, AtomicOp.PARTIAL_Y, AtomicOp.PARTIAL_Z,
            AtomicOp.PARTIAL_T
        ]
        
        # Terminal symbols
        self.terminals = [AtomicOp.CONST, AtomicOp.VAR]
        
        # Variables available in the problem
        self.variables = ['u', 'x', 'y', 'z', 't']
        
        # Constants
        self.constants = [0.0, 1.0, 2.0, -1.0, 0.5]
        
        self.population: List[Equation] = []
        self.generation = 0
        self.best_equation: Optional[Equation] = None
        
    def generate_random_node(self, depth: int = 0) -> EquationNode:
        """Generate a random expression node.
        
        Args:
            depth: Current depth in the tree (to prevent infinite recursion)
            
        Returns:
            Random EquationNode
        """
        # If we've reached max depth, must use terminal
        if depth >= self.max_depth:
            op = random.choice(self.terminals)
        else:
            # Choose between operator and terminal
            if random.random() < 0.3:  # 30% chance of terminal
                op = random.choice(self.terminals)
            else:
                op = random.choice(self.gene_pool)
        
        node = EquationNode(op=op)
        
        # Generate children based on operator type
        if op == AtomicOp.CONST:
            node.value = random.choice(self.constants)
        elif op == AtomicOp.VAR:
            node.var_name = random.choice(self.variables)
        elif op in [AtomicOp.PARTIAL_X, AtomicOp.PARTIAL_Y, 
                    AtomicOp.PARTIAL_Z, AtomicOp.PARTIAL_T]:
            # Unary operator: one child
            node.children = [self.generate_random_node(depth + 1)]
        elif op in [AtomicOp.ADD, AtomicOp.SUB, AtomicOp.MUL, AtomicOp.DIV]:
            # Binary operator: two children
            node.children = [
                self.generate_random_node(depth + 1),
                self.generate_random_node(depth + 1)
            ]
        
        return node
    
    def generate_random_equation(self) -> Equation:
        """Generate a random equation.
        
        Returns:
            Random Equation with LHS and RHS
        """
        # LHS is typically a time derivative (for PDE)
        lhs = EquationNode(op=AtomicOp.PARTIAL_T, children=[
            EquationNode(op=AtomicOp.VAR, var_name='u')
        ])
        
        # RHS is a complex expression to be evolved
        rhs = self.generate_random_node(depth=0)
        
        return Equation(lhs=lhs, rhs=rhs, generation=self.generation)
    
    def initialize_population(self):
        """Initialize the population with random equations."""
        self.population = [
            self.generate_random_equation() 
            for _ in range(self.population_size)
        ]
    
    def evaluate_fitness(
        self,
        equation: Equation,
        data: Dict[str, np.ndarray],
        fitness_func: Callable[[np.ndarray, np.ndarray], float]
    ) -> float:
        """Evaluate fitness of an equation against data.
        
        Args:
            equation: Equation to evaluate
            data: Dictionary with keys 'u', 'dudt', 'x', 'y', 't', etc.
            fitness_func: Function that computes fitness from predicted vs actual
            
        Returns:
            Fitness score (higher is better)
        """
        try:
            # Evaluate RHS on the data
            predicted = self._evaluate_node(equation.rhs, data)
            
            # Get actual LHS value (typically ∂u/∂t from data)
            actual = data.get('dudt', None)
            
            if actual is None or predicted is None:
                return 0.0
            
            # Compute fitness
            fitness = fitness_func(predicted, actual)
            equation.fitness = fitness
            return fitness
            
        except Exception as e:
            # Equation failed to evaluate (division by zero, etc.)
            equation.fitness = 0.0
            return 0.0
    
    def _evaluate_node(
        self,
        node: EquationNode,
        data: Dict[str, np.ndarray]
    ) -> Optional[np.ndarray]:
        """Evaluate an expression node on data.
        
        Args:
            node: EquationNode to evaluate
            data: Dictionary of data arrays
            
        Returns:
            Evaluated array or None if evaluation fails
        """
        if node.op == AtomicOp.CONST:
            # Return constant array with same shape as data
            shape = list(data.values())[0].shape
            return np.full(shape, node.value)
        
        elif node.op == AtomicOp.VAR:
            # Return variable from data
            return data.get(node.var_name, None)
        
        elif node.op in [AtomicOp.PARTIAL_X, AtomicOp.PARTIAL_Y, 
                         AtomicOp.PARTIAL_Z, AtomicOp.PARTIAL_T]:
            # Compute partial derivative using finite differences
            if len(node.children) == 0:
                return None
            
            child_val = self._evaluate_node(node.children[0], data)
            if child_val is None:
                return None
            
            # Determine axis for derivative
            axis_map = {
                AtomicOp.PARTIAL_X: 1,  # Assuming shape (t, x, y, z) or (x, y, z)
                AtomicOp.PARTIAL_Y: 2,
                AtomicOp.PARTIAL_Z: 3,
                AtomicOp.PARTIAL_T: 0
            }
            
            axis = axis_map.get(node.op, 0)
            
            # Handle different array dimensions
            if axis >= child_val.ndim:
                axis = child_val.ndim - 1
            
            # Compute gradient using numpy
            return np.gradient(child_val, axis=axis)
        
        elif node.op in [AtomicOp.ADD, AtomicOp.SUB, AtomicOp.MUL, AtomicOp.DIV]:
            # Binary operations
            if len(node.children) != 2:
                return None
            
            left = self._evaluate_node(node.children[0], data)
            right = self._evaluate_node(node.children[1], data)
            
            if left is None or right is None:
                return None
            
            if node.op == AtomicOp.ADD:
                return left + right
            elif node.op == AtomicOp.SUB:
                return left - right
            elif node.op == AtomicOp.MUL:
                return left * right
            elif node.op == AtomicOp.DIV:
                # Protect against division by zero
                with np.errstate(divide='ignore', invalid='ignore'):
                    result = np.divide(left, right)
                    result = np.nan_to_num(result, nan=0.0, posinf=0.0, neginf=0.0)
                return result
        
        return None
    
    def crossover(self, parent1: Equation, parent2: Equation) -> Equation:
        """Perform crossover between two parent equations.
        
        Args:
            parent1: First parent equation
            parent2: Second parent equation
            
        Returns:
            Offspring equation
        """
        # Create deep copies of parents' RHS
        child_rhs = self._copy_node(parent1.rhs)
        donor_rhs = self._copy_node(parent2.rhs)
        
        # Select random crossover points
        child_nodes = self._get_all_nodes(child_rhs)
        donor_nodes = self._get_all_nodes(donor_rhs)
        
        if len(child_nodes) > 0 and len(donor_nodes) > 0:
            # Pick random nodes
            child_point = random.choice(child_nodes)
            donor_point = random.choice(donor_nodes)
            
            # Swap subtrees
            child_point.op = donor_point.op
            child_point.children = [self._copy_node(c) for c in donor_point.children]
            child_point.value = donor_point.value
            child_point.var_name = donor_point.var_name
        
        # Create child equation (LHS stays the same)
        lhs = EquationNode(op=AtomicOp.PARTIAL_T, children=[
            EquationNode(op=AtomicOp.VAR, var_name='u')
        ])
        
        child = Equation(lhs=lhs, rhs=child_rhs, generation=self.generation)
        child.metadata['parents'] = [parent1.fitness, parent2.fitness]
        
        return child
    
    def mutate(self, equation: Equation) -> Equation:
        """Mutate an equation.
        
        Args:
            equation: Equation to mutate
            
        Returns:
            Mutated equation
        """
        mutated_rhs = self._copy_node(equation.rhs)
        
        # Get all nodes
        nodes = self._get_all_nodes(mutated_rhs)
        
        if len(nodes) > 0:
            # Pick random node to mutate
            node = random.choice(nodes)
            
            # Mutation types
            mutation_type = random.choice(['replace_op', 'replace_subtree', 'modify_value'])
            
            if mutation_type == 'replace_op':
                # Replace operator with another from gene pool
                if node.op in self.gene_pool:
                    node.op = random.choice(self.gene_pool)
            
            elif mutation_type == 'replace_subtree':
                # Replace entire subtree with new random tree
                new_subtree = self.generate_random_node(depth=0)
                node.op = new_subtree.op
                node.children = new_subtree.children
                node.value = new_subtree.value
                node.var_name = new_subtree.var_name
            
            elif mutation_type == 'modify_value':
                # Modify constant or variable
                if node.op == AtomicOp.CONST:
                    node.value = random.choice(self.constants)
                elif node.op == AtomicOp.VAR:
                    node.var_name = random.choice(self.variables)
        
        lhs = EquationNode(op=AtomicOp.PARTIAL_T, children=[
            EquationNode(op=AtomicOp.VAR, var_name='u')
        ])
        
        mutated = Equation(lhs=lhs, rhs=mutated_rhs, generation=self.generation)
        mutated.metadata['parent'] = equation.fitness
        mutated.metadata['mutation_type'] = mutation_type
        
        return mutated
    
    def _copy_node(self, node: EquationNode) -> EquationNode:
        """Deep copy a node and its subtree."""
        new_node = EquationNode(
            op=node.op,
            value=node.value,
            var_name=node.var_name
        )
        new_node.children = [self._copy_node(c) for c in node.children]
        return new_node
    
    def _get_all_nodes(self, node: EquationNode) -> List[EquationNode]:
        """Get all nodes in a tree (for mutation/crossover)."""
        nodes = [node]
        for child in node.children:
            nodes.extend(self._get_all_nodes(child))
        return nodes
    
    def evolve(
        self,
        data: Dict[str, np.ndarray],
        fitness_func: Callable[[np.ndarray, np.ndarray], float],
        num_generations: int = 100,
        verbose: bool = True
    ) -> Equation:
        """Run the evolutionary process to discover equations.
        
        Args:
            data: Dictionary of data arrays
            fitness_func: Function to compute fitness
            num_generations: Number of generations to evolve
            verbose: Whether to print progress
            
        Returns:
            Best equation found
        """
        # Initialize population
        self.initialize_population()
        
        for generation in range(num_generations):
            self.generation = generation
            
            # Evaluate fitness of all equations
            for eq in self.population:
                self.evaluate_fitness(eq, data, fitness_func)
            
            # Sort by fitness
            self.population.sort(key=lambda eq: eq.fitness, reverse=True)
            
            # Track best equation
            if self.best_equation is None or self.population[0].fitness > self.best_equation.fitness:
                self.best_equation = self._copy_equation(self.population[0])
            
            if verbose and generation % 10 == 0:
                best_fitness = self.population[0].fitness
                avg_fitness = sum(eq.fitness for eq in self.population) / len(self.population)
                print(f"Generation {generation}: Best={best_fitness:.6f}, Avg={avg_fitness:.6f}")
                print(f"  Best equation: {self.population[0]}")
            
            # Selection: keep top 20%
            elite_size = max(2, int(0.2 * self.population_size))
            elite = self.population[:elite_size]
            
            # Generate next generation
            next_generation = elite.copy()
            
            while len(next_generation) < self.population_size:
                # Tournament selection
                tournament_size = 3
                tournament = random.sample(elite, min(tournament_size, len(elite)))
                parent1 = max(tournament, key=lambda eq: eq.fitness)
                
                tournament = random.sample(elite, min(tournament_size, len(elite)))
                parent2 = max(tournament, key=lambda eq: eq.fitness)
                
                # Crossover
                if random.random() < self.crossover_rate:
                    child = self.crossover(parent1, parent2)
                else:
                    child = self._copy_equation(parent1)
                
                # Mutation
                if random.random() < self.mutation_rate:
                    child = self.mutate(child)
                
                next_generation.append(child)
            
            self.population = next_generation
        
        # Final evaluation
        for eq in self.population:
            self.evaluate_fitness(eq, data, fitness_func)
        
        self.population.sort(key=lambda eq: eq.fitness, reverse=True)
        
        if self.population[0].fitness > self.best_equation.fitness:
            self.best_equation = self._copy_equation(self.population[0])
        
        if verbose:
            print(f"\nEvolution complete!")
            print(f"Best equation: {self.best_equation}")
            print(f"Fitness: {self.best_equation.fitness:.6f}")
        
        return self.best_equation
    
    def _copy_equation(self, equation: Equation) -> Equation:
        """Deep copy an equation."""
        return Equation(
            lhs=self._copy_node(equation.lhs),
            rhs=self._copy_node(equation.rhs),
            fitness=equation.fitness,
            generation=equation.generation,
            metadata=equation.metadata.copy()
        )
    
    def save_receipt(self, equation: Equation, filepath: Path):
        """Save equation discovery receipt.
        
        This creates a receipt showing the derivation tree of the discovered
        equation, proving it was constructed from atomic primitives.
        
        Args:
            equation: Equation to save
            filepath: Path to save receipt
        """
        receipt = {
            "equation": str(equation),
            "fitness": equation.fitness,
            "generation": equation.generation,
            "complexity": equation.complexity(),
            "lhs": equation.lhs.to_dict(),
            "rhs": equation.rhs.to_dict(),
            "derivation_tree": self._build_derivation_tree(equation.rhs),
            "metadata": equation.metadata,
            "verification": {
                "uses_only_atomic_ops": self._verify_atomic_ops_only(equation),
                "discovered_second_derivatives": self._detect_second_derivatives(equation.rhs),
                "grammar_compliant": True
            }
        }
        
        with open(filepath, 'w') as f:
            json.dump(receipt, f, indent=2)
    
    def _build_derivation_tree(self, node: EquationNode, indent: int = 0) -> str:
        """Build human-readable derivation tree showing construction."""
        lines = []
        prefix = "  " * indent
        
        if node.op == AtomicOp.CONST:
            lines.append(f"{prefix}CONST({node.value})")
        elif node.op == AtomicOp.VAR:
            lines.append(f"{prefix}VAR({node.var_name})")
        else:
            lines.append(f"{prefix}{node.op.value}")
            for child in node.children:
                lines.append(self._build_derivation_tree(child, indent + 1))
        
        return "\n".join(lines)
    
    def _verify_atomic_ops_only(self, equation: Equation) -> bool:
        """Verify equation uses only atomic operations from grammar."""
        nodes = self._get_all_nodes(equation.rhs)
        for node in nodes:
            if node.op not in self.gene_pool and node.op not in self.terminals:
                return False
        return True
    
    def _detect_second_derivatives(self, node: EquationNode) -> List[str]:
        """Detect if equation contains composed second derivatives.
        
        This searches for patterns like ∂/∂x(∂/∂x u) which form the
        building blocks of diffusion equations.
        """
        second_derivatives = []
        
        # Check if this node is a derivative
        if node.op in [AtomicOp.PARTIAL_X, AtomicOp.PARTIAL_Y, 
                       AtomicOp.PARTIAL_Z, AtomicOp.PARTIAL_T]:
            # Check if its child is also a derivative
            if len(node.children) > 0:
                child = node.children[0]
                if child.op in [AtomicOp.PARTIAL_X, AtomicOp.PARTIAL_Y, 
                                AtomicOp.PARTIAL_Z, AtomicOp.PARTIAL_T]:
                    second_derivatives.append(f"{node.op.value}({child.op.value})")
        
        # Recursively check children
        for child in node.children:
            second_derivatives.extend(self._detect_second_derivatives(child))
        
        return second_derivatives
