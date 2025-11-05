#!/usr/bin/env python3
"""
The Known Universe - A Library of Fundamental Laws

This module contains computable representations of fundamental mathematical
and physical laws that can be compared against computational strategies
to find isomorphisms.
"""

import numpy as np
from typing import Dict, Any, Callable, List
from dataclasses import dataclass


@dataclass
class FundamentalLaw:
    """Represents a fundamental law of mathematics or physics."""
    name: str
    domain: str  # 'mathematics' or 'physics'
    description: str
    computational_signature: Dict[str, Any]
    

class KnownUniverse:
    """Container for all known fundamental laws."""
    
    def __init__(self):
        self.laws: List[FundamentalLaw] = []
        self._initialize_mathematics()
        self._initialize_physics()
    
    def _initialize_mathematics(self):
        """Initialize mathematical laws."""
        
        # Fourier Transform
        self.laws.append(FundamentalLaw(
            name="Fourier Transform",
            domain="mathematics",
            description="Transforms a function from time/space domain to frequency domain",
            computational_signature={
                'type': 'domain_transformation',
                'properties': [
                    'linear',
                    'invertible',
                    'complexity_reducing',
                    'information_preserving'
                ],
                'pattern': 'converts_local_to_global',
                'essence': 'reveals_hidden_structure_through_basis_change'
            }
        ))
        
        # Principle of Least Action (Mathematical formulation)
        self.laws.append(FundamentalLaw(
            name="Variational Calculus / Principle of Least Action",
            domain="mathematics",
            description="Path that extremizes action functional",
            computational_signature={
                'type': 'optimization',
                'properties': [
                    'global_optimization',
                    'path_selection',
                    'extremal_principle'
                ],
                'pattern': 'finds_optimal_path_through_space',
                'essence': 'nature_chooses_extremal_paths'
            }
        ))
        
        # Information Theory - Entropy
        self.laws.append(FundamentalLaw(
            name="Shannon Entropy / Information Theory",
            domain="mathematics",
            description="Quantifies information content and uncertainty",
            computational_signature={
                'type': 'information_measure',
                'properties': [
                    'uncertainty_quantification',
                    'compression_limit',
                    'optimal_encoding'
                ],
                'pattern': 'measures_structure_vs_randomness',
                'essence': 'information_equals_surprise'
            }
        ))
        
        # Graph Isomorphism
        self.laws.append(FundamentalLaw(
            name="Graph Isomorphism",
            domain="mathematics",
            description="Structure-preserving bijection between graphs",
            computational_signature={
                'type': 'structural_equivalence',
                'properties': [
                    'preserves_adjacency',
                    'preserves_structure',
                    'reveals_symmetry'
                ],
                'pattern': 'finds_structural_equivalence',
                'essence': 'different_labels_same_structure'
            }
        ))
        
        # Spectral Decomposition
        self.laws.append(FundamentalLaw(
            name="Spectral Decomposition / Eigenvalue Decomposition",
            domain="mathematics",
            description="Decomposes operator into eigenvalues and eigenvectors",
            computational_signature={
                'type': 'decomposition',
                'properties': [
                    'reveals_invariant_directions',
                    'diagonalization',
                    'basis_transformation'
                ],
                'pattern': 'finds_natural_coordinates',
                'essence': 'reveals_intrinsic_structure'
            }
        ))
        
        # Kolmogorov Complexity
        self.laws.append(FundamentalLaw(
            name="Kolmogorov Complexity / Algorithmic Information",
            domain="mathematics",
            description="Shortest program that generates a string",
            computational_signature={
                'type': 'complexity_measure',
                'properties': [
                    'incompressibility',
                    'randomness_definition',
                    'minimal_description'
                ],
                'pattern': 'finds_minimal_representation',
                'essence': 'true_complexity_is_description_length'
            }
        ))
    
    def _initialize_physics(self):
        """Initialize physical laws."""
        
        # Thermodynamic Entropy
        self.laws.append(FundamentalLaw(
            name="Second Law of Thermodynamics / Entropy",
            domain="physics",
            description="Entropy of isolated system never decreases",
            computational_signature={
                'type': 'thermodynamic_principle',
                'properties': [
                    'irreversibility',
                    'disorder_increase',
                    'information_loss'
                ],
                'pattern': 'systems_evolve_toward_equilibrium',
                'essence': 'nature_forgets_through_coarse_graining'
            }
        ))
        
        # Landauer's Principle
        self.laws.append(FundamentalLaw(
            name="Landauer's Principle",
            domain="physics",
            description="Erasing information costs energy kT ln 2",
            computational_signature={
                'type': 'thermodynamic_computing',
                'properties': [
                    'information_energy_equivalence',
                    'irreversibility_cost',
                    'physical_computation_bound'
                ],
                'pattern': 'computation_has_thermodynamic_cost',
                'essence': 'information_is_physical'
            }
        ))
        
        # Principle of Least Action (Physics)
        self.laws.append(FundamentalLaw(
            name="Hamilton's Principle of Least Action",
            domain="physics",
            description="Physical systems evolve along paths of stationary action",
            computational_signature={
                'type': 'variational_principle',
                'properties': [
                    'path_optimization',
                    'global_causality',
                    'extremal_evolution'
                ],
                'pattern': 'nature_optimizes_action',
                'essence': 'physics_is_an_optimization_problem'
            }
        ))
        
        # Quantum Measurement / Collapse
        self.laws.append(FundamentalLaw(
            name="Quantum Measurement Collapse",
            domain="physics",
            description="Observation collapses superposition to eigenstate",
            computational_signature={
                'type': 'information_acquisition',
                'properties': [
                    'state_reduction',
                    'observation_effect',
                    'information_gain'
                ],
                'pattern': 'looking_changes_reality',
                'essence': 'measurement_creates_classical_information'
            }
        ))
        
        # Holographic Principle
        self.laws.append(FundamentalLaw(
            name="Holographic Principle",
            domain="physics",
            description="Information in volume encoded on boundary",
            computational_signature={
                'type': 'dimensional_reduction',
                'properties': [
                    'boundary_encoding',
                    'information_projection',
                    'dimensional_compression'
                ],
                'pattern': 'lower_dimension_contains_full_information',
                'essence': 'reality_is_holographic'
            }
        ))
    
    def get_all_laws(self) -> List[FundamentalLaw]:
        """Return all known laws."""
        return self.laws
    
    def get_laws_by_domain(self, domain: str) -> List[FundamentalLaw]:
        """Get laws from specific domain."""
        return [law for law in self.laws if law.domain == domain]


# Singleton instance
UNIVERSE = KnownUniverse()


if __name__ == "__main__":
    # Display all known laws
    print("=" * 70)
    print("THE KNOWN UNIVERSE - FUNDAMENTAL LAWS")
    print("=" * 70)
    print()
    
    universe = KnownUniverse()
    
    print("MATHEMATICS:")
    print("-" * 70)
    for law in universe.get_laws_by_domain('mathematics'):
        print(f"\n{law.name}")
        print(f"  {law.description}")
        print(f"  Essence: {law.computational_signature['essence']}")
    
    print("\n")
    print("PHYSICS:")
    print("-" * 70)
    for law in universe.get_laws_by_domain('physics'):
        print(f"\n{law.name}")
        print(f"  {law.description}")
        print(f"  Essence: {law.computational_signature['essence']}")
    
    print("\n")
    print("=" * 70)
    print(f"Total laws in library: {len(universe.get_all_laws())}")
    print("=" * 70)
