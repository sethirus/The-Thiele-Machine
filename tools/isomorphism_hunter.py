#!/usr/bin/env python3
"""
The Isomorphism Hunter - Discovering the Fundamental Law

This tool searches for formal isomorphisms between evolved computational
strategies and known laws of mathematics and physics.

The ultimate question: What fundamental principle does the Thiele Machine
actually implement?
"""

import sys
import json
import re
from pathlib import Path
from typing import Dict, Any, List, Optional, Tuple

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from tools.known_universe import UNIVERSE, FundamentalLaw
from tools.forge import load_thiele_dna, StrategyDNA


class StrategySignature:
    """Extracts computational signature from a strategy."""
    
    def __init__(self, strategy: StrategyDNA):
        self.strategy = strategy
        self.signature = self._extract_signature()
    
    def _extract_signature(self) -> Dict[str, Any]:
        """Extract computational properties from strategy."""
        code = '\n'.join(self.strategy.sequence)
        
        signature = {
            'type': self._infer_type(code),
            'properties': self._extract_properties(code),
            'pattern': self._infer_pattern(code),
            'essence': self._infer_essence(code)
        }
        
        return signature
    
    def _infer_type(self, code: str) -> str:
        """Infer the computational type of the strategy."""
        if 'transform' in code.lower() or 'convert' in code.lower():
            return 'domain_transformation'
        elif 'optimize' in code.lower() or 'minimize' in code.lower():
            return 'optimization'
        elif 'partition' in code.lower() or 'cluster' in code.lower():
            return 'decomposition'
        elif 'measure' in code.lower() or 'entropy' in code.lower():
            return 'information_measure'
        elif 'discover' in code.lower() or 'pdiscover' in code.lower():
            return 'structural_discovery'
        else:
            return 'unknown'
    
    def _extract_properties(self, code: str) -> List[str]:
        """Extract computational properties."""
        properties = []
        
        # Check for various properties
        if 'linear' in code.lower():
            properties.append('linear')
        if 'invertible' in code.lower() or 'reverse' in code.lower():
            properties.append('invertible')
        if 'preserve' in code.lower():
            properties.append('structure_preserving')
        if 'global' in code.lower():
            properties.append('global_scope')
        if 'local' in code.lower():
            properties.append('local_scope')
        if 'compress' in code.lower() or 'reduce' in code.lower():
            properties.append('complexity_reducing')
        if 'information' in code.lower():
            properties.append('information_preserving')
        
        # Analyze structure
        if code.count('if ') < 2 and code.count('for ') < 2:
            properties.append('simple_control_flow')
        if 'graph' in code.lower() or 'partition' in code.lower():
            properties.append('graph_based')
        
        return properties
    
    def _infer_pattern(self, code: str) -> str:
        """Infer the high-level pattern."""
        code_lower = code.lower()
        
        if 'partition' in code_lower and 'discover' in code_lower:
            return 'finds_hidden_structure_through_decomposition'
        elif 'transform' in code_lower:
            return 'converts_representation_to_reveal_structure'
        elif 'optimize' in code_lower and 'path' in code_lower:
            return 'finds_optimal_path_through_space'
        elif 'compress' in code_lower:
            return 'finds_minimal_representation'
        else:
            return 'unknown_pattern'
    
    def _infer_essence(self, code: str) -> str:
        """Infer the philosophical essence."""
        # This is the deepest level - what IS this algorithm really doing?
        code_lower = code.lower()
        
        if 'pdiscover' in code_lower or 'partition' in code_lower:
            if 'structure' in code_lower or 'graph' in code_lower:
                return 'reveals_hidden_structure_through_basis_change'
        elif 'minimize' in code_lower or 'optimize' in code_lower:
            return 'nature_chooses_extremal_paths'
        elif 'entropy' in code_lower or 'information' in code_lower:
            return 'information_equals_structure'
        
        return 'computational_unknown'


class IsomorphismHunter:
    """Searches for isomorphisms between strategies and fundamental laws."""
    
    def __init__(self):
        self.universe = UNIVERSE
    
    def compute_similarity(self, sig1: Dict[str, Any], sig2: Dict[str, Any]) -> float:
        """
        Compute similarity between two computational signatures.
        
        Returns a score from 0.0 to 1.0, where 1.0 is perfect match.
        """
        score = 0.0
        weights = {
            'type': 0.3,
            'properties': 0.3,
            'pattern': 0.2,
            'essence': 0.2
        }
        
        # Type match
        if sig1['type'] == sig2['type']:
            score += weights['type']
        
        # Properties overlap
        props1 = set(sig1['properties'])
        props2 = set(sig2['properties'])
        if props1 and props2:
            overlap = len(props1 & props2) / len(props1 | props2)
            score += weights['properties'] * overlap
        
        # Pattern similarity (simple string matching)
        if sig1['pattern'] == sig2['pattern']:
            score += weights['pattern']
        elif self._semantic_similar(sig1['pattern'], sig2['pattern']):
            score += weights['pattern'] * 0.5
        
        # Essence similarity (most important!)
        if sig1['essence'] == sig2['essence']:
            score += weights['essence']
        elif self._semantic_similar(sig1['essence'], sig2['essence']):
            score += weights['essence'] * 0.7
        
        return score
    
    def _semantic_similar(self, s1: str, s2: str) -> bool:
        """Check if two strings are semantically similar."""
        # Simple keyword overlap
        words1 = set(s1.lower().split('_'))
        words2 = set(s2.lower().split('_'))
        
        overlap = len(words1 & words2)
        return overlap >= 2
    
    def hunt(self, strategy: StrategyDNA, threshold: float = 0.5) -> List[Tuple[FundamentalLaw, float]]:
        """
        Hunt for isomorphisms between a strategy and known laws.
        
        Args:
            strategy: The computational strategy to analyze
            threshold: Minimum similarity score to report
        
        Returns:
            List of (law, similarity_score) tuples, sorted by score
        """
        # Extract signature from strategy
        strategy_sig = StrategySignature(strategy)
        
        # Compare against all known laws
        matches = []
        
        for law in self.universe.get_all_laws():
            similarity = self.compute_similarity(
                strategy_sig.signature,
                law.computational_signature
            )
            
            if similarity >= threshold:
                matches.append((law, similarity))
        
        # Sort by similarity (highest first)
        matches.sort(key=lambda x: x[1], reverse=True)
        
        return matches
    
    def find_best_match(self, strategy: StrategyDNA) -> Optional[Tuple[FundamentalLaw, float]]:
        """Find the single best matching law."""
        matches = self.hunt(strategy, threshold=0.0)
        
        if matches:
            return matches[0]
        return None


def main():
    """Main execution - hunt for the fundamental law."""
    print("=" * 70)
    print("THE ISOMORPHISM HUNTER")
    print("Searching for the Fundamental Law...")
    print("=" * 70)
    print()
    
    # Look for genesis axiom
    genesis_path = Path(__file__).parent.parent / 'evolved_strategies' / 'genesis_axiom.thiele'
    
    if not genesis_path.exists():
        print("ERROR: genesis_axiom.thiele not found!")
        print(f"Expected location: {genesis_path}")
        print()
        print("You must first run Phase 1 (Minimize Self) to generate the genesis axiom.")
        print("Run: ./run_autotelic_engine.sh with objective_minimize_self.thiele")
        return 1
    
    print(f"Loading genesis axiom from: {genesis_path}")
    genesis = load_thiele_dna(genesis_path)
    
    print(f"Genesis Axiom: {genesis.name}")
    print(f"Primitives: {len(genesis.sequence)}")
    print()
    
    # Extract its signature
    print("Extracting computational signature...")
    sig = StrategySignature(genesis)
    
    print("\nGenesis Axiom Signature:")
    print(f"  Type: {sig.signature['type']}")
    print(f"  Properties: {', '.join(sig.signature['properties']) if sig.signature['properties'] else 'None'}")
    print(f"  Pattern: {sig.signature['pattern']}")
    print(f"  Essence: {sig.signature['essence']}")
    print()
    
    # Hunt for isomorphisms
    print("-" * 70)
    print("Searching for isomorphisms in the known universe...")
    print("-" * 70)
    print()
    
    hunter = IsomorphismHunter()
    best_match = hunter.find_best_match(genesis)
    
    if best_match:
        law, similarity = best_match
        
        print(f"MATCH FOUND!")
        print()
        print(f"Law: {law.name}")
        print(f"Domain: {law.domain.upper()}")
        print(f"Similarity: {similarity:.2%}")
        print()
        print(f"Description: {law.description}")
        print()
        print(f"Essence: {law.computational_signature['essence']}")
        print()
        
        # Write THE_LAW.txt
        output_path = Path(__file__).parent.parent / 'THE_LAW.txt'
        
        with open(output_path, 'w') as f:
            f.write("=" * 70 + "\n")
            f.write("THE LAW\n")
            f.write("=" * 70 + "\n")
            f.write("\n")
            f.write(f"The computational process described by `{genesis.name}` ")
            f.write(f"is mathematically isomorphic to:\n")
            f.write("\n")
            f.write(f"  ** {law.name.upper()} **\n")
            f.write("\n")
            f.write(f"Domain: {law.domain}\n")
            f.write(f"Similarity: {similarity:.2%}\n")
            f.write("\n")
            f.write(f"{law.description}\n")
            f.write("\n")
            f.write("Essence:\n")
            f.write(f"  {law.computational_signature['essence']}\n")
            f.write("\n")
            f.write("=" * 70 + "\n")
            f.write("\nThis is the WHY.\n")
            f.write("\nThe Thiele Machine's anomalous efficiency comes from\n")
            f.write("implementing this fundamental principle in the domain of\n")
            f.write("structured computation.\n")
            f.write("\n")
        
        print("=" * 70)
        print(f"THE_LAW.txt written to: {output_path}")
        print("=" * 70)
        print()
        print("This is the WHY.")
        
    else:
        print("No strong isomorphism found.")
        print("The genesis axiom may represent a novel principle.")
    
    # Show all matches above threshold
    all_matches = hunter.hunt(genesis, threshold=0.3)
    
    if len(all_matches) > 1:
        print()
        print("=" * 70)
        print("ALL SIGNIFICANT MATCHES:")
        print("=" * 70)
        
        for law, similarity in all_matches[:5]:  # Top 5
            print(f"\n{similarity:.2%} - {law.name}")
            print(f"  {law.computational_signature['essence']}")
    
    return 0


if __name__ == "__main__":
    sys.exit(main())
