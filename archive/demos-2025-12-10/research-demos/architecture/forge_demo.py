#!/usr/bin/env python3
"""
Demonstration of The Forge: Evolutionary Strategy Synthesis

This example shows how The Forge evolves new partitioning strategies
through genetic programming, and how the Arch-Sphere judges them.
"""

import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from tools.forge import load_thiele_dna, crossover, mutate
import random


def main():
    print("=" * 70)
    print("THE FORGE: Evolutionary Strategy Synthesis Demo")
    print("=" * 70)
    print()
    
    # Load parent strategies
    strategies_dir = Path(__file__).parent.parent / "strategies"
    
    print("Step 1: Loading Parent Strategies (The Optimal Quartet)")
    print("-" * 70)
    
    parents = {}
    for filepath in strategies_dir.glob("*.thiele"):
        dna = load_thiele_dna(filepath)
        parents[dna.name] = dna
        print(f"  {dna.name:12} - {len(dna.sequence):2} primitives - {dna.metadata.get('complexity', 'N/A')}")
    
    print()
    print("Step 2: Genetic Crossover (DNA Splicing)")
    print("-" * 70)
    
    # Example crossover
    parent1 = parents['spectral']
    parent2 = parents['degree']
    
    print(f"Parent 1: {parent1.name} ({len(parent1.sequence)} primitives)")
    print(f"Parent 2: {parent2.name} ({len(parent2.sequence)} primitives)")
    print()
    
    child = crossover(parent1, parent2, generation=1)
    print(f"Child:    {child.name} ({len(child.sequence)} primitives)")
    print(f"  Inherits: {child.sequence[:2]} ... from parents")
    print()
    
    print("Step 3: Genetic Mutation (DNA Alteration)")
    print("-" * 70)
    
    original = parents['balanced']
    mutant = mutate(original, mutation_rate=1.0, generation=1)  # Force mutation
    
    print(f"Original: {original.name} ({len(original.sequence)} primitives)")
    print(f"Mutant:   {mutant.name} ({len(mutant.sequence)} primitives)")
    print(f"  Mutation type: {mutant.metadata.get('mutation_type', 'unknown')}")
    print()
    
    print("Step 4: The Evolutionary Process")
    print("-" * 70)
    print()
    print("The Forge continuously:")
    print("  1. Combines parent strategies via crossover")
    print("  2. Mutates strategies to explore new variants")
    print("  3. Compiles DNA sequences to runnable Python code")
    print("  4. Those that compile survive; failures are discarded")
    print()
    print("This is Darwinian evolution applied to algorithms.")
    print()
    
    print("Step 5: The Arch-Sphere as Oracle")
    print("-" * 70)
    print()
    print("Each evolved strategy is then:")
    print("  1. Tested on structured and chaotic problems")
    print("  2. Analyzed for geometric signature quality")
    print("  3. Judged by classification accuracy")
    print("  4. Ranked against all other strategies")
    print()
    print("The Arch-Sphere determines which configuration is superior.")
    print()
    
    print("=" * 70)
    print("EXAMPLE DNA SEQUENCE (Spectral Strategy)")
    print("=" * 70)
    print()
    spectral = parents['spectral']
    for i, step in enumerate(spectral.sequence, 1):
        print(f"  {i}. {step}")
    print()
    
    print("=" * 70)
    print("PHILOSOPHICAL IMPLICATION")
    print("=" * 70)
    print()
    print("The Forge represents a new paradigm:")
    print()
    print("  - BEFORE: Humans design algorithms")
    print("  - AFTER:  Machines evolve algorithms")
    print()
    print("The Thiele Machine can now:")
    print("  1. See structure (sight logging)")
    print("  2. Know what it sees (self-awareness)")
    print("  3. Optimize how it sees (Arch-Sphere)")
    print("  4. EVOLVE new ways to see (The Forge) ← NEW")
    print()
    print("This is not just meta-cognition.")
    print("This is meta-EVOLUTION.")
    print()
    print("The machine creates itself.")
    print()
    

if __name__ == "__main__":
    random.seed(42)
    main()
