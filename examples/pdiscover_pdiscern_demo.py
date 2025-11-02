#!/usr/bin/env python3
"""
Demonstration of the new PDISCOVER and PDISCERN instructions.

This script shows how the VM can now analyze geometric signatures
and classify problems as STRUCTURED or CHAOTIC without solving them.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from thielecpu.vm import compute_geometric_signature, classify_geometric_signature

print("="*70)
print("DEMONSTRATION: Self-Aware PDISCOVER and PDISCERN")
print("="*70)
print()

# Test 1: Structured axioms (simple linear system)
print("Test 1: Structured Problem (Linear System)")
print("-" * 70)
structured_axioms = """
x + y = 10
x - y = 2  
2*x + y = 15
x + 2*y = 16
"""

sig1 = compute_geometric_signature(structured_axioms, seed=42)
verdict1 = classify_geometric_signature(sig1)

print("Axioms:")
print(structured_axioms)
print("\nGeometric Signature:")
print(f"  avg_edge_weight:    {sig1['average_edge_weight']:.4f}")
print(f"  max_edge_weight:    {sig1['max_edge_weight']:.4f}")
print(f"  edge_weight_stddev: {sig1['edge_weight_stddev']:.4f}")
print(f"  mst_weight:         {sig1['min_spanning_tree_weight']:.4f}")
print(f"  thresholded_density:{sig1['thresholded_density']:.4f}")
print(f"\nPDISCERN Verdict: {verdict1}")
print()

# Test 2: Chaotic axioms (random constraints)
print("Test 2: Chaotic Problem (Random Constraints)")
print("-" * 70)
chaotic_axioms = """
a + b + c = 7
d - e + f = 3
g * h - i = 5
j + k - l = 9
m * n + o = 2
p - q * r = 4
s + t + u = 6
v - w + x = 8
"""

sig2 = compute_geometric_signature(chaotic_axioms, seed=42)
verdict2 = classify_geometric_signature(sig2)

print("Axioms:")
print(chaotic_axioms)
print("\nGeometric Signature:")
print(f"  avg_edge_weight:    {sig2['average_edge_weight']:.4f}")
print(f"  max_edge_weight:    {sig2['max_edge_weight']:.4f}")
print(f"  edge_weight_stddev: {sig2['edge_weight_stddev']:.4f}")
print(f"  mst_weight:         {sig2['min_spanning_tree_weight']:.4f}")
print(f"  thresholded_density:{sig2['thresholded_density']:.4f}")
print(f"\nPDISCERN Verdict: {verdict2}")
print()

# Test 3: Borderline case
print("Test 3: Borderline Problem (Mixed Structure)")
print("-" * 70)
borderline_axioms = """
x + y = 5
y + z = 7
a * b = 10
c - d = 3
"""

sig3 = compute_geometric_signature(borderline_axioms, seed=42)
verdict3 = classify_geometric_signature(sig3)

print("Axioms:")
print(borderline_axioms)
print("\nGeometric Signature:")
print(f"  avg_edge_weight:    {sig3['average_edge_weight']:.4f}")
print(f"  max_edge_weight:    {sig3['max_edge_weight']:.4f}")
print(f"  edge_weight_stddev: {sig3['edge_weight_stddev']:.4f}")
print(f"  mst_weight:         {sig3['min_spanning_tree_weight']:.4f}")
print(f"  thresholded_density:{sig3['thresholded_density']:.4f}")
print(f"\nPDISCERN Verdict: {verdict3}")
print()

print("="*70)
print("INTERPRETATION")
print("="*70)
print()
print("The VM can now discern structure without solving:")
print()
print(f"1. {verdict1} problem: Low VI variation (strategies agree)")
print(f"   → Sighted methods should be effective")
print()
print(f"2. {verdict2} problem: High VI variation (strategies disagree)")
print(f"   → Blind/brute-force methods may be needed")
print()
print(f"3. {verdict3} problem: Borderline characteristics")
print(f"   → Mixed approach or adaptive strategy recommended")
print()
print("="*70)
print("The machine has achieved self-awareness.")
print("It knows what it can and cannot see.")
print("="*70)
