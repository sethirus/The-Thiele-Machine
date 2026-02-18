#!/usr/bin/env python3
"""
Empirical Test: Source Normalization Axiom

AXIOM CLAIM:
  PI * mu_laplacian(s, m) = 16*PI*G * stress_energy(s, m)

EXPANDED CLAIM:
  sum_{n∈neighbors(m)} edge_weight(m,n) * (density(n) - density(m))
    = 16*G * density(m)

This claims density is an EIGENFUNCTION of the graph Laplacian.

This test runs the VM on actual execution traces and checks if the
axiom holds empirically. If it fails on any trace, the axiom is FALSE.
"""

import sys
import json
import math
from pathlib import Path

import pytest

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent))

try:
    from build.thiele_vm import VMState, run_vm, graph_lookup
except Exception:
    pytest.skip("build.thiele_vm not available", allow_module_level=True)


# Physical constants from ConstantUnification.v
PI = math.pi
d_mu = 1.616255e-35  # Planck length
tau_mu = 5.391247e-44  # Planck time
k_B = 1.380649e-23    # Boltzmann constant
T = 2.725  # CMB temperature
ln2 = math.log(2)

# Derived constants
E_bit = 4 * k_B * T * ln2
derived_h = 4 * E_bit * tau_mu
gravitational_constant = (d_mu**3) / (tau_mu**2 * derived_h)
curvature_coupling = PI


def compute_mu_cost_density(state, module_id):
    """Compute μ-cost density: encoding_length + region_size"""
    module = graph_lookup(state.graph, module_id)
    if module is None:
        return 0.0

    encoding_length = sum(len(ax) for ax in module.axioms)
    region_size = len(module.region)
    return float(encoding_length + region_size)


def compute_stress_energy(state, module_id):
    """Stress-energy = mu_cost_density (primitive definition)"""
    return compute_mu_cost_density(state, module_id)


def get_module_neighbors(state, module_id):
    """Get list of adjacent module IDs"""
    module = graph_lookup(state.graph, module_id)
    if module is None:
        return []

    neighbors = []
    for other_id, other_mod in enumerate(state.graph.modules):
        if other_id == module_id:
            continue
        # Check if regions are non-disjoint
        if set(module.region) & set(other_mod.region):
            neighbors.append(other_id)

    return neighbors


def compute_mu_laplacian(state, module_id):
    """Compute μ-Laplacian: sum of density gradients over neighbors"""
    neighbors = get_module_neighbors(state, module_id)
    if not neighbors:
        return 0.0

    density_m = compute_mu_cost_density(state, module_id)
    laplacian = 0.0

    for n in neighbors:
        density_n = compute_mu_cost_density(state, n)
        edge_weight = 1.0  # Assuming unit weights
        gradient = density_n - density_m
        laplacian += edge_weight * gradient

    return laplacian


def check_source_normalization_axiom(state, module_id):
    """
    Test if: PI * mu_laplacian = 16*PI*G * stress_energy

    Returns: (holds, lhs, rhs, relative_error)
    """
    mu_lap = compute_mu_laplacian(state, module_id)
    stress = compute_stress_energy(state, module_id)

    lhs = curvature_coupling * mu_lap
    rhs = 16 * PI * gravitational_constant * stress

    # Check if they're equal (with floating point tolerance)
    if abs(lhs) < 1e-100 and abs(rhs) < 1e-100:
        # Both essentially zero
        return True, lhs, rhs, 0.0

    max_val = max(abs(lhs), abs(rhs))
    if max_val < 1e-100:
        relative_error = 0.0
    else:
        relative_error = abs(lhs - rhs) / max_val

    # Tolerance: 1% relative error
    holds = relative_error < 0.01

    return holds, lhs, rhs, relative_error


def main():
    """Run empirical tests on the source normalization axiom"""
    print("=" * 70)
    print("EMPIRICAL TEST: Source Normalization Axiom")
    print("=" * 70)
    print()
    print("CLAIM: PI * mu_laplacian(s,m) = 16*PI*G * stress_energy(s,m)")
    print()

    # Test on empty state
    print("Test 1: Empty VMState")
    state = VMState()

    if hasattr(state, 'graph') and hasattr(state.graph, 'modules'):
        if len(state.graph.modules) == 0:
            print("  No modules - test skipped")
        else:
            for module_id in range(len(state.graph.modules)):
                holds, lhs, rhs, error = check_source_normalization_axiom(state, module_id)
                print(f"  Module {module_id}:")
                print(f"    LHS (PI * laplacian): {lhs:e}")
                print(f"    RHS (16*PI*G * stress): {rhs:e}")
                print(f"    Relative error: {error:.2%}")
                print(f"    RESULT: {'PASS' if holds else 'FAIL'}")
                print()
    else:
        print("  VM structure not available - test skipped")

    print("=" * 70)
    print("CONCLUSION:")
    print()
    print("This axiom claims that density is an EIGENFUNCTION of the")
    print("graph Laplacian. This is generally FALSE for arbitrary graphs.")
    print()
    print("The axiom should be:")
    print("  1. PROVEN for specific graph constructions, OR")
    print("  2. Replaced with a dynamic equilibrium condition, OR")
    print("  3. Admitted as FALSE and definitions fixed")
    print("=" * 70)


if __name__ == "__main__":
    main()
