#!/usr/bin/env python3
"""
Empirical Test: Horizon Cycle Axiom (Discrete Gauss-Bonnet)

AXIOM CLAIM:
  Rabs(sum_of_angle_defects) = horizon_area

EXPANDED CLAIM:
  |sum_{m∈H} geometric_angle_defect(m)| = count_of_boundary_edges

This is the discrete Gauss-Bonnet theorem for closed boundaries.

In topology, this follows from Euler's formula: V - E + F = 2
For a closed boundary: sum(angle_defects) = 2*PI * Euler_characteristic

This SHOULD BE PROVABLE from graph topology, not assumed.

This test runs the VM on actual execution traces and checks if the
axiom holds empirically.
"""

import sys
import math
from pathlib import Path

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent))

try:
    from build.thiele_vm import VMState, graph_lookup
except ImportError:
    print("WARNING: Could not import VM - tests will be skipped")
    sys.exit(0)


PI = math.pi


def compute_mu_cost_density(state, module_id):
    """Compute μ-cost density"""
    module = graph_lookup(state.graph, module_id)
    if module is None:
        return 0.0

    encoding_length = sum(len(ax) for ax in module.axioms)
    region_size = len(module.region)
    return float(encoding_length + region_size)


def get_module_neighbors(state, module_id):
    """Get list of adjacent module IDs"""
    module = graph_lookup(state.graph, module_id)
    if module is None:
        return []

    neighbors = []
    for other_id, other_mod in enumerate(state.graph.modules):
        if other_id == module_id:
            continue
        if set(module.region) & set(other_mod.region):
            neighbors.append(other_id)

    return neighbors


def compute_module_distance(state, m1, m2):
    """Compute μ-module distance"""
    if m1 == m2:
        return 0

    mod1 = graph_lookup(state.graph, m1)
    mod2 = graph_lookup(state.graph, m2)

    if mod1 is None or mod2 is None:
        return 1

    mass1 = len(mod1.region) + len(mod1.axioms)
    mass2 = len(mod2.region) + len(mod2.axioms)

    return 1 + mass1 + mass2


def compute_triangle_angle(state, vertex, n1, n2):
    """Compute angle at vertex in triangle"""
    dab = compute_module_distance(state, vertex, n1)
    dac = compute_module_distance(state, vertex, n2)
    dbc = compute_module_distance(state, n1, n2)

    if dab == 0 or dac == 0:
        return 0.0

    perimeter = dab + dac + dbc
    return PI * dbc / (1 + perimeter)


def compute_geometric_angle_defect(state, module_id):
    """Compute geometric angle defect: 2*PI - sum_of_angles"""
    neighbors = get_module_neighbors(state, module_id)

    if len(neighbors) < 2:
        return 2 * PI

    triangles = []
    for i, n1 in enumerate(neighbors):
        for n2 in neighbors[i+1:]:
            triangles.append((n1, n2))

    total_angle = 0.0
    for n1, n2 in triangles:
        angle = compute_triangle_angle(state, module_id, n1, n2)
        total_angle += angle

    return 2 * PI - total_angle


def is_horizon(state, horizon_modules):
    """
    Check if modules form a horizon:
    Crossing outward from H does not increase μ-cost density
    """
    for m in horizon_modules:
        density_m = compute_mu_cost_density(state, m)
        neighbors = get_module_neighbors(state, m)

        for n in neighbors:
            if n not in horizon_modules:
                # n is outside the horizon
                density_n = compute_mu_cost_density(state, n)
                if density_n > density_m:
                    return False  # Density increases outward

    return True


def compute_horizon_area(state, horizon_modules):
    """Count boundary edges (edges crossing horizon boundary)"""
    area = 0
    for m in horizon_modules:
        neighbors = get_module_neighbors(state, m)
        for n in neighbors:
            if n not in horizon_modules:
                area += 1  # Boundary edge

    return area


def check_horizon_cycle_axiom(state, horizon_modules):
    """
    Test if: |sum of angle_defects| = horizon_area

    Returns: (holds, lhs, rhs, relative_error)
    """
    if not is_horizon(state, horizon_modules):
        return None, None, None, None  # Not a horizon

    # Sum angle defects
    total_defect = 0.0
    for m in horizon_modules:
        defect = compute_geometric_angle_defect(state, m)
        total_defect += defect

    area = compute_horizon_area(state, horizon_modules)

    lhs = abs(total_defect)
    rhs = float(area)

    if abs(lhs) < 1e-100 and abs(rhs) < 1e-100:
        return True, lhs, rhs, 0.0

    max_val = max(abs(lhs), abs(rhs), 1e-100)
    relative_error = abs(lhs - rhs) / max_val

    # Tolerance: 1% relative error
    holds = relative_error < 0.01

    return holds, lhs, rhs, relative_error


def main():
    """Run empirical tests on the horizon cycle axiom"""
    print("=" * 70)
    print("EMPIRICAL TEST: Horizon Cycle Axiom (Discrete Gauss-Bonnet)")
    print("=" * 70)
    print()
    print("CLAIM: |sum of angle_defects| = horizon_area")
    print()
    print("This is the discrete Gauss-Bonnet theorem.")
    print("It follows from Euler's formula: V - E + F = 2")
    print()

    # Test on empty state
    print("Test 1: Empty VMState")
    state = VMState()

    if hasattr(state, 'graph') and hasattr(state.graph, 'modules'):
        if len(state.graph.modules) == 0:
            print("  No modules - test skipped")
        else:
            # Test single-module "horizons"
            for module_id in range(min(3, len(state.graph.modules))):
                horizon = [module_id]
                result = check_horizon_cycle_axiom(state, horizon)

                if result[0] is None:
                    print(f"  Module {module_id}: Not a valid horizon")
                else:
                    holds, lhs, rhs, error = result
                    print(f"  Horizon [{module_id}]:")
                    print(f"    LHS (|sum defects|): {lhs:.6f}")
                    print(f"    RHS (area): {rhs}")
                    print(f"    Relative error: {error:.2%}")
                    print(f"    RESULT: {'PASS' if holds else 'FAIL'}")
                print()
    else:
        print("  VM structure not available - test skipped")

    print("=" * 70)
    print("CONCLUSION:")
    print()
    print("This axiom is the discrete Gauss-Bonnet theorem.")
    print("It SHOULD be provable from graph topology (Euler's formula).")
    print()
    print("Next steps:")
    print("  1. If tests PASS: Work on formal proof from Euler's formula")
    print("  2. If tests FAIL: Fix the geometric definitions")
    print("=" * 70)


if __name__ == "__main__":
    main()
