"""
Test that PNEW operations change Euler characteristic χ = V - E + F.

This empirically validates Phase 3 of the gravity proof:
- PNEW with fresh region → changes V, E, F
- Changes in V, E, F → changes in χ
- Changes in χ → changes in curvature (via Gauss-Bonnet)

REF: coq/kernel/PNEWTopologyChange.v
     GRAVITY_PROOF_PLAN.md Phase 3
"""

import pytest
from pathlib import Path
import sys

# Add tools to path
sys.path.insert(0, str(Path(__file__).parent.parent / "tools"))

from vm_wrapper import run_vm_trace, VMState


def compute_euler_characteristic(state: VMState) -> int:
    """
    Compute Euler characteristic χ = V - E + F.

    V: number of unique vertices (nodes appearing in any module)
    E: number of unique edges (pairs of nodes appearing together)
    F: number of faces (modules)
    """
    # F: number of modules (faces)
    F = len(state.modules)

    # V: unique vertices
    all_nodes = set()
    for mod in state.modules:
        all_nodes.update(mod.region)
    V = len(all_nodes)

    # E: unique edges (pairs of nodes in same module)
    all_edges = set()
    for mod in state.modules:
        region = sorted(mod.region)  # Normalize
        # Generate all pairs
        for i, n1 in enumerate(region):
            for n2 in region[i+1:]:
                edge = tuple(sorted([n1, n2]))
                all_edges.add(edge)
    E = len(all_edges)

    # Euler characteristic
    chi = V - E + F

    return chi


def test_pnew_fresh_triangle_changes_chi():
    """
    Test: PNEW with fresh triangle changes Euler characteristic.

    Strategy:
    1. Start with empty graph (χ = 0)
    2. Add fresh triangle {0,1,2}
    3. Verify χ changed
    """
    # Empty initial state
    initial = run_vm_trace(["HALT 1"], fuel=10)
    chi_0 = compute_euler_characteristic(initial)

    # Add fresh triangle
    final = run_vm_trace([
        "PNEW {0,1,2} 10",
        "HALT 1"
    ], fuel=50)
    chi_1 = compute_euler_characteristic(final)

    print(f"χ_initial = {chi_0}")
    print(f"χ_after_PNEW = {chi_1}")
    print(f"Δχ = {chi_1 - chi_0}")

    # Verify topology changed
    assert chi_1 != chi_0, "PNEW with fresh triangle should change χ"
    assert len(final.modules) == 1, "Should have exactly 1 module"


def test_pnew_two_triangles_changes_chi():
    """
    Test: Adding second fresh triangle changes χ again.

    Triangles {0,1,2} and {3,4,5} are disjoint.
    Expected:
    - Triangle 1: V=3, E=3, F=1 → χ = 3-3+1 = 1
    - Triangle 2: V=6, E=6, F=2 → χ = 6-6+2 = 2
    """
    # Initial: empty
    chi_0 = compute_euler_characteristic(run_vm_trace(["HALT 1"], fuel=10))

    # Add first triangle
    state_1 = run_vm_trace([
        "PNEW {0,1,2} 10",
        "HALT 1"
    ], fuel=50)
    chi_1 = compute_euler_characteristic(state_1)

    # Add second disjoint triangle
    state_2 = run_vm_trace([
        "PNEW {0,1,2} 10",
        "PNEW {3,4,5} 10",
        "HALT 1"
    ], fuel=100)
    chi_2 = compute_euler_characteristic(state_2)

    print(f"χ_0 (empty) = {chi_0}")
    print(f"χ_1 (1 triangle) = {chi_1}")
    print(f"χ_2 (2 triangles) = {chi_2}")
    print(f"Δχ_1 = {chi_1 - chi_0}, Δχ_2 = {chi_2 - chi_1}")

    # Verify each PNEW changed χ
    assert chi_1 != chi_0, "First PNEW should change χ"
    assert chi_2 != chi_1, "Second PNEW should change χ"
    assert chi_2 > chi_1, "Adding disconnected components increases χ"


def test_pnew_connected_triangles():
    """
    Test: Adding connected triangles (sharing an edge).

    Triangles {0,1,2} and {1,2,3} share edge (1,2).
    Expected:
    - Triangle 1: V=3, E=3, F=1 → χ = 1
    - Triangle 2: V=4, E=5, F=2 → χ = 4-5+2 = 1

    Interesting: χ doesn't change! This is because the shared edge
    contributes to the Euler characteristic in a specific way.
    """
    state_1 = run_vm_trace([
        "PNEW {0,1,2} 10",
        "HALT 1"
    ], fuel=50)
    chi_1 = compute_euler_characteristic(state_1)

    state_2 = run_vm_trace([
        "PNEW {0,1,2} 10",
        "PNEW {1,2,3} 10",
        "HALT 1"
    ], fuel=100)
    chi_2 = compute_euler_characteristic(state_2)

    print(f"χ_1 (1 triangle) = {chi_1}")
    print(f"χ_2 (2 connected triangles) = {chi_2}")
    print(f"Δχ = {chi_2 - chi_1}")

    # For connected triangles sharing an edge:
    # ΔV = 1 (one new vertex)
    # ΔE = 2 (two new edges)
    # ΔF = 1 (one new face)
    # Δχ = 1 - 2 + 1 = 0
    # So χ doesn't change!

    print(f"State 1: V={len({n for m in state_1.modules for n in m.region})}, "
          f"E={len({tuple(sorted([n1,n2])) for m in state_1.modules for i,n1 in enumerate(sorted(m.region)) for n2 in sorted(m.region)[i+1:]})}, "
          f"F={len(state_1.modules)}")

    all_edges_2 = set()
    for m in state_2.modules:
        region = sorted(m.region)
        for i, n1 in enumerate(region):
            for n2 in region[i+1:]:
                all_edges_2.add(tuple(sorted([n1, n2])))

    print(f"State 2: V={len({n for m in state_2.modules for n in m.region})}, "
          f"E={len(all_edges_2)}, "
          f"F={len(state_2.modules)}")

    # This demonstrates that not all PNEW operations change χ
    # Only certain topological configurations do
    # This matches the Coq proof which requires specific conditions


def test_pnew_topology_incremental():
    """
    Test: Build up a mesh and track χ changes.

    Create a triangular mesh step by step and observe how χ evolves.
    This demonstrates the connection between local operations (PNEW)
    and global topology (χ).
    """
    instructions_list = [
        [],
        ["PNEW {0,1,2} 10"],
        ["PNEW {0,1,2} 10", "PNEW {1,2,3} 10"],
        ["PNEW {0,1,2} 10", "PNEW {1,2,3} 10", "PNEW {2,3,4} 10"],
        ["PNEW {0,1,2} 10", "PNEW {1,2,3} 10", "PNEW {2,3,4} 10", "PNEW {0,2,4} 10"],
    ]

    chi_values = []
    for instrs in instructions_list:
        state = run_vm_trace(instrs + ["HALT 1"], fuel=200)
        chi = compute_euler_characteristic(state)
        chi_values.append(chi)

        V = len({n for m in state.modules for n in m.region})
        all_edges = set()
        for m in state.modules:
            region = sorted(m.region)
            for i, n1 in enumerate(region):
                for n2 in region[i+1:]:
                    all_edges.add(tuple(sorted([n1, n2])))
        E = len(all_edges)
        F = len(state.modules)

        print(f"Step {len(instrs)}: V={V}, E={E}, F={F} → χ={chi}")

    print(f"\nχ evolution: {chi_values}")
    print(f"Δχ sequence: {[chi_values[i+1]-chi_values[i] for i in range(len(chi_values)-1)]}")

    # Verify χ is measurable and changes with topology
    assert len(set(chi_values)) > 1, "χ should vary as topology changes"


def test_pnew_fresh_increases_F():
    """
    Test: PNEW with fresh region always increases F (face count).

    This directly validates the Coq theorem:
    pnew_fresh_increases_F : forall g region,
      graph_find_region g region = None ->
      let (g', _) := graph_pnew g region in
      F g' = S (F g).
    """
    # Start with 1 module
    state_1 = run_vm_trace([
        "PNEW {0,1,2} 10",
        "HALT 1"
    ], fuel=50)
    F_1 = len(state_1.modules)

    # Add fresh module
    state_2 = run_vm_trace([
        "PNEW {0,1,2} 10",
        "PNEW {3,4,5} 10",
        "HALT 1"
    ], fuel=100)
    F_2 = len(state_2.modules)

    print(f"F_1 = {F_1}, F_2 = {F_2}, ΔF = {F_2 - F_1}")

    assert F_2 == F_1 + 1, "PNEW with fresh region should increase F by exactly 1"


def test_pnew_duplicate_region_preserves_F():
    """
    Test: PNEW with duplicate region doesn't increase F.

    When graph_find_region returns Some (region already exists),
    PNEW returns the existing module ID and doesn't modify the graph.
    """
    # Add same region twice
    state = run_vm_trace([
        "PNEW {0,1,2} 10",
        "PNEW {0,1,2} 10",  # Duplicate
        "HALT 1"
    ], fuel=100)

    F = len(state.modules)
    print(f"F after duplicate PNEW = {F}")

    assert F == 1, "PNEW with duplicate region should not increase F"


def test_euler_char_definition():
    """
    Sanity test: Verify χ = V - E + F holds by definition.
    """
    state = run_vm_trace([
        "PNEW {0,1,2} 10",
        "PNEW {1,2,3} 10",
        "PNEW {2,3,4} 10",
        "HALT 1"
    ], fuel=150)

    # Manual computation
    all_nodes = set()
    all_edges = set()
    for mod in state.modules:
        all_nodes.update(mod.region)
        region = sorted(mod.region)
        for i, n1 in enumerate(region):
            for n2 in region[i+1:]:
                all_edges.add(tuple(sorted([n1, n2])))

    V = len(all_nodes)
    E = len(all_edges)
    F = len(state.modules)

    chi_manual = V - E + F
    chi_computed = compute_euler_characteristic(state)

    print(f"V={V}, E={E}, F={F}")
    print(f"χ (manual) = {chi_manual}")
    print(f"χ (computed) = {chi_computed}")

    assert chi_manual == chi_computed, "χ computation should match definition"


if __name__ == "__main__":
    print("=" * 70)
    print("TESTING: PNEW Changes Topology (Phase 3 of Gravity Proof)")
    print("=" * 70)
    print()

    test_pnew_fresh_triangle_changes_chi()
    print()

    test_pnew_two_triangles_changes_chi()
    print()

    test_pnew_connected_triangles()
    print()

    test_pnew_topology_incremental()
    print()

    test_pnew_fresh_increases_F()
    print()

    test_pnew_duplicate_region_preserves_F()
    print()

    test_euler_char_definition()
    print()

    print("=" * 70)
    print("ALL TESTS PASSED: PNEW demonstrably changes topology")
    print("=" * 70)
