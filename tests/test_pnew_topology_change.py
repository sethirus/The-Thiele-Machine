"""
Test that PNEW operations change Euler characteristic χ = V - E + F.

This empirically validates Phase 3 of the gravity proof:
- PNEW with fresh region → changes V, E, F
- Changes in V, E, F → changes in χ
- Changes in χ → changes in curvature (via Gauss-Bonnet)

REF: coq/kernel/PNEWTopologyChange.v
     GRAVITY_PROOF_PLAN.md Phase 3
"""

from build.thiele_vm import run_vm, VMState


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


def compute_topology_counts(state: VMState) -> tuple[int, int, int]:
    """Return (V, E, F) for the current module graph."""
    faces = len(state.modules)

    vertices = set()
    edges = set()
    for mod in state.modules:
        region = sorted(mod.region)
        vertices.update(region)
        for i, n1 in enumerate(region):
            for n2 in region[i + 1:]:
                edges.add((n1, n2))

    return len(vertices), len(edges), faces


def test_pnew_fresh_triangle_changes_chi():
    """
    Test: PNEW with fresh triangle changes Euler characteristic.

    Strategy:
    1. Start with empty graph (χ = 0)
    2. Add fresh triangle {0,1,2}
    3. Verify χ changed
    """
    # Empty initial state
    initial = run_vm(["HALT 1"], fuel=10)
    chi_0 = compute_euler_characteristic(initial)

    # Add fresh triangle
    final = run_vm([
        "PNEW {0,1,2} 10",
        "HALT 1"
    ], fuel=50)
    chi_1 = compute_euler_characteristic(final)

    # Verify topology changed
    assert chi_1 != chi_0, "PNEW with fresh triangle should change χ"
    assert len(final.modules) == 1, "Should have exactly 1 module"
    assert compute_topology_counts(final) == (3, 3, 1)


def test_pnew_two_triangles_changes_chi():
    """
    Test: Adding second fresh triangle changes χ again.

    Triangles {0,1,2} and {3,4,5} are disjoint.
    Expected:
    - Triangle 1: V=3, E=3, F=1 → χ = 3-3+1 = 1
    - Triangle 2: V=6, E=6, F=2 → χ = 6-6+2 = 2
    """
    # Initial: empty
    chi_0 = compute_euler_characteristic(run_vm(["HALT 1"], fuel=10))

    # Add first triangle
    state_1 = run_vm([
        "PNEW {0,1,2} 10",
        "HALT 1"
    ], fuel=50)
    chi_1 = compute_euler_characteristic(state_1)

    # Add second disjoint triangle
    state_2 = run_vm([
        "PNEW {0,1,2} 10",
        "PNEW {3,4,5} 10",
        "HALT 1"
    ], fuel=100)
    chi_2 = compute_euler_characteristic(state_2)

    # Verify each PNEW changed χ
    assert chi_1 != chi_0, "First PNEW should change χ"
    assert chi_2 != chi_1, "Second PNEW should change χ"
    assert chi_2 > chi_1, "Adding disconnected components increases χ"
    assert compute_topology_counts(state_1) == (3, 3, 1)
    assert compute_topology_counts(state_2) == (6, 6, 2)


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
    state_1 = run_vm([
        "PNEW {0,1,2} 10",
        "HALT 1"
    ], fuel=50)
    chi_1 = compute_euler_characteristic(state_1)

    state_2 = run_vm([
        "PNEW {0,1,2} 10",
        "PNEW {1,2,3} 10",
        "HALT 1"
    ], fuel=100)
    chi_2 = compute_euler_characteristic(state_2)

    # For connected triangles sharing an edge:
    # ΔV = 1 (one new vertex)
    # ΔE = 2 (two new edges)
    # ΔF = 1 (one new face)
    # Δχ = 1 - 2 + 1 = 0
    # So χ doesn't change!

    assert chi_1 == 1
    assert chi_2 == 1
    assert compute_topology_counts(state_1) == (3, 3, 1)
    assert compute_topology_counts(state_2) == (4, 5, 2)


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
    topology_counts = []
    for instrs in instructions_list:
        state = run_vm(instrs + ["HALT 1"], fuel=200)
        chi = compute_euler_characteristic(state)
        chi_values.append(chi)
        topology_counts.append(compute_topology_counts(state))

    # Verify χ is measurable and changes with topology
    assert chi_values[0] == 0, "Empty graph should have χ = 0"
    assert chi_values[1] == 1, "Single fresh triangle should have χ = 1"
    assert [count[2] for count in topology_counts] == [0, 1, 2, 3, 4]
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
    state_1 = run_vm([
        "PNEW {0,1,2} 10",
        "HALT 1"
    ], fuel=50)
    F_1 = len(state_1.modules)

    # Add fresh module
    state_2 = run_vm([
        "PNEW {0,1,2} 10",
        "PNEW {3,4,5} 10",
        "HALT 1"
    ], fuel=100)
    F_2 = len(state_2.modules)

    assert F_2 == F_1 + 1, "PNEW with fresh region should increase F by exactly 1"


def test_pnew_duplicate_region_preserves_F():
    """
    Test: PNEW with duplicate region doesn't increase F.

    When graph_find_region returns Some (region already exists),
    PNEW returns the existing module ID and doesn't modify the graph.
    """
    # Add same region twice
    state = run_vm([
        "PNEW {0,1,2} 10",
        "PNEW {0,1,2} 10",  # Duplicate
        "HALT 1"
    ], fuel=100)

    F = len(state.modules)
    assert F == 1, "PNEW with duplicate region should not increase F"


def test_euler_char_definition():
    """
    Sanity test: Verify χ = V - E + F holds by definition.
    """
    state = run_vm([
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

    assert chi_manual == chi_computed, "χ computation should match definition"
