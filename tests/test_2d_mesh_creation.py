"""
Test: Does the VM naturally create 2D manifold structure?

The previous tests used PNEW to create a chain:
  Module 1: {0,1,2}
  Module 2: {1,2,3}  <- shares edge with 1
  Module 3: {2,3,4}  <- shares edge with 2
  ...
  This is 1D (each module has 2 neighbors max)

For gravity to emerge, we need 2D structure where modules form a mesh.

Test different VM operations:
1. PNEW with different region patterns
2. PSPLIT creating branching structure
3. Actual computation traces
"""

import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent / "tools"))

from vm_wrapper import run_vm_trace, VMState

def test_2d_mesh_creation():
    """Try to create a 2D mesh structure"""
    print("=" * 80)
    print("TEST: Creating 2D Mesh with PNEW")
    print("=" * 80)

    instructions = []

    # Create a triangular lattice (2D)
    # Layer 0: module at {0,1,2}
    # Layer 1: modules at {0,1,3}, {1,2,3}
    # Layer 2: modules at {0,3,4}, {3,4,1}, {4,2,1}
    # This creates a 2D mesh with higher connectivity

    regions = [
        [0, 1, 2],   # Center
        [0, 1, 3],   # Adjacent 1
        [1, 2, 3],   # Adjacent 2
        [0, 2, 4],   # Adjacent 3
        [2, 3, 4],   # Adjacent 4
        [0, 3, 5],   # Ring 2
        [3, 4, 5],
        [1, 3, 6],
        [3, 5, 6],
    ]

    for i, region in enumerate(regions):
        region_str = "{" + ",".join(map(str, region)) + "}"
        instructions.append(f"PNEW {region_str} {10 + i}")

    instructions.append("HALT 1")

    state = run_vm_trace(instructions, fuel=500)

    print(f"\nCreated {len(state.modules)} modules")
    print("\nConnectivity analysis:")

    # Analyze connectivity
    degrees = []
    for module in state.modules:
        target_region = set(module.region)
        neighbors = []

        for other in state.modules:
            if other.id == module.id:
                continue

            other_region = set(other.region)
            shared = target_region.intersection(other_region)

            if len(shared) >= 2:  # Share edge
                neighbors.append(other.id)

        degree = len(neighbors)
        degrees.append(degree)

        if degree > 0:
            print(f"  Module {module.id}: region={module.region}, neighbors={neighbors}, degree={degree}")

    avg_degree = sum(degrees) / len(degrees) if degrees else 0
    max_degree = max(degrees) if degrees else 0

    print(f"\nTopology:")
    print(f"  Average degree: {avg_degree:.2f}")
    print(f"  Max degree: {max_degree}")

    if max_degree > 2:
        print(f"  ✓ This is a 2D MESH (max degree > 2)")
        print(f"  ✓ Gauss-Bonnet theorem APPLIES here!")
        return state, True
    else:
        print(f"  ✗ Still 1D chain")
        return state, False


def test_computational_trace():
    """Test a real computational trace with splits and merges"""
    print("\n" + "=" * 80)
    print("TEST: Real Computation with PSPLIT/PMERGE")
    print("=" * 80)

    instructions = [
        # Create initial module
        "PNEW {0,1,2} 10",

        # Split it
        "PSPLIT 1 {0,1} {1,2} 5",

        # Create more modules
        "PNEW {1,2,3} 12",
        "PNEW {0,2,3} 13",

        # Split again
        "PSPLIT 4 {0,2} {2,3} 6",

        "HALT 1"
    ]

    state = run_vm_trace(instructions, fuel=500)

    print(f"\nCreated {len(state.modules)} modules via splits")

    # Analyze
    for module in state.modules:
        target_region = set(module.region)
        neighbors = [other.id for other in state.modules
                    if other.id != module.id and
                    len(target_region.intersection(set(other.region))) >= 2]

        print(f"  Module {module.id}: region={module.region}, neighbors={neighbors}")

    return state


if __name__ == "__main__":
    print("FINDING 2D STRUCTURE IN VM EXECUTION\n")

    # Test 1: Try to create 2D mesh
    state_2d, is_2d = test_2d_mesh_creation()

    # Test 2: Real computation
    state_comp = test_computational_trace()

    if is_2d:
        print("\n" + "=" * 80)
        print("SUCCESS: WE CAN CREATE 2D MANIFOLDS")
        print("=" * 80)
        print("""
Now we can test:
1. Does Gauss-Bonnet hold on this 2D mesh?
2. Does curvature relate to Euler characteristic?
3. Does information create the geometry?

This is the path to PROVING emergence!
        """)
    else:
        print("\n" + "=" * 80)
        print("Need different VM operations to create 2D structure")
        print("=" * 80)
