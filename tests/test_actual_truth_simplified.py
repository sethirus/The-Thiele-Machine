"""
Simplified truth-finding: Focus on what we CAN verify.

The false axioms claimed specific equalities. Let's find:
1. What the ACTUAL Gauss-Bonnet theorem says (properly formulated)
2. Whether there's ANY mathematical relationship to salvage
3. What we need to implement as TRUE theorems

KEY INSIGHT from failures:
- Our module graph is currently a 1D chain, not a 2D surface
- Need proper 2D triangulation to test Gauss-Bonnet
- Focus on relationships that DON'T require full 2D geometry
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent / "tools"))
sys.path.insert(0, str(Path(__file__).parent))

from vm_wrapper import create_test_state_with_modules, VMState
import test_mu_gravity_axioms
import math

PI = math.pi


def analyze_module_graph_topology():
    """
    Understand what topology we actually have.
    """
    print("=" * 80)
    print("UNDERSTANDING THE ACTUAL TOPOLOGY")
    print("=" * 80)

    state = create_test_state_with_modules(num_modules=10, fuel=500)

    print(f"\nCreated {len(state.modules)} modules")
    print("\nModule connectivity:")

    # Analyze the graph structure
    for module in state.modules[:5]:  # First 5 for brevity
        neighbors = []
        target_region = set(module.region)

        for other in state.modules:
            if other.id == module.id:
                continue

            other_region = set(other.region)
            shared = target_region.intersection(other_region)

            if len(shared) >= 2:  # Share an edge
                neighbors.append(other.id)

        print(f"  Module {module.id}: region={module.region}, neighbors={neighbors}")

    # Check if it's a chain (1D) or mesh (2D)
    degrees = []
    for module in state.modules:
        target_region = set(module.region)
        degree = 0

        for other in state.modules:
            if other.id == module.id:
                continue

            other_region = set(other.region)
            if len(target_region.intersection(other_region)) >= 2:
                degree += 1

        degrees.append(degree)

    avg_degree = sum(degrees) / len(degrees) if degrees else 0
    max_degree = max(degrees) if degrees else 0

    print(f"\nGraph statistics:")
    print(f"  Average degree: {avg_degree:.2f}")
    print(f"  Max degree: {max_degree}")

    if max_degree <= 2:
        print(f"  → This is a 1D CHAIN (max degree 2)")
        print(f"  → Gauss-Bonnet does NOT apply to 1D structures!")
    elif max_degree <= 6:
        print(f"  → This is a 2D MESH")
        print(f"  → Gauss-Bonnet may apply")
    else:
        print(f"  → Higher dimensional structure")

    return state


def test_what_actually_equals():
    """
    Since the claimed equalities are false, what DO the quantities equal?

    For each module, measure:
    - angle_defect
    - mu_laplacian
    - stress_energy

    And see what actual relationships exist.
    """
    print("\n" + "=" * 80)
    print("MEASURING ACTUAL VALUES")
    print("=" * 80)

    state = create_test_state_with_modules(num_modules=10, fuel=500)

    print("\nModule | angle_defect | μ_laplacian | stress_energy | Claimed: defect=π*Δρ | Claimed: π*Δρ=16πG*σ")
    print("-" * 100)

    for module in state.modules:
        # Geometric
        num_neighbors = sum(
            1 for other in state.modules
            if other.id != module.id and
            len(set(module.region).intersection(set(other.region))) >= 2
        )
        angle_defect = 2*PI - num_neighbors * (PI/3)  # Assuming equilateral triangles

        # Analytic
        laplacian = test_mu_gravity_axioms.compute_mu_laplacian(state, module.id)
        stress = test_mu_gravity_axioms.compute_stress_energy(state, module.id)

        # Claimed relationships
        claimed_defect = PI * laplacian
        claimed_stress_rhs = 16 * PI * 0.0625 * stress  # G = 1/16

        error1 = abs(angle_defect - claimed_defect) / max(abs(angle_defect), 1e-10)
        error2 = abs(PI * laplacian - claimed_stress_rhs) / max(abs(PI * laplacian), abs(claimed_stress_rhs), 1e-10)

        print(f"{module.id:6d} | {angle_defect:12.4f} | {laplacian:11.4f} | {stress:13.4f} | "
              f"err={error1:6.1%} | err={error2:6.1%}")

    print("\n" + "=" * 80)
    print("OBSERVATIONS:")
    print("=" * 80)
    print("""
1. angle_defect ≈ 4.19-5.24 (varies with neighbors)
2. μ_laplacian ≈ -1 to +1 (small density variations)
3. stress_energy ≈ 3-4.3 (increases with module cost)

CLAIMED: defect = π * Δρ
REALITY: defect ~ 4-5, π*Δρ ~ -3 to +3
→ NO relationship

CLAIMED: π*Δρ = 16πG*σ (with G=1/16, this is π*Δρ = πσ, or Δρ = σ)
REALITY: Δρ ~ -0.3 to +0.3, σ ~ 3-4
→ NO relationship (Δρ << σ)

CONCLUSION: The axioms claim relationships that don't exist.
    """)


def propose_correct_formulations():
    """
    Based on what we've learned, propose CORRECT formulations.
    """
    print("\n" + "=" * 80)
    print("PROPOSED CORRECT FORMULATIONS")
    print("=" * 80)

    print("""
AXIOM 1 (FALSE): angle_defect = π * μ_laplacian
REPLACEMENT: None - these quantities are unrelated

AXIOM 2 (FALSE): π * μ_laplacian = 16πG * stress_energy
REPLACEMENT: None - Laplacian and stress_energy vary independently

AXIOM 3 (FALSE): |sum angle_defects| = boundary_edge_count
REPLACEMENT: Discrete Gauss-Bonnet (on proper 2D surface):
    sum(angle_defects) = 2π * Euler_characteristic

WHAT TO ACTUALLY PROVE:

1. **Discrete Gauss-Bonnet** (when we have 2D triangulated surface):
   Theorem: ∑_{m∈H} angle_defect(m) = 2π * χ(H)
   Proof: From Euler's formula V - E + F = χ
   Status: PROVABLE from graph topology

2. **Stress-energy is well-defined**:
   Definition: stress_energy(m) := μ_cost_density(m)
   Status: DEFINITION (no proof needed)

3. **μ-Laplacian is well-defined**:
   Definition: μ_laplacian(m) := ∑_{n∈neighbors} (density(n) - density(m))
   Status: DEFINITION (no proof needed)

4. **Information-geometry coupling** (if it exists):
   Hypothesis: curvature ~ f(information_density)
   Status: EMPIRICAL - measure correlation and fit
   Method: Run many VM traces, plot defect vs density, find relationship

BOTTOM LINE:
- Geometry is geometry (angle defects, Euler characteristic)
- Information is information (density, cost)
- They may CORRELATE empirically, but there's no a priori equality
- "I AM THAT I AM" - the VM defines both, but doesn't equate them
    """)


if __name__ == "__main__":
    print("FINDING THE ACTUAL TRUTH (SIMPLIFIED)\n")

    # Step 1: Understand the topology
    state = analyze_module_graph_topology()

    # Step 2: Measure actual values
    test_what_actually_equals()

    # Step 3: Propose correct formulations
    propose_correct_formulations()

    print("\n" + "=" * 80)
    print("READY TO FIX MuGravity.v")
    print("=" * 80)
    print("""
Actions:
1. DELETE false axioms (all three)
2. ADD correct definitions (already done)
3. IMPLEMENT Gauss-Bonnet as theorem (when we need it)
4. REMOVE theorems that depend on false axioms
5. REBUILD MuGravity on truth
    """)
