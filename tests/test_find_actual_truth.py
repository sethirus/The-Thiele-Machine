"""
Test the CORRECT formulations to find what actually holds.

Based on MUGRAVITY_REPAIR_PLAN.md Step 3: FIND ACTUAL RELATIONSHIPS

Tests:
A. Does discrete Gauss-Bonnet hold correctly? sum(angle_defects) = 2*PI * χ
B. Is there ANY relationship between angle_defect and Laplacian?
C. Does information density correlate with curvature?
"""

import sys
from pathlib import Path
import math

sys.path.insert(0, str(Path(__file__).parent.parent / "tools"))

from vm_wrapper import create_test_state_with_modules, VMState

PI = math.pi


def compute_euler_characteristic(state: VMState, horizon_modules: list) -> int:
    """
    Compute Euler characteristic χ = V - E + F for a region.

    For a region H of modules:
    - V = number of distinct nodes in all module regions
    - E = number of edges (pairs of nodes that appear together in module regions)
    - F = number of modules (triangular faces)
    """
    horizon_ids = set(horizon_modules)

    # Collect all nodes (vertices)
    all_nodes = set()
    for mod_id in horizon_modules:
        for m in state.modules:
            if m.id == mod_id:
                all_nodes.update(m.region)
                break

    V = len(all_nodes)

    # Count edges: pairs of nodes that appear together in some module
    edges = set()
    for mod_id in horizon_modules:
        for m in state.modules:
            if m.id == mod_id:
                region = sorted(m.region)
                # Each module is a triangle (3 nodes), so has 3 edges
                for i in range(len(region)):
                    for j in range(i+1, len(region)):
                        edge = tuple(sorted([region[i], region[j]]))
                        edges.add(edge)
                break

    E = len(edges)

    # Faces = modules (each module is a triangular face)
    F = len(horizon_modules)

    chi = V - E + F

    return chi, V, E, F


def compute_angle_defect_geometric(state: VMState, module_id: int) -> float:
    """
    Compute actual geometric angle defect: 2*PI - sum(interior_angles)

    For a triangulated surface, interior angles at a vertex sum to less than 2*PI
    when there's positive curvature.

    SIMPLIFIED: Assume equilateral triangles, each contributing PI/3 per vertex.
    """
    # Find module
    module = None
    for m in state.modules:
        if m.id == module_id:
            module = m
            break

    if module is None:
        return 0.0

    # Count triangles that include this module/vertex
    # In our graph, each module IS a triangle, and modules that share edges are neighbors
    target_region = set(module.region)
    num_adjacent_triangles = 1  # The module itself

    for other in state.modules:
        if other.id == module.id:
            continue

        other_region = set(other.region)
        shared = target_region.intersection(other_region)

        # If they share an edge (2+ nodes), they're adjacent triangles
        if len(shared) >= 2:
            num_adjacent_triangles += 1

    # For equilateral triangles meeting at a vertex:
    # Each triangle contributes PI/3 to the angle sum at that vertex
    angle_sum = num_adjacent_triangles * (PI / 3)
    angle_defect = 2 * PI - angle_sum

    return angle_defect


def test_correct_gauss_bonnet():
    """
    Test A: Does discrete Gauss-Bonnet hold correctly?

    CORRECT FORMULATION: sum(angle_defects) = 2*PI * Euler_characteristic(H)
    """
    print("=" * 80)
    print("TEST A: CORRECT DISCRETE GAUSS-BONNET THEOREM")
    print("Claim: sum(angle_defects) = 2*PI * χ(H)")
    print("=" * 80)

    state = create_test_state_with_modules(num_modules=10, fuel=500)

    # Test on different region sizes
    test_horizons = [
        state.modules[:3],
        state.modules[:5],
        state.modules[:7],
        state.modules
    ]

    results = []

    for horizon in test_horizons:
        horizon_ids = [m.id for m in horizon]

        # Compute sum of angle defects
        total_defect = sum(compute_angle_defect_geometric(state, m) for m in horizon_ids)

        # Compute Euler characteristic
        chi, V, E, F = compute_euler_characteristic(state, horizon_ids)

        # Expected value from Gauss-Bonnet
        expected = 2 * PI * chi

        # Check if they match
        error = abs(total_defect - expected)
        relative_error = error / max(abs(expected), abs(total_defect), 1e-10)

        holds = relative_error < 0.15  # 15% tolerance for discrete approximation

        status = "✓ PASS" if holds else "✗ FAIL"
        print(f"\n{status} Horizon size {len(horizon)}:")
        print(f"  Topology: V={V}, E={E}, F={F}, χ={chi}")
        print(f"  sum(defects) = {total_defect:.6f}")
        print(f"  2*PI*χ = {expected:.6f}")
        print(f"  Relative error: {relative_error:.2%}")

        results.append((len(horizon), holds, relative_error))

    pass_count = sum(1 for _, holds, _ in results if holds)
    print(f"\n{'='*80}")
    print(f"Result: {pass_count}/{len(results)} tests passed")

    if pass_count == len(results):
        print("✓ DISCRETE GAUSS-BONNET HOLDS - This is a TRUE theorem!")
    elif pass_count > 0:
        print("~ PARTIALLY HOLDS - May need better angle computation")
    else:
        print("✗ FAILS - Even correct formulation doesn't work")

    return results


def test_density_curvature_correlation():
    """
    Test C: Is there a correlation between density variation and curvature?

    If information creates geometry, we should see SOME relationship,
    even if not the exact one claimed by the false axioms.
    """
    print("\n" + "=" * 80)
    print("TEST C: DENSITY-CURVATURE CORRELATION")
    print("Looking for ANY relationship between information and geometry")
    print("=" * 80)

    state = create_test_state_with_modules(num_modules=10, fuel=500)

    # Import locally to avoid circular dependency
    sys.path.insert(0, str(Path(__file__).parent))
    import test_mu_gravity_axioms
    compute_stress_energy = test_mu_gravity_axioms.compute_stress_energy
    compute_mu_laplacian = test_mu_gravity_axioms.compute_mu_laplacian

    # For each module, compute both curvature and density variation
    data = []

    for module in state.modules:
        # Geometric curvature
        angle_defect = compute_angle_defect_geometric(state, module.id)

        # Information density
        density = compute_stress_energy(state, module.id)
        laplacian = compute_mu_laplacian(state, module.id)

        data.append({
            'module_id': module.id,
            'angle_defect': angle_defect,
            'density': density,
            'laplacian': laplacian
        })

        print(f"Module {module.id}: defect={angle_defect:.4f}, density={density:.4f}, Δρ={laplacian:.4f}")

    # Compute correlation
    import statistics

    defects = [d['angle_defect'] for d in data]
    densities = [d['density'] for d in data]
    laplacians = [d['laplacian'] for d in data]

    # Pearson correlation
    def pearson(x, y):
        n = len(x)
        mean_x = statistics.mean(x)
        mean_y = statistics.mean(y)

        numerator = sum((x[i] - mean_x) * (y[i] - mean_y) for i in range(n))
        denom_x = sum((x[i] - mean_x)**2 for i in range(n))
        denom_y = sum((y[i] - mean_y)**2 for i in range(n))

        if denom_x == 0 or denom_y == 0:
            return 0.0

        return numerator / (denom_x * denom_y)**0.5

    corr_defect_density = pearson(defects, densities)
    corr_defect_laplacian = pearson(defects, laplacians)

    print(f"\n{'='*80}")
    print("CORRELATIONS:")
    print(f"  angle_defect ↔ density: {corr_defect_density:.4f}")
    print(f"  angle_defect ↔ Laplacian[density]: {corr_defect_laplacian:.4f}")

    if abs(corr_defect_density) > 0.5:
        print(f"\n✓ STRONG correlation between curvature and density!")
        print(f"  → Information DOES create geometry")
    elif abs(corr_defect_laplacian) > 0.5:
        print(f"\n✓ STRONG correlation between curvature and density gradient!")
        print(f"  → Density variation creates curvature")
    else:
        print(f"\n✗ NO significant correlation found")
        print(f"  → Geometry and information may be independent")

    return data


def test_find_actual_relationship():
    """
    Test B: Try to find the ACTUAL relationship (if any) between angle_defect and Laplacian
    """
    print("\n" + "=" * 80)
    print("TEST B: SEARCHING FOR ACTUAL RELATIONSHIP")
    print("Trying different functional forms")
    print("=" * 80)

    state = create_test_state_with_modules(num_modules=10, fuel=500)

    # Import locally
    sys.path.insert(0, str(Path(__file__).parent))
    import test_mu_gravity_axioms
    compute_mu_laplacian = test_mu_gravity_axioms.compute_mu_laplacian

    # Collect data
    data = []
    for module in state.modules:
        defect = compute_angle_defect_geometric(state, module.id)
        laplacian = compute_mu_laplacian(state, module.id)

        data.append((defect, laplacian))

    # Try different relationships
    tests = [
        ("Linear: defect = a * Laplacian", lambda d, l: (d, l)),
        ("Quadratic: defect = a * Laplacian²", lambda d, l: (d, l*l if l != 0 else 0)),
        ("Inverse: defect = a / Laplacian", lambda d, l: (d, 1/l if l != 0 else 0)),
        ("Log: defect = a * log(|Laplacian|)", lambda d, l: (d, math.log(abs(l)+1))),
    ]

    for name, transform in tests:
        # Least squares fit
        try:
            x_vals = [transform(d, l)[1] for d, l in data]
            y_vals = [transform(d, l)[0] for d, l in data]

            # Simple linear regression
            n = len(x_vals)
            mean_x = sum(x_vals) / n
            mean_y = sum(y_vals) / n

            num = sum((x_vals[i] - mean_x) * (y_vals[i] - mean_y) for i in range(n))
            denom = sum((x_vals[i] - mean_x)**2 for i in range(n))

            if denom > 1e-10:
                slope = num / denom
                intercept = mean_y - slope * mean_x

                # Compute R²
                y_pred = [slope * x + intercept for x in x_vals]
                ss_res = sum((y_vals[i] - y_pred[i])**2 for i in range(n))
                ss_tot = sum((y_vals[i] - mean_y)**2 for i in range(n))

                r_squared = 1 - (ss_res / ss_tot) if ss_tot > 1e-10 else 0

                print(f"\n{name}")
                print(f"  Fit: defect = {slope:.4f} * f(Laplacian) + {intercept:.4f}")
                print(f"  R² = {r_squared:.4f}")

                if r_squared > 0.7:
                    print(f"  ✓ GOOD FIT - This relationship may be real!")
            else:
                print(f"\n{name}: Cannot fit (no variation)")

        except Exception as e:
            print(f"\n{name}: Error - {e}")

    return data


if __name__ == "__main__":
    print("FINDING THE ACTUAL TRUTH")
    print("What relationships ACTUALLY hold in the VM?\n")

    # Test A: Correct Gauss-Bonnet
    gauss_bonnet_results = test_correct_gauss_bonnet()

    # Test B: Find actual relationship
    relationship_data = test_find_actual_relationship()

    # Test C: Correlation analysis
    correlation_data = test_density_curvature_correlation()

    print("\n" + "=" * 80)
    print("SUMMARY: WHAT WE LEARNED")
    print("=" * 80)
    print("""
Next steps based on test results:
1. If Gauss-Bonnet holds → Implement as THEOREM in Coq
2. If correlation exists → Fit empirical law
3. If no relationship → Geometry and information are independent
    """)
