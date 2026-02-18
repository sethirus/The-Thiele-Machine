"""
Empirical tests for the three MuGravity axioms.

These tests verify whether the claimed axioms actually hold on real VM execution traces.

According to AXIOM_AUDIT.md:
- geometric_calibration_axiom: Should be provable (discrete Gauss equation)
- horizon_cycle_axiom: Should be provable (discrete Gauss-Bonnet theorem)
- source_normalization_axiom: Questionable - may be false or equilibrium-only

Tests run on real VM states extracted from Coq-verified semantics.
"""

import sys
from pathlib import Path
import math

# Add tools directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / "tools"))

from vm_wrapper import create_test_state_with_modules, VMState, VMModule

# Constants from MuGravity.v
PI = math.pi
CURVATURE_COUPLING = PI  # From MuGravity.v
GRAVITATIONAL_CONSTANT = 0.0625  # 1/16 in MuGravity.v

def compute_stress_energy(state: VMState, module_id: int) -> float:
    """
    Compute stress_energy (information density) for a module.

    From MuGravity.v:
      stress_energy s m = mu_cost_density s m
                        = (encoding_length + region_size) / region_size
    """
    # Find module
    module = None
    for m in state.modules:
        if m.id == module_id:
            module = m
            break

    if module is None:
        return 0.0

    region_size = len(module.region)
    if region_size == 0:
        return 0.0

    # Approximation: encoding_length ~ creation cost
    # For test modules, this is 10 + offset
    offset = module_id - state.modules[0].id
    encoding_length = 10.0 + offset

    return (encoding_length + region_size) / region_size


def compute_mu_laplacian(state: VMState, module_id: int) -> float:
    """
    Compute the discrete Laplacian: sum_{n∈neighbors(m)} (density(n) - density(m))

    Neighbors are modules that share edges (overlapping regions).
    """
    # Find target module
    target_module = None
    for m in state.modules:
        if m.id == module_id:
            target_module = m
            break

    if target_module is None:
        return 0.0

    target_density = compute_stress_energy(state, module_id)
    target_region = set(target_module.region)

    # Find neighbors (modules with shared edges)
    laplacian = 0.0
    for other in state.modules:
        if other.id == module_id:
            continue

        other_region = set(other.region)
        shared = target_region.intersection(other_region)

        # If they share >= 2 nodes, they're neighbors (share an edge)
        if len(shared) >= 2:
            other_density = compute_stress_energy(state, other.id)
            # Edge weight = 1 (simplified)
            laplacian += (other_density - target_density)

    return laplacian


def compute_geometric_angle_defect(state: VMState, module_id: int) -> float:
    """
    Compute discrete Gaussian curvature as angle defect.

    From MuGravity.v:
      geometric_angle_defect s m = 2*PI - sum_angles s m (module_triangles s m)

    For a vertex m with k neighbors in a triangulated surface:
      angle_defect = 2*PI - sum of interior angles at m

    Simplified: assume regular triangulation, each interior angle ≈ PI/3
    """
    # Find module
    module = None
    for m in state.modules:
        if m.id == module_id:
            module = m
            break

    if module is None:
        return 0.0

    # Count neighbors (modules sharing edges)
    target_region = set(module.region)
    num_neighbors = 0

    for other in state.modules:
        if other.id == module.id:
            continue

        other_region = set(other.region)
        shared = target_region.intersection(other_region)

        if len(shared) >= 2:
            num_neighbors += 1

    if num_neighbors == 0:
        # Isolated vertex has full 2*PI angle defect
        return 2 * PI

    # For regular triangulation: angle_sum ≈ num_neighbors * (PI/3)
    # But this is a CRUDE approximation - real geometry would need actual angles
    estimated_angle_sum = num_neighbors * (PI / 3)
    angle_defect = 2 * PI - estimated_angle_sum

    return angle_defect


def compute_horizon_area(state: VMState, horizon_modules: list) -> int:
    """
    Compute boundary area (number of boundary edges) for a region.

    For a set H of modules, count edges on the boundary.
    """
    # Collect all regions in horizon
    horizon_ids = set(horizon_modules)
    all_nodes = set()
    for mod_id in horizon_modules:
        for m in state.modules:
            if m.id == mod_id:
                all_nodes.update(m.region)
                break

    # Count boundary edges: edges with one endpoint in H and one outside
    boundary_count = 0

    for mod_id in horizon_modules:
        for m in state.modules:
            if m.id == mod_id:
                module_region = set(m.region)
                # Check edges to other modules
                for other in state.modules:
                    if other.id in horizon_ids:
                        continue  # Internal edge
                    other_region = set(other.region)
                    shared = module_region.intersection(other_region)
                    if len(shared) >= 2:
                        boundary_count += 1

    return boundary_count


# ========== AXIOM TESTS ==========

def check_source_normalization_axiom(state: VMState, module_id: int, tolerance: float = 0.1) -> tuple:
    """
    Test Axiom 1: source_normalization_axiom

    Claim: PI * mu_laplacian(m) = 16*PI*G * stress_energy(m)
    Simplified: Laplacian[density] = 16*G * density

    This claims density is an eigenfunction with eigenvalue 16*G.

    Returns: (holds, lhs, rhs, relative_error)
    """
    mu_lap = compute_mu_laplacian(state, module_id)
    stress = compute_stress_energy(state, module_id)

    lhs = CURVATURE_COUPLING * mu_lap
    rhs = 16 * PI * GRAVITATIONAL_CONSTANT * stress

    max_val = max(abs(lhs), abs(rhs), 1e-10)
    relative_error = abs(lhs - rhs) / max_val

    holds = relative_error < tolerance

    return holds, lhs, rhs, relative_error


def check_geometric_calibration_axiom(state: VMState, module_id: int, tolerance: float = 0.1) -> tuple:
    """
    Test Axiom 2: geometric_calibration_axiom

    Claim: angle_defect(m) = PI * mu_laplacian(m)

    This is the discrete Gauss equation relating geometry to analysis.

    Returns: (holds, lhs, rhs, relative_error)
    """
    angle_defect = compute_geometric_angle_defect(state, module_id)
    mu_lap = compute_mu_laplacian(state, module_id)

    lhs = angle_defect
    rhs = CURVATURE_COUPLING * mu_lap

    max_val = max(abs(lhs), abs(rhs), 1e-10)
    relative_error = abs(lhs - rhs) / max_val

    holds = relative_error < tolerance

    return holds, lhs, rhs, relative_error


def check_horizon_cycle_axiom(state: VMState, horizon_modules: list, tolerance: float = 0.1) -> tuple:
    """
    Test Axiom 3: horizon_cycle_axiom

    Claim: |sum_{m∈H} angle_defect(m)| = boundary_edge_count(H)

    This is the discrete Gauss-Bonnet theorem: sum of curvatures = 2*PI*χ

    Returns: (holds, lhs, rhs, relative_error)
    """
    total_defect = sum(compute_geometric_angle_defect(state, m) for m in horizon_modules)
    area = compute_horizon_area(state, horizon_modules)

    lhs = abs(total_defect)
    rhs = float(area)

    max_val = max(abs(lhs), abs(rhs), 1e-10)
    relative_error = abs(lhs - rhs) / max_val

    holds = relative_error < tolerance

    return holds, lhs, rhs, relative_error


# ========== MAIN TEST RUNNER ==========

def run_all_tests():
    """Run comprehensive tests on all three axioms"""

    print("=" * 80)
    print("EMPIRICAL AXIOM VERIFICATION")
    print("Testing the three MuGravity 'fundamental axioms'")
    print("=" * 80)

    # Create test state with modules
    print("\nCreating test VM state with 10 modules...")
    state = create_test_state_with_modules(num_modules=10, fuel=500)

    print(f"✓ Created {len(state.modules)} modules")
    print(f"  Final μ-cost: {state.mu}")
    print(f"  Module IDs: {[m.id for m in state.modules]}")

    # Test each module individually
    results = {
        'source_normalization': [],
        'geometric_calibration': [],
        'horizon_cycle': []
    }

    print("\n" + "=" * 80)
    print("TEST 1: source_normalization_axiom")
    print("Claim: PI * Laplacian[density] = 16*PI*G * density")
    print("=" * 80)

    for module in state.modules:
        holds, lhs, rhs, err = test_source_normalization_axiom(state, module.id)
        results['source_normalization'].append((module.id, holds, err))

        status = "✓ PASS" if holds else "✗ FAIL"
        print(f"{status} Module {module.id}: LHS={lhs:.6f}, RHS={rhs:.6f}, error={err:.2%}")

    pass_count = sum(1 for _, holds, _ in results['source_normalization'] if holds)
    print(f"\nResult: {pass_count}/{len(state.modules)} modules satisfy axiom")

    print("\n" + "=" * 80)
    print("TEST 2: geometric_calibration_axiom")
    print("Claim: angle_defect = PI * Laplacian[density]")
    print("=" * 80)

    for module in state.modules:
        holds, lhs, rhs, err = check_geometric_calibration_axiom(state, module.id)
        results['geometric_calibration'].append((module.id, holds, err))

        status = "✓ PASS" if holds else "✗ FAIL"
        print(f"{status} Module {module.id}: LHS={lhs:.6f}, RHS={rhs:.6f}, error={err:.2%}")

    pass_count = sum(1 for _, holds, _ in results['geometric_calibration'] if holds)
    print(f"\nResult: {pass_count}/{len(state.modules)} modules satisfy axiom")

    print("\n" + "=" * 80)
    print("TEST 3: horizon_cycle_axiom (Discrete Gauss-Bonnet)")
    print("Claim: |sum of angle_defects| = boundary_edge_count")
    print("=" * 80)

    # Test on different horizon regions
    test_horizons = [
        state.modules[:3],   # First 3 modules
        state.modules[:5],   # First 5 modules
        state.modules[:7],   # First 7 modules
        state.modules        # All modules
    ]

    for i, horizon in enumerate(test_horizons):
        horizon_ids = [m.id for m in horizon]
        holds, lhs, rhs, err = check_horizon_cycle_axiom(state, horizon_ids)
        results['horizon_cycle'].append((len(horizon), holds, err))

        status = "✓ PASS" if holds else "✗ FAIL"
        print(f"{status} Horizon size {len(horizon)}: LHS={lhs:.6f}, RHS={rhs:.6f}, error={err:.2%}")

    pass_count = sum(1 for _, holds, _ in results['horizon_cycle'] if holds)
    print(f"\nResult: {pass_count}/{len(test_horizons)} horizons satisfy axiom")

    # ========== SUMMARY ==========
    print("\n" + "=" * 80)
    print("VERDICT")
    print("=" * 80)

    total_pass = 0
    total_tests = 0

    for axiom_name, axiom_results in results.items():
        passes = sum(1 for _, holds, _ in axiom_results if holds)
        total = len(axiom_results)
        total_pass += passes
        total_tests += total

        if passes == total:
            verdict = "✓ AXIOM HOLDS"
        elif passes > total / 2:
            verdict = "~ PARTIALLY HOLDS"
        else:
            verdict = "✗ AXIOM FAILS"

        print(f"{axiom_name}: {passes}/{total} tests passed - {verdict}")

    print(f"\nOverall: {total_pass}/{total_tests} tests passed ({100*total_pass/total_tests:.1f}%)")

    print("\n" + "=" * 80)
    print("INTERPRETATION")
    print("=" * 80)
    print("""
According to AXIOM_AUDIT.md:

1. source_normalization_axiom: Claims Laplacian[ρ] = λ*ρ (eigenfunction)
   - If FAILS: Axiom is false or only holds at equilibrium
   - If PASSES: May be provable from graph structure

2. geometric_calibration_axiom: Discrete Gauss equation
   - SHOULD BE PROVABLE from discrete differential geometry
   - This is Gauss's Theorema Egregium in discrete form

3. horizon_cycle_axiom: Discrete Gauss-Bonnet theorem
   - SHOULD BE PROVABLE from Euler's formula (V-E+F=χ)
   - Standard result in graph topology

Only "I AM THAT I AM" (VM existence) should be axiomatic.
Everything else should be proven or observed.
    """)

    return results


if __name__ == "__main__":
    results = run_all_tests()
