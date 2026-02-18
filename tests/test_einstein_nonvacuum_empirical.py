"""Test Einstein equations for non-uniform mass distributions."""
import numpy as np

def test_einstein_nonuniform_mass():
    """
    Test whether G_μν = 8πG T_μν holds for non-uniform mass.
    
    For non-uniform mass, both tensors should be non-zero.
    The question: are they proportional?
    """
    print("\n=== EINSTEIN EQUATIONS: NON-UNIFORM MASS ===")
    print()
    
    # Create a simple non-uniform mass distribution
    # e.g., mass[i] = i (linear gradient)
    masses = [0, 1, 2, 3]
    
    print(f"Mass distribution: {masses}")
    print()
    
    # For our discrete metric with corrected definition:
    # metric[μ,ν](w,w) = edge_length(μ,ν) if μ=ν, else 0
    # edge_length(μ,ν) = mass[μ] + mass[ν]
    
    # So metric is DIAGONAL but varies by index
    print("Metric tensor (diagonal entries):")
    for mu in range(4):
        edge_mu = 2 * masses[mu]
        print(f"  g[{mu},{mu}] = {edge_mu}")
    print()
    
    # Christoffel symbols: Γ^ρ_{μν} = (1/2)(∂_μ g_{νρ} + ∂_ν g_{μρ} - ∂_ρ g_{μν})
    # With corrected metric, g[μ,ν](w,w) is independent of w
    # So all derivatives are ZERO
    # Therefore Christoffel = 0 even for non-uniform mass!
    
    print("Christoffel symbols:")
    print("  All Γ = 0 (metric independent of position)")
    print()
    
    # Riemann tensor: R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ} + ...
    # If all Christoffel = 0, then Riemann = 0
    print("Riemann tensor:")
    print("  All R = 0 (Christoffel = 0)")
    print()
    
    # Einstein tensor G_μν = R_μν - (1/2)g_μν R
    # If Riemann = 0, then Ricci = 0, so G = 0
    print("Einstein tensor:")
    print("  All G = 0 (Riemann = 0)")
    print()
    
    # Stress-energy tensor
    # T_00 = energy_density = mass[v]
    # T_0i = momentum_density = ∂_i (mass)
    # T_ij = stress
    print("Stress-energy tensor:")
    for v in range(4):
        print(f"  T_00({v}) = {masses[v]}")
    print()
    
    print("CONCLUSION:")
    print("  G_μν = 0 for all components")
    print("  T_00(v) = mass[v] (varies by vertex)")
    print("  Therefore: G_μν ≠ 8πG T_μν (unless mass=0 everywhere)")
    print()
    print("PROBLEM: Our metric definition makes spacetime ALWAYS flat!")
    print("  metric[μ,ν](w,w) independent of w → zero Christoffel")
    print("  zero Christoffel → zero curvature")
    print("  zero curvature → Einstein tensor = 0")
    print()
    print("But stress-energy can be non-zero, so equation fails.")
    print()
    print("ROOT CAUSE:")
    print("  The metric should depend on the mass at the POINT w,")
    print("  not just on the index labels μ,ν.")
    print()
    print("CORRECT DEFINITION:")
    print("  metric[μ,ν](w,w) should use mass[w] to determine edge lengths,")
    print("  not mass[μ] or mass[ν].")
    print("  Then metric varies with position, creating curvature.")

if __name__ == '__main__':
    test_einstein_nonuniform_mass()
