"""
DEBUG: Why is Gauss-Bonnet off by 2.5x?

Deep investigation into the discrete Gauss-Bonnet formula.
"""

import sys
from pathlib import Path
import math

sys.path.insert(0, str(Path(__file__).parent.parent / "tools"))
sys.path.insert(0, str(Path(__file__).parent))

from vm_wrapper import run_vm_trace
import test_2d_mesh_creation
import test_mu_gravity_axioms

PI = math.pi

def test_weighted_gauss_bonnet():
    """
    Test the WEIGHTED Gauss-Bonnet formula.
    
    For discrete surfaces, the correct formula includes vertex AREAS:
      sum_v K(v) * A(v) = 2π*χ
    
    where A(v) is the area associated with vertex v (its "dual cell").
    """
    print("=" * 80)
    print("WEIGHTED GAUSS-BONNET TEST")
    print("=" * 80)
    
    state, _ = test_2d_mesh_creation.test_2d_mesh_creation()
    
    all_vertices = set()
    for m in state.modules:
        all_vertices.update(m.region)
    
    V = len(all_vertices)
    F = len(state.modules)
    edges = set()
    for m in state.modules:
        region = sorted(m.region)
        for i in range(len(region)):
            for j in range(i+1, len(region)):
                edges.add(tuple(sorted([region[i], region[j]])))
    E = len(edges)
    chi = V - E + F
    
    print(f"\nTopology: V={V}, E={E}, F={F}, χ={chi}")
    
    # Compute curvature and area for each vertex
    print("\nVertex | #Tri | Area | Curvature | Weighted K")
    print("-" * 60)
    
    total_weighted_curvature = 0
    
    for vertex in sorted(all_vertices):
        # Count incident triangles
        incident = [m for m in state.modules if vertex in m.region]
        num_tri = len(incident)
        
        # Angle sum (assuming equilateral for now)
        angle_sum = num_tri * (PI / 3)
        
        # Curvature = 2π - angle_sum
        curvature = 2 * PI - angle_sum
        
        # Vertex area = (1/3) * sum of incident triangle areas
        # For unit triangles, each has area = sqrt(3)/4
        # But in discrete Gauss-Bonnet, often use A(v) = 1/V or other weighting
        
        # Try: A(v) = # of incident triangles / total triangles
        area_weight = num_tri / F
        
        weighted = curvature * area_weight
        total_weighted_curvature += weighted
        
        print(f"{vertex:6d} | {num_tri:4d} | {area_weight:.4f} | {curvature:9.6f} | {weighted:10.6f}")
    
    predicted = 2 * PI * chi
    
    print(f"\n{'='*80}")
    print(f"RESULTS (area-weighted):")
    print(f"{'='*80}")
    print(f"sum(K * A) = {total_weighted_curvature:.6f}")
    print(f"2π*χ = {predicted:.6f}")
    print(f"Ratio: {total_weighted_curvature / predicted:.4f}")
    
    # Try uniform weighting
    uniform_weight = 1.0 / V
    total_uniform = 0
    
    for vertex in all_vertices:
        incident = [m for m in state.modules if vertex in m.region]
        angle_sum = len(incident) * (PI / 3)
        curvature = 2 * PI - angle_sum
        total_uniform += curvature * uniform_weight
    
    print(f"\nWith uniform weighting (A=1/V):")
    print(f"sum(K * 1/V) = {total_uniform:.6f}")
    print(f"2π*χ = {predicted:.6f}")
    print(f"Ratio: {total_uniform / predicted:.4f}")
    
    # The key insight: maybe we need to NORMALIZE differently
    # Let's try: what if the formula is sum(K * A) = C * χ for some constant C?
    
    unweighted_sum = sum(2*PI - len([m for m in state.modules if v in m.region])*(PI/3) 
                         for v in all_vertices)
    
    print(f"\nFinding the normalization constant:")
    print(f"unweighted sum(K) = {unweighted_sum:.6f}")
    print(f"χ = {chi}")
    print(f"Implied constant: {unweighted_sum / chi:.6f}")
    print(f"Expected (2π): {2*PI:.6f}")
    print(f"Factor: {unweighted_sum / (2*PI*chi):.4f}")
    
    # This factor of ~2.5 is consistent!
    # Let me check: is this related to average vertex valence?
    
    avg_valence = sum(len([m for m in state.modules if v in m.region]) for v in all_vertices) / V
    
    print(f"\nAverage vertex valence: {avg_valence:.4f}")
    print(f"Factor / avg_valence: {(unweighted_sum / (2*PI*chi)) / avg_valence:.4f}")

if __name__ == "__main__":
    test_weighted_gauss_bonnet()
