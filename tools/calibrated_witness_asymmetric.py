"""Phase A asymmetric search. The earlier search assumed sorted masses (WLOG
under graph symmetry), but for asymmetric configurations or non-vertex-
transitive graphs we should be more general.

Approach: for each graph, try all integer mass tuples with each entry in
[0, max_mass]. Look for total_S = 2N in particular.

Key bounds derived analytically:
  - For K_N with finite masses: total_S < C(N,3) strictly. So K_N can hit
    target 2N only if C(N,3) > 2N, i.e., N >= 6, AND target is achievable
    from below. K_5: C(5,3)=10=2N, asymptote = target, never reached.
    K_6: C(6,3)=20, target=12. M=0 already gives total_S=15>12. Asymptote=20.
       Can we go BELOW 15 with asymmetric masses?
    K_7: M=0 gives 35*1/4=8.75 ... wait, 21 triples * 1/4 = 5.25? Let me recompute.

Wait: number of triangle term-triples in K_N is N * C(N-1, 2) = 3*C(N,3). For N=6:
3*20 = 60 triangle terms. At M=0 each is 1/4, total = 60/4 = 15. ✓ for K_6.
For K_7: 3*35 = 105 triangle terms, total at M=0 = 105/4 = 26.25.

Important question: can K_6 with non-uniform masses give total_S < 15?
Per-triangle-term ratio at apex m: d(a,b)/(1+d(m,a)+d(m,b)+d(a,b)).
With M_m huge, M_a=M_b=0: ratio -> 0. But this also affects OTHER apexes.
Look at it via the 3-apex sum for the triple {m,a,b}: (A+B+C)/(1+A+B+C).
This is monotonically increasing in A+B+C (since 1 - 1/(1+s) is increasing).
So minimum 3-apex contribution per triple is at A=B=C=1 (M=0 everywhere),
giving 3/4. Max approaches 1 (all big).

So total_S over K_N has range [(3T+W)/4, ...) where T=#triangles, W=#wedges.
For K_N: T=C(N,3), W=0. Range = [3*C(N,3)/4, C(N,3)).
K_6: [15, 20). Target=12. Below the range. INFEASIBLE.
K_7: [26.25, 35). Target=14. Below range. INFEASIBLE.
K_8: [42, 56). Target=16. INFEASIBLE.
K_5: [7.5, 10). Target=10. Asymptotically reaches but not attained. INFEASIBLE.
K_4: [3, 4). Target=8. Above range. INFEASIBLE.
K_3: [0.75, 1). Target=6. Above range. INFEASIBLE.

So NO K_N achieves it.

For non-complete graphs (T triangles, W wedges):
  total_S range ~= [(3T+W)/4, target_asymptote).
For target 2N: need (3T+W)/4 <= 2N <= some upper limit.
Lower: 3T+W <= 8N, i.e., Sum_m C(deg(m),2) <= 8N.
Upper: total_S can exceed asymptote 1/3 with asymmetric masses, going up to 1/2 per term.
       So upper bound is (3T+W)/2.

For exact 2N: need (3T+W)/4 <= 2N < (3T+W)/2, i.e., 4N < 3T+W <= 8N.

For graphs with sum_m C(deg,2) = 4N+k (k in [1, 4N]), target might be achievable.
Concrete: octahedron has sum_m C(4,2) = 6*6 = 36 = 6N; target 12. 4N=24 < 36, 8N=48>36.
So octahedron is in feasibility window. M=0 gives 36/4=9. Target 12. Need to push UP.

Search octahedron with asymmetric masses.
"""

from fractions import Fraction
from itertools import product
import sys
sys.path.insert(0, "/workspaces/The-Thiele-Machine/tools")
from calibrated_witness_search import (
    make_graph_complete, make_graph_cycle, make_graph_star, make_graph_wheel,
    make_graph_octahedron, make_graph_prism, make_graph_K33,
    total_S, S_m, density_solution_exists, neighbors_of, triangles_at,
)


def search_full(name, n, edges, max_mass, target):
    """Full search (not sorted) over mass cube."""
    found = []
    closest = []  # (|diff|, M, total_S)
    for M in product(range(max_mass + 1), repeat=n):
        M = list(M)
        ts = total_S(edges, n, M)
        diff = abs(ts - target)
        if ts == target:
            ok, rho = density_solution_exists(edges, n, M)
            found.append((M, ts, ok, rho))
            if ok:
                return found, closest
        if len(closest) < 8 or diff < closest[-1][0]:
            closest.append((diff, M, ts))
            closest.sort(key=lambda x: x[0])
            closest = closest[:8]
    return found, closest


def main():
    target_graphs = [
        ("Octahedron N=6", 6, make_graph_octahedron(), 6),  # target 12, asymptote 12
        ("Triangular prism N=6", 6, make_graph_prism(), 6),
        ("K_3,3 N=6", 6, make_graph_K33(), 6),
        ("K_4 N=4", 4, make_graph_complete(4), 8),  # asymptote 4 < 8 — infeasible
        ("Diamond N=4", 4, [(0,1),(0,2),(0,3),(1,2),(1,3)], 8),
        ("K_5 N=5", 5, make_graph_complete(5), 5),  # asymptote 10 = target — infeasible
        # 4-regular bipartite small:
        ("K_4 minus PM N=4", 4, [(0,1),(2,3),(0,2),(1,3)], 6),  # 4-cycle is 2-regular — irrelevant
    ]

    for (name, n, edges, mmax) in target_graphs:
        print(f"\n=== {name} ===")
        target = Fraction(2 * n, 1)
        # Compute structural quantities
        T = 0
        W = 0
        edge_set = set(tuple(sorted(e)) for e in edges)
        for m in range(n):
            nbrs = neighbors_of(edges, n, m)
            for i, a in enumerate(nbrs):
                for b in nbrs[i+1:]:
                    if tuple(sorted([a, b])) in edge_set:
                        T += 1  # triangle term (apex m)
                    else:
                        W += 1  # wedge term
        # T counts each triangle 3 times (once per apex)
        triangles = T // 3
        wedges = W
        sumC = T + W  # = sum_m C(deg(m), 2) = 3*triangles + wedges
        print(f"  triangles in graph = {triangles}, wedges (paths of len 2) = {wedges}")
        print(f"  Sum_m C(deg(m), 2) = {sumC}")
        print(f"  total_S range estimate: [{sumC/4:.3f}, ...)")
        print(f"  target = {target} = {float(target)}")
        # Asymptote (uniform M -> infty):
        # triangle term -> 1/3, wedge term -> 1/3
        # so asymptote = sumC/3
        print(f"  uniform-mass asymptote (M->infty): {sumC/3:.4f}")

        found, closest = search_full(name, n, edges, mmax, target)
        if found:
            print(f"  FOUND {len(found)} solutions:")
            for f in found[:5]:
                print(f"    M={f[0]}, total_S={f[1]}, density_ok={f[2]}, rho={f[3]}")
        else:
            print(f"  No exact total_S = {target} solutions (mass cube up to {mmax})")
            print(f"  Closest configurations (|total_S - target|, M, total_S):")
            for c in closest[:5]:
                print(f"    diff={c[0]}={float(c[0]):.4f}, M={c[1]}, total_S={c[2]}={float(c[2]):.4f}")


if __name__ == "__main__":
    main()
