"""Search for (graph, M) where S_m is integer for every module AND total_S = 2N.
Then density system has integer solution.

Strategy: enumerate graphs (small), enumerate small mass tuples, check both
constraints."""

from itertools import product, combinations
from fractions import Fraction
import sys
sys.path.insert(0, "/workspaces/The-Thiele-Machine/tools")
from calibrated_witness_search import (
    total_S, S_m, density_solution_exists, neighbors_of, triangles_at,
    make_graph_complete, make_graph_cycle, make_graph_octahedron, make_graph_prism,
    make_graph_K33, make_graph_wheel, make_graph_star,
)


def all_S_m_integer(edges, n, M):
    for m in range(n):
        sm = S_m(edges, n, m, M)
        if sm.denominator != 1:
            return False
    return True


def main():
    print("Search: (graph, M) with all S_m integer AND total_S = 2N.\n")

    # Test set of graphs
    graphs = []
    for N in range(3, 8):
        graphs.append((f"K_{N}", N, make_graph_complete(N)))
    for N in [3, 4, 5, 6, 7]:
        if N >= 3:
            graphs.append((f"C_{N}", N, make_graph_cycle(N)))
    graphs.append(("Star K_{1,3}", 4, make_graph_star(4)))
    graphs.append(("W_4", 5, make_graph_wheel(5)))
    graphs.append(("Octahedron", 6, make_graph_octahedron()))
    graphs.append(("Prism", 6, make_graph_prism()))
    graphs.append(("K_{3,3}", 6, make_graph_K33()))
    # Specific small graphs from the M=0 search:
    graphs.append(("Special_N7_a", 7, [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 6)]))

    # Enumerate non-isomorphic graphs on small N
    print("--- All non-isomorphic graphs on N <= 5 ---")
    def all_simple_graphs(n):
        """Generate all (non-iso) simple graphs by edge mask, then deduplicate by canonical form."""
        seen = set()
        for mask in range(2 ** (n * (n - 1) // 2)):
            edges = []
            bit = 0
            for a in range(n):
                for b in range(a + 1, n):
                    if (mask >> bit) & 1:
                        edges.append((a, b))
                    bit += 1
            # Canonical form via sorted degree sequence as a coarse hash (not full iso)
            yield edges

    # For each graph, search M
    print("\nMain search:")
    found_count = 0
    for (name, n, edges) in graphs:
        target = Fraction(2 * n)
        # Find max degree
        from collections import Counter
        deg = Counter()
        for (a, b) in edges:
            deg[a] += 1; deg[b] += 1
        # Search M up to small range
        max_mass = 6 if n <= 5 else 4
        for M in product(range(max_mass + 1), repeat=n):
            M = list(M)
            if all_S_m_integer(edges, n, M):
                ts = total_S(edges, n, M)
                if ts == target:
                    print(f"  {name} (N={n}): M={M}, total_S={ts}, all S_m integer")
                    ok, rho = density_solution_exists(edges, n, M)
                    print(f"    density solution: ok={ok}, rho={rho}")
                    if ok:
                        found_count += 1
                        print(f"    *** FULL WITNESS ***")

    print(f"\nTotal full witnesses found: {found_count}")

    # Side investigation: enumerate small graphs (N=3..5) freely
    print("\n--- Free enumeration of small graphs N=3..5 with M=[0..3]^N ---")
    for N in range(3, 6):
        target = Fraction(2 * N)
        for edges in all_simple_graphs(N):
            for M in product(range(4), repeat=N):
                M = list(M)
                # Need >=1 module with deg >= 2 to have a triangle
                deg = [0] * N
                for (a, b) in edges:
                    deg[a] += 1; deg[b] += 1
                if all(d < 2 for d in deg):
                    continue
                if all_S_m_integer(edges, N, M):
                    ts = total_S(edges, N, M)
                    if ts == target:
                        ok, rho = density_solution_exists(edges, N, M)
                        if ok:
                            print(f"  N={N}, edges={edges}, M={M}, ts={ts}, rho={rho}  *** WITNESS ***")
                            found_count += 1
                        else:
                            print(f"  N={N}, edges={edges}, M={M}, ts={ts}: integer S_m but no density solution")
    print(f"\nFinal witness count: {found_count}")


if __name__ == "__main__":
    main()
