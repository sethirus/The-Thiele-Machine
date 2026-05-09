"""Deep search on octahedron: total_S(M) is rational and can exceed target=12
(found configurations with ts > 12 and ts < 12 in random search). The question
is whether 2N = 12 is attained EXACTLY at some integer mass tuple.

Search strategy: random-restart hill climbing in mass space."""

from fractions import Fraction
from itertools import product
import random
import sys
sys.path.insert(0, "/workspaces/The-Thiele-Machine/tools")
from calibrated_witness_search import (
    total_S, S_m, density_solution_exists, make_graph_octahedron,
    neighbors_of, triangles_at,
)


def compare(ts, target):
    """Return -1, 0, or 1."""
    if ts < target:
        return -1
    if ts > target:
        return 1
    return 0


def main():
    n = 6
    edges = make_graph_octahedron()
    target = Fraction(2 * n, 1)
    random.seed(123)

    # Phase 1: random search to find above and below target
    print("Octahedron deep search for exact total_S = 12.")
    print("=" * 60)
    above = []  # (ts, M)
    below = []
    exact_found = []
    for trial in range(200000):
        M = [random.randint(0, 50) for _ in range(n)]
        ts = total_S(edges, n, M)
        if ts == target:
            exact_found.append(list(M))
            if len(exact_found) >= 5:
                break
        elif ts < target:
            below.append((ts, list(M)))
        else:
            above.append((ts, list(M)))
    print(f"Random search 200000 trials, M_i in [0,50]:")
    print(f"  Configurations above target (ts > 12): {len(above)}")
    print(f"  Configurations below target (ts < 12): {len(below)}")
    print(f"  Exact-match configurations: {len(exact_found)}")
    if exact_found:
        print(f"  Examples of exact matches:")
        for M in exact_found[:5]:
            print(f"    M={M}")

    # Sort and look at closest from each side
    above.sort(key=lambda x: x[0])
    below.sort(key=lambda x: -x[0])
    print()
    print(f"Closest above target (5 nearest):")
    for ts, M in above[:5]:
        gap = ts - target
        print(f"  M={M}, ts={float(ts):.8f}, gap=+{float(gap):.4e}")
    print(f"Closest below target (5 nearest):")
    for ts, M in below[:5]:
        gap = target - ts
        print(f"  M={M}, ts={float(ts):.8f}, gap=-{float(gap):.4e}")

    # Phase 2: 1-step neighbor search around the closest configurations
    print()
    print("Neighbor search around closest configurations:")

    def neighbor_search(seed_M, depth=2, max_change=2):
        """Try changing each coordinate by +/- delta in [-max_change, max_change]."""
        best_above = None
        best_below = None
        for delta_tuple in product(range(-max_change, max_change + 1), repeat=n):
            M = [max(0, seed_M[i] + delta_tuple[i]) for i in range(n)]
            ts = total_S(edges, n, M)
            if ts == target:
                return M
            elif ts > target and (best_above is None or ts < best_above[0]):
                best_above = (ts, list(M))
            elif ts < target and (best_below is None or ts > best_below[0]):
                best_below = (ts, list(M))
        return None

    seeds = (above[:3] + below[:3])
    for ts, M in seeds:
        result = neighbor_search(M, max_change=2)
        if result is not None:
            print(f"  EXACT WITNESS FOUND: M={result}")
            ok, rho = density_solution_exists(edges, n, result)
            print(f"    density check: ok={ok}, rho={rho}")
            return result

    # Phase 3: Sympy continuous "between" search.
    # We have a config A above target and a config B below target. We can do a
    # bisection or test the "midpoint" lattice.
    print()
    print("Bisection / lattice search between above and below configurations:")
    if above and below:
        ts_a, M_a = above[0]
        ts_b, M_b = below[0]
        # Sweep along the line M_b -> M_a with integer steps.
        for t in range(-3, 200):
            M_t = [M_b[i] + (t * (M_a[i] - M_b[i])) // 100 for i in range(n)]
            if any(x < 0 for x in M_t):
                continue
            ts = total_S(edges, n, M_t)
            if ts == target:
                print(f"  EXACT WITNESS via bisection: M={M_t}")
                ok, rho = density_solution_exists(edges, n, M_t)
                print(f"    density check: ok={ok}, rho={rho}")
                return M_t

    # Phase 4: try the pattern [a, b, a, b, a, b] (alternating among antipodal pairs)
    # since the octahedron has 3 antipodal pairs.
    print()
    print("Search pattern: M_0 = M_1 = a, M_2 = M_3 = b, M_4 = M_5 = c.")
    found = []
    for a in range(0, 30):
        for b in range(0, 30):
            for c in range(0, 30):
                M = [a, a, b, b, c, c]
                ts = total_S(edges, n, M)
                if ts == target:
                    found.append((list(M), ts))
                    if len(found) > 10:
                        break
    if found:
        print(f"  Found {len(found)} antipode-symmetric solutions (a=M_0=M_1, b=M_2=M_3, c=M_4=M_5):")
        for M, ts in found[:5]:
            ok, rho = density_solution_exists(edges, n, M)
            print(f"    M={M}, ts={ts}, density_ok={ok}, rho={rho}")
    else:
        print("  No antipode-symmetric integer solution found in 30^3 cube.")

    # Print the analytical equation for antipode-symmetric on octahedron
    print()
    print("Antipode-symmetric octahedron sympy analysis:")
    import sympy as sp
    a, b, c = sp.symbols('a b c', integer=True, nonnegative=True)
    masses = [a, a, b, b, c, c]
    def D(i, j):
        if i == j:
            return 0
        return 1 + masses[i] + masses[j]
    total = sp.Integer(0)
    for m in range(n):
        nbrs = neighbors_of(edges, n, m)
        for i, n1 in enumerate(nbrs):
            for n2 in nbrs[i+1:]:
                num = D(n1, n2)
                den = 1 + D(m, n1) + D(m, n2) + D(n1, n2)
                total = total + sp.Mul(num, sp.Pow(den, -1))
    total = sp.together(total)
    # Solve total = 12
    print("  total_S(a,b,c) =")
    print("   ", sp.simplify(total))
    print()
    print("  Solving total_S = 12 over non-negative integers (sympy):")
    sol = sp.solve(sp.Eq(total, 12), [a, b, c], dict=True)
    print(f"  Solutions: {sol}")


if __name__ == "__main__":
    main()
