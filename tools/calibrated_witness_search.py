"""Phase A: symbolic search for a finite calibrated VMState witness.

Setup. Given a partition graph topology G = (V, E) on N = |V| modules:
  - structural mass M_i in N (per module),
  - mu-cost density rho_i in N (per module),
  - mu-distance d(a, b) = 1 + M_a + M_b for a != b,
  - module_neighbors(m) = { n : (m, n) in E },
  - module_triangles(m) = { (n1, n2) : n1 < n2, both in neighbors(m) },
    (NB: kernel does NOT require n1 ~ n2 to count; just both adjacent to m),
  - triangle_angle(m, n1, n2) = pi * d(n1, n2) / (1 + d(m, n1) + d(m, n2) + d(n1, n2)),
  - S_m := sum over T_m of d(n1, n2) / (1 + d(m,n1) + d(m,n2) + d(n1,n2)),
  - L_m := sum over neighbors(m) of (rho_n - rho_m).

Calibration at every module:
    2*pi - pi * S_m = pi * L_m   <=>   S_m + L_m = 2.

Density side decouples. Summing over m: sum_m L_m = 0 by edge antisymmetry,
so the necessary condition on structural-mass parameters is

    sum_m S_m = 2 N.

If this is solvable in non-negative integers, the density side admits a
solution iff for each m, there exist non-negative integers rho_n (n in V)
with sum_{n adj m} (rho_n - rho_m) = 2 - S_m. With shifts, that becomes
a linear system in N variables with N - 1 independent equations
(one is redundant by sum-zero), generically solvable.

This script enumerates configurations (N, graph, structural-mass tuple)
and checks the structural-mass equation per module:
    S_m = 2 - L_m     (a system of N equations in N + N rho-shifts)
or, equivalently, decouples and solves the structural side first.

Anti-shortcut: every configuration must have at least one module with
non-empty module_triangles, i.e. at least one module of degree >= 2.
"""

from fractions import Fraction
from itertools import combinations, product
from typing import Dict, List, Tuple


def make_graph_complete(n: int) -> List[Tuple[int, int]]:
    return [(a, b) for a in range(n) for b in range(a + 1, n)]


def make_graph_cycle(n: int) -> List[Tuple[int, int]]:
    return [(i, (i + 1) % n) if i < (i + 1) % n else ((i + 1) % n, i) for i in range(n)]


def make_graph_star(n: int) -> List[Tuple[int, int]]:
    # Center is 0, leaves are 1..n-1
    return [(0, i) for i in range(1, n)]


def make_graph_wheel(n: int) -> List[Tuple[int, int]]:
    # Wheel W_{n-1}: hub 0 + cycle on 1..n-1
    edges = [(0, i) for i in range(1, n)]
    rim = [(i, i + 1) for i in range(1, n - 1)] + [(1, n - 1)]
    return edges + [tuple(sorted(e)) for e in rim]


def make_graph_octahedron() -> List[Tuple[int, int]]:
    # 6 vertices, each connected to all but its antipode.
    # Antipodes: (0,1), (2,3), (4,5).
    n = 6
    antipodes = {(0, 1), (2, 3), (4, 5)}
    edges = []
    for a in range(n):
        for b in range(a + 1, n):
            if (a, b) not in antipodes:
                edges.append((a, b))
    return edges


def make_graph_prism() -> List[Tuple[int, int]]:
    # Triangular prism: two triangles {0,1,2} and {3,4,5}, with rungs 0-3, 1-4, 2-5.
    return [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (0, 3), (1, 4), (2, 5)]


def make_graph_K33() -> List[Tuple[int, int]]:
    # Bipartite K_{3,3}: parts {0,1,2} and {3,4,5}.
    return [(a, b) for a in range(3) for b in range(3, 6)]


def neighbors_of(edges: List[Tuple[int, int]], n: int, m: int) -> List[int]:
    out = []
    for (a, b) in edges:
        if a == m:
            out.append(b)
        elif b == m:
            out.append(a)
    return sorted(set(out))


def triangles_at(edges: List[Tuple[int, int]], n: int, m: int) -> List[Tuple[int, int]]:
    nbrs = neighbors_of(edges, n, m)
    # Kernel: all pairs (n1, n2) with n1 < n2 of neighbors (no n1~n2 requirement)
    return [(a, b) for i, a in enumerate(nbrs) for b in nbrs[i + 1:]]


def d(M: List[int], a: int, b: int) -> int:
    if a == b:
        return 0
    return 1 + M[a] + M[b]


def S_m(edges: List[Tuple[int, int]], n: int, m: int, M: List[int]) -> Fraction:
    s = Fraction(0)
    for (n1, n2) in triangles_at(edges, n, m):
        d_ab = d(M, m, n1)
        d_ac = d(M, m, n2)
        d_bc = d(M, n1, n2)
        denom = 1 + d_ab + d_ac + d_bc
        s += Fraction(d_bc, denom)
    return s


def total_S(edges: List[Tuple[int, int]], n: int, M: List[int]) -> Fraction:
    return sum((S_m(edges, n, i, M) for i in range(n)), Fraction(0))


def has_triangle_module(edges: List[Tuple[int, int]], n: int) -> bool:
    return any(len(triangles_at(edges, n, m)) > 0 for m in range(n))


def density_solution_exists(edges: List[Tuple[int, int]], n: int, M: List[int]) -> Tuple[bool, List[int]]:
    """Given chosen structural masses M, check whether non-negative integer densities
    rho_0..rho_{n-1} exist with: for every m, sum_{j adj m} (rho_j - rho_m) = 2 - S_m.

    The system is linear: A rho = b, where A_{m,m} = -deg(m), A_{m,j} = 1 for j adj m.
    rank deficient by 1 (rows sum to 0). Solvable iff sum_m b_m = 0,
    which equals sum_m (2 - S_m) = 2n - total_S = 0, i.e. total_S = 2n.
    Then a particular solution lives in Q; we look for non-negative integer one.
    """
    import numpy as np
    A = [[0] * n for _ in range(n)]
    b_target = []
    for m in range(n):
        nbrs = neighbors_of(edges, n, m)
        deg = len(nbrs)
        A[m][m] = -deg
        for j in nbrs:
            A[m][j] = 1
        sm = S_m(edges, n, m, M)
        b_target.append(Fraction(2) - sm)

    # Check global sum-zero
    if sum(b_target, Fraction(0)) != 0:
        return False, []

    # Solve for rho (over rationals). Use the fact that null space is span of (1, 1, ..., 1).
    # Drop last equation (redundant), set rho_{n-1} = 0, solve for rho_0..rho_{n-2}.
    # System: M_red rho_red = b_red - A[:,n-1] * 0 = b_red.
    M_red = [[Fraction(A[i][j]) for j in range(n - 1)] for i in range(n - 1)]
    b_red = [b_target[i] for i in range(n - 1)]
    # Gauss elimination
    rho = list(b_red)
    aug = [row + [r] for row, r in zip(M_red, rho)]
    nrows = n - 1
    ncols = n - 1
    # Forward elimination
    row = 0
    for col in range(ncols):
        # Find pivot
        pivot_row = None
        for r in range(row, nrows):
            if aug[r][col] != 0:
                pivot_row = r
                break
        if pivot_row is None:
            continue
        if pivot_row != row:
            aug[row], aug[pivot_row] = aug[pivot_row], aug[row]
        # Normalize
        piv = aug[row][col]
        aug[row] = [x / piv for x in aug[row]]
        for r in range(nrows):
            if r != row and aug[r][col] != 0:
                factor = aug[r][col]
                aug[r] = [aug[r][k] - factor * aug[row][k] for k in range(ncols + 1)]
        row += 1
    # Read solution
    sol = [Fraction(0)] * (n - 1)
    for r in range(nrows):
        # find pivot col
        pcol = None
        for c in range(ncols):
            if aug[r][c] == 1 and all(aug[rr][c] == 0 for rr in range(nrows) if rr != r):
                pcol = c
                break
        if pcol is None:
            continue
        sol[pcol] = aug[r][-1]
    rho_full = sol + [Fraction(0)]
    # Shift to non-negative integers if possible
    # rho_full + c * (1,1,...,1) is also a solution. Need each entry to be a non-negative integer.
    # Pick c such that all rho_full[i] + c are non-negative integers.
    # First need each rho_full[i] to share the same fractional part (so a single c can integerize).
    fracs = [r - int(r) if r >= 0 else r - (int(r) - 1) for r in rho_full]
    # Simpler: shift by -min and check integrality.
    minv = min(rho_full)
    shifted = [r - minv for r in rho_full]
    if all(s.denominator == 1 for s in shifted):
        return True, [int(s) for s in shifted]
    # Try adding a rational c so all become integers, with same denominator.
    common_denom = 1
    for s in shifted:
        common_denom = common_denom * s.denominator // _gcd(common_denom, s.denominator)
    # Multiply all rho by common_denom: a valid solution has same gradients scaled? No,
    # gradients are absolute (rho_j - rho_m). We can't rescale. So if denominators differ,
    # there is NO non-negative integer solution.
    return False, []


def _gcd(a: int, b: int) -> int:
    while b:
        a, b = b, a % b
    return abs(a)


def search_configuration(name: str, n: int, edges: List[Tuple[int, int]],
                         max_mass: int = 6,
                         require_triangle: bool = True) -> Dict:
    """Try all M_0..M_{n-1} in [0, max_mass]^n.
    Returns dict with verdict and any solution found.
    """
    has_tri = has_triangle_module(edges, n)
    result = {
        "config": name,
        "n": n,
        "edges": edges,
        "has_triangle_module": has_tri,
        "max_mass_searched": max_mass,
        "verdict": None,
        "solution": None,
        "S_m_total_target": 2 * n,
        "samples": [],
    }
    if require_triangle and not has_tri:
        result["verdict"] = "skipped: no triangle module"
        return result

    found = None
    samples = []
    for M in product(range(max_mass + 1), repeat=n):
        M = list(M)
        ts = total_S(edges, n, M)
        if ts == 2 * n:
            ok, rho = density_solution_exists(edges, n, M)
            samples.append({"M": M, "total_S": str(ts), "density_ok": ok, "rho": rho})
            if ok:
                found = (M, rho)
                break
        else:
            # record some samples for audit
            if len(samples) < 3:
                samples.append({"M": M, "total_S": str(ts), "density_ok": "n/a"})
    result["samples"] = samples[:30]
    if found is not None:
        M, rho = found
        result["verdict"] = "SOLUTION FOUND"
        result["solution"] = {"M": M, "rho": rho}
    else:
        result["verdict"] = "no integer solution in mass cube"
    return result


def main():
    configurations = []

    # N = 3
    configurations.append(("K3 (triangle)", 3, make_graph_complete(3)))
    # 3-cycle = K3
    # 3-path: 0-1-2, only m=1 has 1 triangle (degree 2 -> 1 pair)
    configurations.append(("P3 (path 0-1-2)", 3, [(0, 1), (1, 2)]))

    # N = 4
    configurations.append(("K4 (tetrahedron)", 4, make_graph_complete(4)))
    configurations.append(("C4 (4-cycle)", 4, make_graph_cycle(4)))
    configurations.append(("Star K_{1,3}", 4, make_graph_star(4)))
    configurations.append(("Diamond (K4 minus edge)", 4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]))

    # N = 5
    configurations.append(("K5", 5, make_graph_complete(5)))
    configurations.append(("C5 (5-cycle)", 5, make_graph_cycle(5)))
    configurations.append(("W4 (wheel)", 5, make_graph_wheel(5)))

    # N = 6
    configurations.append(("K6", 6, make_graph_complete(6)))
    configurations.append(("C6 (6-cycle)", 6, make_graph_cycle(6)))
    configurations.append(("Octahedron", 6, make_graph_octahedron()))
    configurations.append(("Triangular prism", 6, make_graph_prism()))
    configurations.append(("K_{3,3}", 6, make_graph_K33()))

    # N = 7
    configurations.append(("K7", 7, make_graph_complete(7)))
    configurations.append(("C7", 7, make_graph_cycle(7)))
    # Heawood would be 14 vertices; skip — too large, also degree 6 already covered by K7

    print("=" * 70)
    print("Phase A: symbolic search for finite calibrated VMState witness")
    print("Calibration condition per module: S_m + L_m = 2 (after dividing by pi)")
    print("Necessary structural condition: sum_m S_m = 2N")
    print("=" * 70)
    print()

    results = []
    found_any = False
    for (name, n, edges) in configurations:
        print(f"--- {name} (N={n}, |E|={len(edges)}) ---")
        # Use smaller mass cube for larger N to keep runtime reasonable
        if n <= 4:
            mc = 8
        elif n == 5:
            mc = 6
        elif n == 6:
            mc = 4
        else:
            mc = 3
        r = search_configuration(name, n, edges, max_mass=mc)
        print(f"  has_triangle_module = {r['has_triangle_module']}")
        print(f"  target sum_m S_m    = {r['S_m_total_target']}")
        print(f"  verdict             = {r['verdict']}")
        if r["solution"]:
            found_any = True
            print(f"  M  = {r['solution']['M']}")
            print(f"  rho= {r['solution']['rho']}")
        elif r["samples"]:
            # Show a couple of samples for audit
            for s in r["samples"][:3]:
                print(f"    M={s['M']}, total_S={s['total_S']}, density_ok={s['density_ok']}")
        print()
        results.append(r)

    print("=" * 70)
    if found_any:
        print("RESULT: at least one configuration admits a finite calibrated witness.")
    else:
        print("RESULT: NO configuration in N <= 7 search space admits an integer "
              "structural-mass solution achieving sum_m S_m = 2N.")
    print("=" * 70)

    # Print the per-module equations for the *first* small case (K3)
    print()
    print("Sanity dump: per-module equations on K3 with M_i symbolic")
    import sympy as sp
    M0, M1, M2 = sp.symbols('M0 M1 M2', integer=True, nonnegative=True)
    rho0, rho1, rho2 = sp.symbols('rho0 rho1 rho2', integer=True, nonnegative=True)
    pi = sp.pi
    def D(a, b, Ma, Mb):
        return 1 + Ma + Mb
    n = 3
    edges = make_graph_complete(3)
    Mvars = [M0, M1, M2]
    rhos = [rho0, rho1, rho2]
    for m in range(n):
        nbrs = neighbors_of(edges, n, m)
        S = 0
        for (a, b) in triangles_at(edges, n, m):
            dab = D(m, a, Mvars[m], Mvars[a])
            dac = D(m, b, Mvars[m], Mvars[b])
            dbc = D(a, b, Mvars[a], Mvars[b])
            S += sp.Rational(1) * dbc / (1 + dab + dac + dbc)
        L = sum(rhos[j] - rhos[m] for j in nbrs)
        eq = sp.Eq(S + L, 2)
        print(f"  module {m}: {sp.simplify(eq)}")

    return results, found_any


if __name__ == "__main__":
    main()
