"""Phase A2 (Phase C tightening): symbolic search for a non-degenerate
calibrated VMState witness on actually-triangulated graphs, under the
TIGHTENED [module_triangles] definition.

Difference from `tools/calibrated_witness_search.py` (which uses the
broken pre-tightening definition):

    OLD: module_triangles(m) = { (n1, n2) : n1 < n2, both adjacent to m }
    NEW: module_triangles(m) = { (n1, n2) : n1 < n2, both adjacent to m,
                                  AND n1 ~ n2 }       <-- mutual adjacency

The new requirement matches `coq/kernel/curvature/MuGravity.v` Phase C1.

Calibration at every module:
    angle_defect_curvature(m) = pi * mu_laplacian(m)
i.e.    2*pi - sum_{(n1,n2) in T_m} pi * d(n1,n2)/(1 + d(m,n1) + d(m,n2) + d(n1,n2))
        = pi * sum_{n adj m} (rho_n - rho_m)

After dividing by pi:
    2 - S_m = L_m         <==>     S_m + L_m = 2

where:
    S_m = sum over (n1, n2) in T_m of d(n1,n2) / (1 + d(m,n1) + d(m,n2) + d(n1,n2))
    L_m = sum over n adj m of (rho_n - rho_m)
    d(a, b) = 1 + M_a + M_b   (a != b)
    rho_i = encoding_length_i + region_size_i

Density side decouples; summing over m gives sum_m L_m = 0 (edge antisymmetry),
so the necessary structural condition is

    sum_m S_m = 2 N.

This script:
  1. Enumerates small triangulated graphs (K_4, K_4-e, octahedron, prism,
     K_5, etc.).
  2. Computes T_m under the tightened definition (mutual adjacency).
  3. Searches small mass-tuples M for sum_m S_m = 2N.
  4. Solves the per-module density linear system over Q.
  5. Reports any configuration that admits a non-negative integer rho.

Outcome 1: a witness is exhibited; print + write JSON.
Outcome 2: no witness within search bounds; print exhaustive log.
Outcome 3: a counting argument shows infeasibility (this script does NOT
attempt this; only Outcomes 1 and 2 are in scope).
"""

from __future__ import annotations

import json
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import Dict, List, Tuple


# --- Graph constructors -----------------------------------------------------


def make_K(n: int) -> List[Tuple[int, int]]:
    return [(a, b) for a in range(n) for b in range(a + 1, n)]


def make_K4_minus_edge() -> Tuple[int, List[Tuple[int, int]]]:
    """K_4 with one edge removed: vertices 0,1,2,3; missing edge (2,3).
    Triangles: {0,1,2}, {0,1,3}. Two triangles sharing edge (0,1)."""
    edges = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]
    return 4, edges


def make_octahedron() -> Tuple[int, List[Tuple[int, int]]]:
    n = 6
    antipodes = {(0, 1), (2, 3), (4, 5)}
    edges = []
    for a in range(n):
        for b in range(a + 1, n):
            if (a, b) not in antipodes:
                edges.append((a, b))
    return n, edges


def make_triangular_prism() -> Tuple[int, List[Tuple[int, int]]]:
    edges = [(0, 1), (1, 2), (0, 2),
             (3, 4), (4, 5), (3, 5),
             (0, 3), (1, 4), (2, 5)]
    return 6, edges


def make_double_tetrahedron() -> Tuple[int, List[Tuple[int, int]]]:
    """Bipyramid B_3 = two tetrahedra glued on a face: vertices 0,1,2 (shared
    face), 3 (top apex), 4 (bottom apex). Triangles: {0,1,2}, {0,1,3},
    {0,2,3}, {1,2,3}, {0,1,4}, {0,2,4}, {1,2,4}."""
    edges = [(0, 1), (0, 2), (1, 2),
             (0, 3), (1, 3), (2, 3),
             (0, 4), (1, 4), (2, 4)]
    return 5, edges


def make_icosahedron() -> Tuple[int, List[Tuple[int, int]]]:
    # 12 vertices, 30 edges, 20 triangles. Use canonical adjacency.
    # Vertices 0..11. Built from "antiprism + caps".
    n = 12
    # Top cap: 0 connects to 1..5; bottom cap: 11 connects to 6..10.
    # Middle: cycle 1-2-3-4-5-1 and 6-7-8-9-10-6 with rungs (i, j) where
    # i in upper, j in lower.
    edges = set()
    for i in range(1, 6):
        edges.add((0, i))
        edges.add((11, i + 5))
    for i in range(1, 6):
        nxt = i + 1 if i < 5 else 1
        edges.add(tuple(sorted((i, nxt))))
        nxt2 = i + 6 if i < 5 else 6
        edges.add(tuple(sorted((i + 5, nxt2))))
    # Rungs: each upper-middle vertex i connects to two lower-middle vertices.
    rungs = [(1, 6), (1, 10), (2, 6), (2, 7), (3, 7), (3, 8),
             (4, 8), (4, 9), (5, 9), (5, 10)]
    for r in rungs:
        edges.add(tuple(sorted(r)))
    return n, sorted(edges)


# --- Triangle / Laplacian computations -------------------------------------


def neighbors_of(edges: List[Tuple[int, int]], m: int) -> List[int]:
    out = set()
    for (a, b) in edges:
        if a == m:
            out.add(b)
        elif b == m:
            out.add(a)
    return sorted(out)


def adj_set(edges: List[Tuple[int, int]]) -> set:
    s = set()
    for (a, b) in edges:
        s.add((min(a, b), max(a, b)))
    return s


def is_adjacent(adj: set, a: int, b: int) -> bool:
    if a == b:
        return False
    return (min(a, b), max(a, b)) in adj


def triangles_at_tightened(edges: List[Tuple[int, int]], m: int) -> List[Tuple[int, int]]:
    """T_m under the tightened definition: pairs (n1, n2) with n1<n2, both
    adjacent to m, AND n1 ~ n2 in the graph."""
    adj = adj_set(edges)
    nbrs = neighbors_of(edges, m)
    out = []
    for i, a in enumerate(nbrs):
        for b in nbrs[i + 1:]:
            if is_adjacent(adj, a, b):
                out.append((a, b))
    return out


def has_geometric_triangle(edges: List[Tuple[int, int]], n: int) -> bool:
    return any(len(triangles_at_tightened(edges, m)) > 0 for m in range(n))


def d(M: List[int], a: int, b: int) -> int:
    if a == b:
        return 0
    return 1 + M[a] + M[b]


def S_m(edges: List[Tuple[int, int]], m: int, M: List[int]) -> Fraction:
    s = Fraction(0)
    for (n1, n2) in triangles_at_tightened(edges, m):
        d_mn1 = d(M, m, n1)
        d_mn2 = d(M, m, n2)
        d_n1n2 = d(M, n1, n2)
        denom = 1 + d_mn1 + d_mn2 + d_n1n2
        s += Fraction(d_n1n2, denom)
    return s


def total_S(edges: List[Tuple[int, int]], n: int, M: List[int]) -> Fraction:
    return sum((S_m(edges, m, M) for m in range(n)), Fraction(0))


# --- Density-side linear system --------------------------------------------


def density_solution_exists(edges: List[Tuple[int, int]], n: int,
                             M: List[int]) -> Tuple[bool, List[int]]:
    """Solve A rho = b where A_{m,m} = -deg(m), A_{m,j} = 1 for j adj m,
    b_m = 2 - S_m. Solvable iff sum_m b_m = 0. Then look for non-neg int
    rho."""
    A = [[Fraction(0)] * n for _ in range(n)]
    b = []
    for m in range(n):
        nbrs = neighbors_of(edges, m)
        A[m][m] = Fraction(-len(nbrs))
        for j in nbrs:
            A[m][j] = Fraction(1)
        b.append(Fraction(2) - S_m(edges, m, M))
    if sum(b, Fraction(0)) != 0:
        return False, []

    # Drop last equation (redundant), set rho_{n-1} = 0, solve for rho_0..rho_{n-2}.
    Ar = [[A[i][j] for j in range(n - 1)] for i in range(n - 1)]
    br = [b[i] for i in range(n - 1)]
    aug = [row + [r] for row, r in zip(Ar, br)]
    nrows = n - 1
    ncols = n - 1
    row = 0
    for col in range(ncols):
        pivot = None
        for r in range(row, nrows):
            if aug[r][col] != 0:
                pivot = r
                break
        if pivot is None:
            continue
        if pivot != row:
            aug[row], aug[pivot] = aug[pivot], aug[row]
        piv = aug[row][col]
        aug[row] = [x / piv for x in aug[row]]
        for r in range(nrows):
            if r != row and aug[r][col] != 0:
                f = aug[r][col]
                aug[r] = [aug[r][k] - f * aug[row][k] for k in range(ncols + 1)]
        row += 1
    sol = [Fraction(0)] * (n - 1)
    for r in range(nrows):
        for c in range(ncols):
            if aug[r][c] == 1 and all(aug[rr][c] == 0 for rr in range(nrows) if rr != r):
                sol[c] = aug[r][-1]
                break
    rho_full = sol + [Fraction(0)]
    # Shift so all are non-negative integers.
    minv = min(rho_full)
    shifted = [r - minv for r in rho_full]
    if all(s.denominator == 1 for s in shifted):
        return True, [int(s) for s in shifted]
    return False, []


# --- Search loop -----------------------------------------------------------


def search_one(name: str, n: int, edges: List[Tuple[int, int]],
               max_mass: int) -> Dict:
    has_tri = has_geometric_triangle(edges, n)
    out: Dict = {
        "config": name,
        "n": n,
        "edge_count": len(edges),
        "edges": edges,
        "has_geometric_triangle": has_tri,
        "max_mass_searched": max_mass,
        "S_m_total_target": 2 * n,
        "verdict": None,
        "solution": None,
        "samples": [],
    }
    if not has_tri:
        out["verdict"] = "skipped: no actual triangle in graph (mutual adjacency empty everywhere)"
        return out

    found = None
    samples = []
    hit_target = 0
    iterations = 0
    for M in product(range(max_mass + 1), repeat=n):
        iterations += 1
        Mlist = list(M)
        ts = total_S(edges, n, Mlist)
        if ts == 2 * n:
            hit_target += 1
            ok, rho = density_solution_exists(edges, n, Mlist)
            samples.append({"M": Mlist, "total_S": str(ts),
                            "density_ok": ok, "rho": rho if ok else None})
            if ok:
                found = (Mlist, rho)
                break
    out["iterations"] = iterations
    out["hit_target_count"] = hit_target
    out["samples"] = samples[:30]
    if found is not None:
        Mlist, rho = found
        # Report the per-module S_m values of the witness for verification.
        Sm_values = {m: str(S_m(edges, m, Mlist)) for m in range(n)}
        out["verdict"] = "WITNESS FOUND"
        out["solution"] = {
            "M": Mlist,
            "rho": rho,
            "S_m": Sm_values,
        }
    else:
        out["verdict"] = (f"no integer solution in mass cube [0..{max_mass}]^{n}; "
                          f"{hit_target} mass tuples hit sum_S = 2N target")
    return out


def count_triangles(edges: List[Tuple[int, int]], n: int) -> int:
    adj = adj_set(edges)
    T = 0
    for a in range(n):
        for b in range(a + 1, n):
            for c in range(b + 1, n):
                if (a, b) in adj and (b, c) in adj and (a, c) in adj:
                    T += 1
    return T


def structural_bound_check(name: str, n: int, edges: List[Tuple[int, int]]) -> Dict:
    """Check the necessary structural bound 4N/3 < T (where T is the number
    of mutually-adjacent triples).

    Each triangle (m, n1, n2) contributes a ratio r = (1+v+w)/(4+2u+2v+2w)
    with u=M_m, v=M_n1, w=M_n2. As v+w -> infinity and u=0, r -> 1/2 (sup).
    Each actual graph triangle has 3 such incidences across the 3 vertices,
    so each triangle contributes at most 3 * (1/2) = 3/2 to sum_m S_m.

    Therefore sum_m S_m < 3T/2 strictly. For calibration we need
    sum_m S_m = 2N, so a NECESSARY condition is 3T/2 > 2N, i.e. T > 4N/3.
    """
    T = count_triangles(edges, n)
    bound_max = Fraction(3 * T, 2)
    bound_min = Fraction(3 * T, 4)
    target = 2 * n
    feasible_in_range = bound_min < target < bound_max
    necessary_T = T > 4 * n / 3
    return {
        "config": name,
        "n": n,
        "edge_count": len(edges),
        "triangle_count_T": T,
        "target_sum_S_m": target,
        "lower_bound_at_M_zero": str(bound_min),
        "supremum_as_M_to_infinity": str(bound_max),
        "necessary_T_gt_4N_over_3": necessary_T,
        "target_in_open_interval": feasible_in_range,
    }


def main() -> None:
    print("=" * 76)
    print("Phase A2: search for non-degenerate calibrated witness under tightened")
    print("[module_triangles] (Phase C1 of MuGravity.v).")
    print("Calibration: S_m + L_m = 2 at every module; sum_m S_m = 2N (necessary).")
    print()
    print("STRUCTURAL UPPER BOUND (over non-negative integer masses):")
    print("  Each triangle ratio r = (1+v+w)/(4+2u+2v+2w) < 1/2 strictly.")
    print("  sum_m S_m < 3T/2 where T = # mutually-adjacent triples.")
    print("  Necessary: T > 4N/3.")
    print("=" * 76)

    configs = []

    # --- N = 4 ---
    configs.append(("K_4 (tetrahedron)", 4, make_K(4)))
    configs.append(("K_4 minus edge (diamond)", *make_K4_minus_edge()))

    # --- N = 5 ---
    configs.append(("K_5 (5-clique)", 5, make_K(5)))
    configs.append(("Bipyramid B_3 / double tetrahedron", *make_double_tetrahedron()))

    # --- N = 6 ---
    configs.append(("K_6 (6-clique)", 6, make_K(6)))
    configs.append(("Octahedron", *make_octahedron()))
    configs.append(("Triangular prism", *make_triangular_prism()))

    # --- N = 7 ---
    configs.append(("K_7 (7-clique)", 7, make_K(7)))

    # --- Bound analysis on each config first ---
    print()
    print("--- Structural-bound analysis ---")
    bounds = []
    for entry in configs:
        name, n, edges = entry
        bd = structural_bound_check(name, n, edges)
        bounds.append(bd)
        print(f"  {name}: T={bd['triangle_count_T']}, target=2N={bd['target_sum_S_m']}, "
              f"range=[{bd['lower_bound_at_M_zero']}, {bd['supremum_as_M_to_infinity']}), "
              f"feasible in range? {bd['target_in_open_interval']}, "
              f"T > 4N/3? {bd['necessary_T_gt_4N_over_3']}")

    results = []
    found_any = False
    for entry in configs:
        name, n, edges = entry
        # Mass-cube radius adapts to N (N^N grows fast).
        if n <= 4:
            mc = 6
        elif n == 5:
            mc = 5
        elif n == 6:
            mc = 4
        else:
            mc = 3
        print(f"\n--- {name} (N={n}, |E|={len(edges)}) ---")
        r = search_one(name, n, edges, mc)
        print(f"  has_geometric_triangle  = {r['has_geometric_triangle']}")
        print(f"  target sum_m S_m        = {r['S_m_total_target']}")
        print(f"  iterations              = {r.get('iterations', 'N/A')}")
        print(f"  hit_target_count        = {r.get('hit_target_count', 'N/A')}")
        print(f"  verdict                 = {r['verdict']}")
        if r["solution"]:
            found_any = True
            print(f"  M    = {r['solution']['M']}")
            print(f"  rho  = {r['solution']['rho']}")
            print(f"  S_m  = {r['solution']['S_m']}")
        elif r["samples"]:
            for s in r["samples"][:3]:
                print(f"    sample: M={s['M']}, total_S={s['total_S']}, "
                      f"density_ok={s['density_ok']}")
        results.append(r)

    print()
    print("=" * 76)
    if found_any:
        print("OUTCOME 1: at least one triangulated graph admits a non-degenerate "
              "calibrated witness under the tightened [module_triangles].")
    else:
        print("OUTCOME 2: NO configuration in this finite search admits a "
              "non-negative integer witness.")
        print("Document the bounds in the artifact log; F3 narrow remains "
              "non-vacuous in principle.")
    print("=" * 76)

    out_path = Path(__file__).resolve().parents[1] / "artifacts" / \
        "calibrated_witness_geometric_search.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w") as f:
        json.dump({
            "structural_bounds": bounds,
            "results": results,
            "found_any": found_any,
        }, f, indent=2, default=str)
    print(f"\nSearch log: {out_path}")


if __name__ == "__main__":
    main()
