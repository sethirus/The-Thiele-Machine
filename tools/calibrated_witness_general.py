"""More general search: try various small graph families with constraint
that S_m is integer for every m AND total_S = 2N AND the density solution
respects the kernel's encoding-length-mod-8 constraint.

Constraint summary for a witness in the kernel:
1. Graph has N modules, edges given by region overlaps.
2. Per module m: M_m = R_m + A_m (region size + axiom count, both >= 0).
3. Per module m: rho_m = enc_m + R_m, where enc_m is a multiple of 8 and >= 0.
4. S_m + L_m = 2 at every m, where:
   - S_m = sum of distance-weighted angle ratios at m (integer required).
   - L_m = sum_{n adj m} (rho_n - rho_m).
5. Total S = sum_m S_m = 2N.
6. Realizability: for non-overlapping regions of leaves with center, etc.
   For star: center R_C >= n (number of leaves).

This search varies multiple structural parameters."""

from fractions import Fraction
from itertools import product, combinations


def make_star(n_leaves):
    return [(0, i) for i in range(1, n_leaves + 1)]


def neighbors(edges, n, m):
    return sorted({b for (a, b) in edges if a == m} | {a for (a, b) in edges if b == m})


def d_dist(M, a, b):
    if a == b:
        return 0
    return 1 + M[a] + M[b]


def s_at(edges, n, m, M):
    nbrs = neighbors(edges, n, m)
    s = Fraction(0)
    for i, n1 in enumerate(nbrs):
        for n2 in nbrs[i+1:]:
            num = d_dist(M, n1, n2)
            denom = 1 + d_dist(M, m, n1) + d_dist(M, m, n2) + d_dist(M, n1, n2)
            s += Fraction(num, denom)
    return s


def total_S(edges, n, M):
    return sum((s_at(edges, n, m, M) for m in range(n)), Fraction(0))


def realize_star(N, M_center, M_leaf):
    """Star K_{1,N-1} witness realizability check."""
    n_leaves = N - 1
    edges = make_star(n_leaves)
    M = [M_center] + [M_leaf] * n_leaves

    # Compute S_m
    s_c = s_at(edges, N, 0, M)
    s_l = s_at(edges, N, 1, M)  # all leaves identical by symmetry
    if s_c.denominator != 1 or s_l.denominator != 1:
        return None
    s_c_int = int(s_c); s_l_int = int(s_l)
    ts = s_c_int + n_leaves * s_l_int
    if ts != 2 * N:
        return None

    # Density at leaf: rho_C - rho_L = 2 - S_L = 2 - 0 = 2
    # Density at center: sum_{leaves} (rho_L - rho_C) = -2(N-1) = 2 - S_C
    # Consistent iff -2(N-1) = 2 - S_C, i.e., S_C = 2N -- WAIT that's the same as ts = 2N
    # which holds. So the system is consistent.

    # rho_C - rho_L = 2; need realizable in kernel.
    # rho_C = enc_C + R_C, rho_L = enc_L + R_L, R_C >= 1 (leaves need overlap).
    # For pairwise non-adjacent leaves, leaf regions are disjoint;
    # each leaf has at least one cell in center's region.
    # Minimum: R_C = n_leaves (one shared cell per leaf), R_L = 1.
    # Actually leaves could share their *non-shared* cells with each other? No,
    # any cell in leaf_i ∩ leaf_j makes them adjacent. So leaf regions disjoint.
    # Each leaf has 1+ cells, center has at least the union of {one cell per leaf}.

    # Simplest: R_L = r_L (each leaf has same r_L cells, all distinct), then
    # center must include at least n_leaves cells (one per leaf), so R_C >= n_leaves.
    # Also each leaf's cells beyond the shared one are NOT in center's region (no constraint).
    # So R_C >= n_leaves; R_L >= 1.
    # M_center = R_C + A_C, with A_C >= 0, so R_C <= M_center.
    # So n_leaves <= R_C <= M_center.

    if M_center < n_leaves:
        return None  # cannot fit n_leaves distinct shared cells in center

    # M_leaf = R_L + A_L, R_L <= M_leaf.

    # Try (R_C, R_L) combinations for which density arithmetic works.
    # rho_C - rho_L = 2 means (enc_C + R_C) - (enc_L + R_L) = 2.
    # enc_C, enc_L are non-negative multiples of 8.
    # So enc_C - enc_L = 2 - (R_C - R_L) = 2 - R_C + R_L.
    # Both enc_C, enc_L >= 0, multiples of 8.
    # Search smallest R_L first (preferred for simplicity)
    candidates = []
    for R_L in range(1, M_leaf + 1):
        for R_C in range(max(n_leaves, R_L), M_center + 1):
            diff = 2 - R_C + R_L
            if diff % 8 != 0:
                continue
            if diff >= 0:
                enc_L = 0; enc_C = diff
            else:
                enc_L = -diff; enc_C = 0
            candidates.append((R_L, R_C, enc_C, enc_L))
    if not candidates:
        return None
    # Pick the simplest: smallest R_L, smallest R_C, smallest encs
    candidates.sort(key=lambda x: (x[0], x[1], x[2] + x[3]))
    R_L, R_C, enc_C, enc_L = candidates[0]
    if True:
            assert enc_C % 8 == 0 and enc_L % 8 == 0
            return {
                "N": N,
                "M_center": M_center,
                "M_leaf": M_leaf,
                "R_C": R_C,
                "R_L": R_L,
                "A_C": M_center - R_C,
                "A_L": M_leaf - R_L,
                "enc_C": enc_C,
                "enc_L": enc_L,
                "rho_C": enc_C + R_C,
                "rho_L": enc_L + R_L,
                "S_C": s_c_int,
                "S_L": s_l_int,
                "edges": edges,
                "M": M,
            }
    return None


def main():
    # Find smallest realizable star witness
    print("Star K_{1,N-1} realizable witnesses (Phase A finding):")
    print("=" * 70)
    smallest = None
    for N in range(3, 50):
        for M_center in range(N - 1, 200):  # M_C >= N-1
            for M_leaf in range(0, 200):
                num = ((N-1)*(N-2)//2) * (1 + 2*M_leaf)
                denom = 4 + 2*M_center + 4*M_leaf
                if denom > 0 and num % denom == 0:
                    s_center = num // denom
                    if s_center == 2 * N:
                        # Check realizability
                        result = realize_star(N, M_center, M_leaf)
                        if result is not None:
                            print(f"  N={N}, M_center={M_center}, M_leaf={M_leaf}: REALIZABLE")
                            for k, v in result.items():
                                print(f"    {k} = {v}")
                            print()
                            if smallest is None:
                                smallest = result
                            break
            else:
                continue
            break
        if smallest is not None and N >= smallest["N"] + 5:
            break

    if smallest is not None:
        print()
        print("=" * 70)
        print(f"SMALLEST realizable star witness: N = {smallest['N']}")
        print(f"  Center: M_C = {smallest['M_center']}, R_C = {smallest['R_C']}, A_C = {smallest['A_C']}")
        print(f"          enc_C = {smallest['enc_C']}, rho_C = {smallest['rho_C']}, S_C = {smallest['S_C']}")
        print(f"  Leaf:   M_L = {smallest['M_leaf']}, R_L = {smallest['R_L']}, A_L = {smallest['A_L']}")
        print(f"          enc_L = {smallest['enc_L']}, rho_L = {smallest['rho_L']}, S_L = {smallest['S_L']}")
        print(f"  Total_S = {smallest['S_C']} + {smallest['N']-1} * {smallest['S_L']} = {smallest['S_C'] + (smallest['N']-1)*smallest['S_L']}, target = {2*smallest['N']}")
    else:
        print("No realizable star witness found.")


if __name__ == "__main__":
    main()
