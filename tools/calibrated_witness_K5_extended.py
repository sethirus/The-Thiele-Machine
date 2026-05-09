"""Phase A extended search: K_5 with much larger structural masses,
and asymmetric mass distributions, in case the uniform analysis missed
something."""

from fractions import Fraction
from itertools import product
import sys

sys.path.insert(0, "/workspaces/The-Thiele-Machine/tools")
from calibrated_witness_search import (
    make_graph_complete, total_S, S_m, density_solution_exists,
    triangles_at, neighbors_of,
)


def main():
    n = 5
    edges = make_graph_complete(5)
    target = Fraction(2 * n, 1)

    print(f"K_5 extended search; target sum_m S_m = {target}")
    print(f"Mass-cube exhaustive search up to M_i = 50.")
    print()

    # Bound the asymptote so we can prune
    # Asymptote per (a,b,m) triangle = 1/3 as masses -> infty
    # Total -> 5 * 6 * 1/3 = 10 strictly from below
    found = None
    closest_below = (Fraction(0), None)
    closest_above = (Fraction(10**9), None)

    # 2^5 = much smaller pruned search: try only sorted (M_0 <= M_1 <= ... <= M_4)
    max_M = 50
    count = 0
    for tup in product(range(max_M + 1), repeat=n):
        if not all(tup[i] <= tup[i+1] for i in range(n-1)):
            continue  # WLOG sorted (graph is vertex-transitive)
        M = list(tup)
        ts = total_S(edges, n, M)
        count += 1
        diff = ts - target
        if diff < 0 and diff > closest_below[0] - target:
            closest_below = (ts, M)
        if diff > 0 and ts < closest_above[0]:
            closest_above = (ts, M)
        if ts == target:
            ok, rho = density_solution_exists(edges, n, M)
            print(f"   total_S match at M={M}, density_ok={ok}, rho={rho}")
            if ok:
                found = (M, rho)
                break
    print(f"Examined {count} sorted mass tuples.")
    print(f"Closest below target: total_S = {closest_below[0]} ({float(closest_below[0]):.6f}) at M = {closest_below[1]}")
    print(f"Closest above target: total_S = {closest_above[0]} ({float(closest_above[0]):.6f}) at M = {closest_above[1]}")
    if found:
        print(f"WITNESS FOUND: M = {found[0]}, rho = {found[1]}")
    else:
        print("No witness found in extended K_5 search.")
        print()
        # Confirm asymptote: take M=[k,k,k,k,k] for large k
        print("Asymptotic behavior of total_S on K_5 with uniform mass:")
        for k in [0, 1, 5, 50, 500, 5000]:
            M = [k] * 5
            ts = total_S(edges, n, M)
            print(f"   M=[{k}]^5 -> total_S = {ts} = {float(ts):.10f}; target = {target} = {float(target):.10f}")
        print()
        print("Per-pair contribution under uniform K_5 mass M:")
        print("    d = 1+2M, denom_per_triangle = 1 + 3d = 4 + 6M")
        print("    ratio = d/(4+6M) = (1+2M)/(4+6M)")
        print("    -> 1/3 as M -> infty, never equals target 1/3 + epsilon for any finite M")
        print("    total_S = 5 * 6 * ratio = 30(1+2M)/(4+6M)")
        print("    sup over M = 10 (asymptote, not attained); per the structural-mass analysis,")
        print("    sum_m S_m = 2N = 10 is unattainable for any finite VMState on K_5.")


if __name__ == "__main__":
    main()
