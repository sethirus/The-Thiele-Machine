"""Search for graphs where target is hit at M=0 (all structural masses zero).
At M=0, every distance is 1, every term ratio is 1/4. So total_S = sum_m C(deg(m),2)/4.
Target 2N: sum_m C(deg(m),2) = 8N.

For N=3..10, enumerate degree sequences satisfying:
- Sum d_i = 2|E| (handshaking, even)
- Sum d_i*(d_i - 1) = 16N
- d_i in [0, N-1]
- Graphical (Erdos-Gallai)

If any degree sequence works, try to construct a graph and verify."""

from itertools import product, combinations
import sys

sys.path.insert(0, "/workspaces/The-Thiele-Machine/tools")
from calibrated_witness_search import total_S, density_solution_exists, neighbors_of, triangles_at
from fractions import Fraction


def is_graphical(seq):
    """Erdos-Gallai theorem: sequence d_1 >= d_2 >= ... >= d_n is graphical iff
    sum is even and for every k, sum_{i=1}^{k} d_i <= k(k-1) + sum_{i>k} min(d_i, k)."""
    seq = sorted(seq, reverse=True)
    n = len(seq)
    if sum(seq) % 2 != 0:
        return False
    for k in range(1, n + 1):
        lhs = sum(seq[:k])
        rhs = k * (k - 1) + sum(min(d, k) for d in seq[k:])
        if lhs > rhs:
            return False
    return True


def construct_graph_from_degseq(seq):
    """Havel-Hakimi: greedy construction. Returns edge list or None."""
    n = len(seq)
    nodes = list(range(n))
    deg = list(seq)
    edges = set()
    # Repeatedly: take node with max remaining degree d; connect to next d nodes by degree.
    while max(deg) > 0:
        # Sort by deg desc, breaking ties by id
        order = sorted(range(n), key=lambda i: (-deg[i], i))
        v = order[0]
        d = deg[v]
        if d > sum(1 for u in order[1:] if deg[u] > 0):
            return None
        for u in order[1:1 + d]:
            if deg[u] <= 0:
                return None
            e = tuple(sorted([v, u]))
            if e in edges:
                return None  # multi-edge
            edges.add(e)
            deg[u] -= 1
        deg[v] = 0
    return sorted(edges)


def main():
    print("Searching for graphs with sum_m d_m(d_m - 1) = 16N (M=0 hits target):")
    for N in range(3, 9):
        target_sum = 16 * N
        print(f"  N = {N}: need sum d_i(d_i-1) = {target_sum}, sum d_i even, d_i in [0,{N-1}]")
        found_seqs = []
        # Iterate all length-N sequences with d_i in [0, N-1]
        for seq in product(range(N), repeat=N):
            seq = tuple(sorted(seq, reverse=True))
            if sum(d * (d - 1) for d in seq) != target_sum:
                continue
            if sum(seq) % 2 != 0:
                continue
            if not is_graphical(seq):
                continue
            if seq in found_seqs:
                continue
            found_seqs.append(seq)
        print(f"    Found {len(found_seqs)} graphical degree sequences:")
        for seq in found_seqs[:8]:
            edges = construct_graph_from_degseq(seq)
            if edges is None:
                print(f"      degseq={seq}: Havel-Hakimi failed")
                continue
            ts = total_S(edges, N, [0] * N)
            print(f"      degseq={seq}, edges={edges}, total_S(M=0)={ts}={float(ts):.4f}")
            if ts == 2 * N:
                print(f"        TARGET HIT at M=0!")
                ok, rho = density_solution_exists(edges, N, [0] * N)
                print(f"        density: ok={ok}, rho={rho}")


if __name__ == "__main__":
    main()
