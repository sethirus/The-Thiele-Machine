#!/usr/bin/env python3
"""Independent finite checks for the monograph's worked demonstrations.

These checks evaluate the stated examples; they do not prove the general
theorems or verify a physical implementation. No floating-point matrix tests
are used for the rational CHSH example.
"""
import argparse
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from thiele_small.small import start, exec_, CA


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def reachable(starts, moves, depth):
    states = set(starts)
    for _ in range(depth):
        states |= {f(s) for s in states for f in moves}
    return states


def determinant(a):
    """Exact elimination with row swaps, independent of Schur cascade code."""
    a = [[Q(x) for x in row] for row in a]
    result = Q(1)
    for k in range(len(a)):
        pivot = next((j for j in range(k, len(a)) if a[j][k]), None)
        if pivot is None:
            return Q(0)
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            result = -result
        value = a[k][k]
        result *= value
        for j in range(k+1, len(a)):
            factor = a[j][k]/value
            for i in range(k+1, len(a)):
                a[j][i] -= factor*a[k][i]
    return result


def check():
    checks = []
    strips = ['1'*n+'0'*(8-n) for n in range(9)]
    successors = strips[1:]+strips[-1:]
    require(len(set(strips)) == 9 and successors[7] == successors[8], 'prefix-strip collision')
    require(len(set(successors)) == 8, 'only the stated prefix collision')
    checks.append({'example': 'eight-box prefix strip', 'states': 9, 'unrestricted_bit_states': 256})

    for t in range(1, 9):
        end = ('end', 0)
        carrier = {('a', i) for i in range(t)} | {('b', i) for i in range(t+1)} | {end}
        def f(s):
            return (('a', s[1]+1) if s[1]+1 < t else end) if s[0] == 'a' else s
        def g(s):
            return (('b', s[1]+1) if s[1]+1 < t+1 else end) if s[0] == 'b' else s
        seeds = {('a', 0), ('b', 0), ('b', 1)}
        before = reachable(seeds, (f, g), t-1)
        require(all(f(g(s)) == g(f(s)) for s in carrier), 'finite arms commute')
        require(all(len({h(s) for s in before}) == len(before) for h in (f, g)), 'horizon injectivity')
        require(reachable(seeds, (f, g), t) == carrier and len(carrier) == 2*t+2, 'finite arms count')
    blank = (-1, -1)
    f = lambda s: s if s == blank else (s[0]+1, s[1])
    g = lambda s: s if s == blank else (s[0], s[1]+1)
    for t in range(9):
        r = reachable({blank, (0, 0), (1, 0), (0, 1)}, (f, g), t)
        triangle = {(i, j) for i in range(t+2) for j in range(t+2-i)} | {blank}
        require(r == triangle and len(r) == 1+(t+2)*(t+3)//2, 'grid triangle count')
        require(all(f(g(s)) == g(f(s)) for s in r), 'grid commutes')
        require(all(len({h(s) for s in r}) == len(r) for h in (f, g)), 'grid shifts injective')
    checks.append({'example': 'two levers', 'finite_arm_horizons': [1, 8], 'grid_horizons': [0, 8]})

    states = set(product((0, 1), repeat=2))
    measure = lambda s: (s[0], s[0]^s[1])
    wipe = lambda s: (s[0], 0)
    require(len({measure(s) for s in states}) == 4 and all(measure(measure(s)) == s for s in states), 'reversible measurement')
    require(len({wipe(s) for s in states}) == 2, 'wipe full-domain collision')
    require(len({wipe(s) for s in {(0, 0), (1, 1)}}) == 2, 'wipe preserves matched-pair distinction')
    checks.append({'example': 'four-state demon', 'all_states': 4, 'wipe_images': 2, 'matched_pair_images': 2})

    program = [('CHECK', ('PGe', 1), CA), ('COMMIT', ('PGe', 1), CA), ('DEC', CA, 4), ('CERTIFY',)]
    s = start(1, 0)
    rows = []
    for i in program:
        s = exec_(s, i)
        rows.append({'instruction': i, 'value': s.ca, 'edition': s.va, 'flag': s.cert, 'ledger': s.mu})
    require(s.ca == 0 and s.va == 1 and s.cert and not s.err and s.mu == 3, 'native historical certification')
    require(s.chan == (('PGe', 1), CA, 0), 'historical channel edition')
    checks.append({'example': 'actual native historical channel', 'trace': rows})

    require((2*6+5)*2**1*3**2 == 306, 'input packing')
    require(306*2 == 612 and 612//3 == 204 and 204//(2**2*3) == 17, 'packed counter trace')
    require((17-5)//6 == 2, 'decoded input')
    checks.append({'example': 'Rice packed input', 'trace': [306, 612, 204, 17, 2]})

    scores = [a*b+a*d+c*b-c*d for a, c, b, d in product((-1, 1), repeat=4)]
    require(set(scores) == {-2, 2}, 'sixteen local CHSH plans')
    e = [Q(3, 5), Q(3, 5), Q(3, 5), Q(-3, 5)]
    require(e[0]+e[1]+e[2]-e[3] == Q(12, 5), 'worked CHSH score')
    require(5**4-3**2*5**2-3**2*5**2 == 175, 'integer allowances')
    require(3*3*5*5+3*(-3)*5*5 == 0, 'integer cross term')
    # Assemble the displayed nine-by-nine matrix, eliminate its leading I_3,
    # then perform the two fraction-free steps on the six-by-six residual.
    a,b,c,d = e
    z = Q(0);o = Q(1);gamma = Q(-1, 2)
    matrix = [
        [o,z,z,z,z,a,b,c,d], [z,o,z,a,b,z,z,z,z], [z,z,o,c,d,z,z,z,z],
        [z,a,c,o,z,z,z,z,z], [z,b,d,z,o,z,z,z,z],
        [a,z,z,z,z,o,z,z,gamma], [b,z,z,z,z,z,o,-gamma,z],
        [c,z,z,z,z,z,-gamma,o,z], [d,z,z,z,z,gamma,z,z,o]]
    residual = [[matrix[i][j]-sum(matrix[i][k]*matrix[k][j] for k in range(3))
                 for j in range(3,9)] for i in range(3,9)]
    def schur(a):
        return [[a[0][0]*a[i][j]-a[0][i]*a[0][j] for j in range(1,len(a))]
                for i in range(1,len(a))]
    first = schur(residual); second = schur(first)
    target = [[32,-18,-18,-7],[-18,32,7,18],[-18,7,32,18],[-7,18,18,32]]
    require(residual[0][0] == Q(7,25) and first[0][0] == Q(49,625), 'first pivots')
    require(second == [[Q(343,781250)*x for x in row] for row in target], 'worked Schur scale and matrix')
    minors = [determinant([row[:n] for row in target[:n]]) for n in range(1,5)]
    require(minors == [32,700,15000,140625], 'worked leading minors')
    zero_block = [[Q(i == j)-e[i]*e[j] for j in range(4)] for i in range(4)]
    require(determinant([row[:3] for row in zero_block[:3]]) == Q(-1250,25**3), 'zero-moment failure')
    checks.append({'example': 'CHSH local plans and exact cascade', 'plans': 16, 'leading_minors': list(map(int,minors)), 'zero_moment_third_minor': '-2/25'})

    leaf = lambda n: ('leaf',n)
    node = lambda l,r: ('node',l,r)
    a = node(leaf(0),leaf(1)); b = node(leaf(2),leaf(3)); c = node(leaf(4),leaf(5))
    right = node(c,leaf(6)); root = node(node(a,b),right)
    rebuilt = node(node(a,node(leaf(2),leaf(3))),right)
    require(rebuilt == root and node(node(a,node(leaf(3),leaf(2))),right) != root, 'ordered Merkle path')
    checks.append({'example': 'seven-leaf symbolic Merkle inclusion', 'leaf': 3, 'siblings': ['d2','a','R']})
    return checks


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = {'status': 'passed', 'scope': 'finite examples only; no general or physical theorem inferred', 'checks': check()}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(f"PASS: {len(result['checks'])} worked-example groups")
