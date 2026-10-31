#!/usr/bin/env python3
"""Independent finite checks for the monograph's worked demonstrations.

These checks evaluate the stated examples; they do not prove the general
theorems or verify a physical implementation.
"""
import argparse
from itertools import product
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def reachable(starts, moves, depth):
    states = set(starts)
    for _ in range(depth):
        states |= {f(s) for s in states for f in moves}
    return states


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
