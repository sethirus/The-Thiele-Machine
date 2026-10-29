#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Devon Thiele
# SPDX-License-Identifier: CC-BY-SA-4.0
"""Count the host steps of the universal program U on a guest, exactly, by
stepping every instruction one at a time except the four unary loops, which
are replaced by their closed forms.

    python3 scripts/count_universal_run.py            # the cases below
    python3 scripts/count_universal_run.py --check    # also check every loop
                                                      # site against plain stepping

U (thiele_small/universal.py, extracted from Coq) reads the guest's program
code one unit at a time, so a guest with the whole chain CHECK, COMMIT,
CERTIFY has a code near 2^106 and a run near 10^33 host steps, which no
machine steps. The steps are still countable. Every instruction of U is
stepped by the host's own step function (thiele_small/multi.py), except at
the four shapes below, where v passes of one loop are replaced by their
effect and their exact step count. The shapes are recognised by structure,
at every address of U where they occur (pc is 1-based, U[pc] the instruction
there), and each rule follows from the host's DEC and INC alone: DEC r j
takes one step, r = 0 goes on to pc+1, otherwise r falls by one, its version
rises by one and pc becomes j; INC r takes one step, r and its version rise
by one, pc becomes pc+1. Neither charges, traps, or touches a fact.

  Z   U[pc] = DEC x pc                      self loop
      x = v:  v+1 steps; x = 0; pc+1
  M   U[pc] = DEC x (pc-1), U[pc-1] = INC y, y != x
      x = v:  2v+1 steps; x = 0, y += v; pc+1
  M2  U[pc] = DEC x (pc-2), U[pc-2] = INC y, U[pc-1] = INC z, y, z != x
      x = v:  3v+1 steps; x = 0, y += v, z += v; pc+1
  H   U[pc] = DEC a (pc+3), U[pc+3] = DEC a (pc-1), U[pc-1] = INC x, x != a
      a = v, k = v // 2:  3k steps; a -= 2k, x += k; pc unchanged, and the
      remaining 0 or 1 in a is stepped one at a time

Versions rise by the number of writes in every case. check_loops() steps each
shape at every site in U, from random other register values, for every v up
to a bound, and compares the whole host state and the step count with the
closed form. The counts of the three guests that the Coq-extracted driver
steps one at a time (scripts/realize_universal_runs.py) are reproduced to the
step, and every run is checked against the guest machine the way that runner
checks it: the host stops when the guest stops, each visit of the loop head
shows the guest after that many steps, and the stop shows the guest's
counters, ledger, flag, trap latch and number of facts.
"""
from __future__ import annotations

import argparse
import random
import sys
import time
from collections import Counter
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

from thiele_small import codes, multi, small, universal  # noqa: E402

U = universal.U
HOST = universal.HOST
RA, RB, GPC = universal.RA, universal.RB, universal.GPC
Z = ("PZero",)

# name -> (guest program, start A, start B)
CASES = {
    "count A down from 2": ([("DEC", 0, 1), ("HALT",)], 2, 0),
    "one passing CHECK": ([("CHECK", Z, 0)], 0, 0),
    "one failing CHECK": ([("CHECK", Z, 0)], 1, 0),
    "CHECK, COMMIT, CERTIFY from (0,0)": ([("CHECK", Z, 0), ("COMMIT", Z, 0), ("CERTIFY",)], 0, 0),
    "CHECK, COMMIT, CERTIFY from (5,0)": ([("CHECK", Z, 0), ("COMMIT", Z, 0), ("CERTIFY",)], 5, 0),
}


def instr(pc):
    """U at 1-based address pc, or None."""
    return U[pc - 1] if 1 <= pc <= len(U) else None


def classify(pc):
    """The loop shape at pc, or None."""
    i = instr(pc)
    if i is None or i[0] != "DEC":
        return None
    x, j = i[1], i[2]
    if j == pc:
        return ("Z", x)
    if j == pc - 1:
        p = instr(pc - 1)
        if p is not None and p[0] == "INC" and p[1] != x:
            return ("M", x, p[1])
    if j == pc - 2:
        p, q = instr(pc - 2), instr(pc - 1)
        if (p is not None and q is not None and p[0] == "INC" and q[0] == "INC"
                and p[1] != x and q[1] != x):
            return ("M2", x, p[1], q[1])
    if j == pc + 3:
        d, p = instr(pc + 3), instr(pc - 1)
        if (d is not None and d[0] == "DEC" and d[1] == x and d[2] == pc - 1
                and p is not None and p[0] == "INC" and p[1] != x):
            return ("H", x, p[1])
    return None


SHAPES = {pc: s for pc in range(1, len(U) + 1) if (s := classify(pc)) is not None}


def fast_forward(t, shape):
    """Apply the closed form of shape to host state t in place; return the
    number of primitive steps it stands for (0 if nothing applies)."""
    kind = shape[0]
    vals, vers = t.vals, t.vers

    def add(r, n):
        vals[r] = vals.get(r, 0) + n
        vers[r] = vers.get(r, 0) + n

    if kind == "Z":
        x = shape[1]
        v = vals.get(x, 0)
        vals[x] = 0
        vers[x] = vers.get(x, 0) + v
        t.pc += 1
        return v + 1
    if kind == "M":
        x, y = shape[1], shape[2]
        v = vals.get(x, 0)
        vals[x] = 0
        vers[x] = vers.get(x, 0) + v
        add(y, v)
        t.pc += 1
        return 2 * v + 1
    if kind == "M2":
        x, y, z = shape[1], shape[2], shape[3]
        v = vals.get(x, 0)
        vals[x] = 0
        vers[x] = vers.get(x, 0) + v
        add(y, v)
        add(z, v)
        t.pc += 1
        return 3 * v + 1
    if kind == "H":
        a, x = shape[1], shape[2]
        v = vals.get(a, 0)
        k = v // 2
        if k == 0:
            return 0
        vals[a] = v - 2 * k
        vers[a] = vers.get(a, 0) + 2 * k
        add(x, k)
        return 3 * k
    raise ValueError(shape)


def snap(t):
    return (t.vals.get(RA, 0), t.vals.get(RB, 0), t.vals.get(GPC, 0), t.mu, int(t.cert), int(t.err))


def run_plain(t, heads=None):
    """Step U one instruction at a time from host state t until it stops."""
    n = 0
    step = HOST._step_inplace
    while True:
        if heads is not None and t.pc == 1 and not t.err:
            heads.append(snap(t))
        if not step(U, t):
            return n
        n += 1


def run_counted(t, heads=None):
    """As run_plain, with the four loop shapes replaced by their closed forms.
    Returns the exact primitive step count."""
    n = 0
    step = HOST._step_inplace
    while True:
        if heads is not None and t.pc == 1 and not t.err:
            heads.append(snap(t))
        s = SHAPES.get(t.pc)
        if s is not None and not t.err:
            if s[0] == "Z" and t.pc == 1 and heads is not None:
                heads.extend([snap(t)] * t.vals.get(s[1], 0))
            k = fast_forward(t, s)
            if k:
                n += k
                continue
        if not step(U, t):
            return n
        n += 1


def final(t):
    return {"pc": t.pc, "RA": t.vals.get(RA, 0), "RB": t.vals.get(RB, 0),
            "ledger": t.mu, "cert": bool(t.cert), "trap": bool(t.err), "facts": len(t.facts)}


def full_state(t):
    return (t.pc, {k: v for k, v in t.vals.items() if v}, {k: v for k, v in t.vers.items() if v},
            list(t.facts), t.chan, t.err, t.mu, t.cert)


def guest_states(P, x, y, cap=1000):
    s = small.start(x, y)
    out = [(s.ca, s.cb, s.pc, s.mu, int(s.cert), int(s.err))]
    while not small.halted(P, s) and len(out) < cap:
        s = small.step(P, s)
        out.append((s.ca, s.cb, s.pc, s.mu, int(s.cert), int(s.err)))
    return out


def check_against_guest(P, x, y, heads, fin):
    """The runner's checks. Returns a list of problems, empty when all hold."""
    gs = guest_states(P, x, y)
    trapped = gs[-1][5] == 1
    want_heads = len(gs) - 1 if trapped else len(gs)
    problems = []
    if len(heads) != want_heads:
        problems.append("head visits %d, guest steps %d" % (len(heads), want_heads))
    for k, (h, g) in enumerate(zip(heads, gs)):
        if h != g:
            problems.append("visit %d shows %r, guest %r" % (k, h, g))
            break
    g = gs[-1]
    got = (fin["RA"], fin["RB"], fin["ledger"], int(fin["cert"]), int(fin["trap"]))
    want = (g[0], g[1], g[3], g[4], g[5])
    if got != want:
        problems.append("stop shows %r, guest %r" % (got, want))
    gfacts = len(small.run_prog(len(gs), P, small.start(x, y)).facts)
    if fin["facts"] != gfacts:
        problems.append("facts %d, guest %d" % (fin["facts"], gfacts))
    return problems


def count(P, x, y):
    """Count U on guest P from (x, y). Returns (steps, final state, head visits,
    problems against the guest machine)."""
    t = universal.hload(P, x, y)
    heads = []
    n = run_counted(t, heads)
    fin = final(t)
    return n, fin, len(heads), check_against_guest(P, x, y, heads, fin)


def check_loops(vmax=40, seed=1):
    """Every loop site in U, every v in 0..vmax, from random other register
    values: plain stepping through the shape must give the same whole state
    and the same step count as the closed form. Returns the number of sites."""
    rnd = random.Random(seed)
    for pc, s in sorted(SHAPES.items()):
        kind = s[0]
        region = {"Z": {pc}, "M": {pc - 1, pc}, "M2": {pc - 2, pc - 1, pc}, "H": {pc - 1, pc, pc + 3}}[kind]
        for v in range(vmax + 1):
            vals = {r: rnd.randrange(0, 7) for r in range(0, 96)}
            vers = {r: rnd.randrange(0, 7) for r in range(0, 96)}
            vals[s[1]] = v
            t0 = multi.HState(vals, vers, pc)
            a = t0.copy()
            n = 0
            if kind == "H":
                for _ in range(3 * (v // 2)):
                    assert HOST._step_inplace(U, a)
                    n += 1
                assert a.pc == pc
            else:
                while a.pc in region:
                    assert HOST._step_inplace(U, a)
                    n += 1
            b = t0.copy()
            m = fast_forward(b, s)
            if full_state(a) != full_state(b) or n != m:
                raise AssertionError("shape %r at %d, v=%d: stepped %d, counted %d" % (s, pc, v, n, m))
    return len(SHAPES)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    ap.add_argument("--check", action="store_true", help="check every loop site against plain stepping")
    ap.add_argument("--vmax", type=int, default=40)
    a = ap.parse_args()
    if a.check:
        n = check_loops(a.vmax)
        print("%d loop sites in U (%s): closed forms agree with stepping for v up to %d" % (
            n, ", ".join("%s %d" % kv for kv in sorted(Counter(s[0] for s in SHAPES.values()).items())), a.vmax))
    for name, (P, x, y) in CASES.items():
        t0 = time.time()
        n, fin, heads, problems = count(P, x, y)
        print("%-36s code 2^%-3d  %s host steps  stops at line %d  ledger %d  flag %s  trap %s  %.3fs  %s" % (
            name, codes.prog_code(P).bit_length() - 1, format(n, ","), fin["pc"], fin["ledger"],
            "up" if fin["cert"] else "down", "up" if fin["trap"] else "down", time.time() - t0,
            "guest agrees" if not problems else "; ".join(problems)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
