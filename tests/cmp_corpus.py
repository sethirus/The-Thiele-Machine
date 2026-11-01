"""Corpus of source programs for the verified compiler, and a random program
generator for differential fuzzing.

This is test scaffolding. Every corpus entry carries a reference function
written directly in python (math.gcd, a plain ackermann, a plain sort ...),
so an answer is checked against ordinary mathematics and not only against
another implementation of the same language.
"""

from __future__ import annotations

import math
import random
from typing import Callable, Dict, List, Optional, Sequence, Tuple

# ---------------------------------------------------------------------------
# a little syntax sugar
# ---------------------------------------------------------------------------


def V(n):
    return ("v", n)


def add(a, b):
    return ("+", a, b)


def sub(a, b):
    return ("-", a, b)


def Set(x, a):
    return ("set", x, a)


def Seq(*s):
    return ("seq",) + tuple(s)


def If(b, s, t="skip"):
    return ("if", b, s, t)


def While(b, s):
    return ("while", b, s)


def Call(ds, p, args):
    return ("call", list(ds), p, list(args))


def Lt(a, b):
    return ("<", a, b)


def Eq(a, b):
    return ("=", a, b)


def Not(b):
    return ("not", b)


def And(a, b):
    return ("and", a, b)


def Or(a, b):
    return ("or", a, b)


def Proc(np_, body, rets):
    return ("proc", np_, body, list(rets))


def Prog(procs, main):
    return ("prog", list(procs), main)


# ---------------------------------------------------------------------------
# procedures
# ---------------------------------------------------------------------------

# multiplication by repeated addition: (a, b) -> a * b
MUL = Proc(2, Seq(Set(2, 0), While(Lt(0, V(0)), Seq(Set(2, add(V(2), V(1))), Set(0, sub(V(0), 1))))), [V(2)])

# division by repeated subtraction: (a, b) -> (quotient, remainder); b = 0 gives (0, a)
DIVMOD = Proc(
    2,
    Seq(Set(2, 0),
        While(And(Lt(0, V(1)), Not(Lt(V(0), V(1)))), Seq(Set(0, sub(V(0), V(1))), Set(2, add(V(2), 1))))),
    [V(2), V(0)])


def fact_proc(mul_index):
    """n -> n!, calling the multiplication at procedure index mul_index."""
    return Proc(1, Seq(Set(1, 1), While(Lt(0, V(0)), Seq(Call([1], mul_index, [V(1), V(0)]), Set(0, sub(V(0), 1))))),
                [V(1)])


def isprime_proc(mul_index, divmod_index):
    """n -> 1 when n is prime, else 0, by trial division up to the square root."""
    body = Seq(
        If(Lt(V(0), 2), Set(2, 0),
           Seq(Set(2, 1), Set(1, 2), Call([3], mul_index, [V(1), V(1)]),
               While(And(Eq(V(2), 1), Not(Lt(V(0), V(3)))),
                     Seq(Call([4, 5], divmod_index, [V(0), V(1)]),
                         If(Eq(V(5), 0), Set(2, 0),
                            Seq(Set(1, add(V(1), 1)), Call([3], mul_index, [V(1), V(1)])))))))
    )
    return Proc(1, body, [V(2)])


def ack_level(k):
    """Procedure k of a tower: level 0 is n -> n + 1 and level k is
    n -> (level k-1) applied n + 1 times to 1, which is ackermann(k, n)."""
    if k == 0:
        return Proc(1, "skip", [add(V(0), 1)])
    return Proc(1, Seq(Set(1, 1), Set(2, add(V(0), 1)),
                       While(Lt(0, V(2)), Seq(Call([1], k - 1, [V(1)]), Set(2, sub(V(2), 1))))),
                [V(1)])


def ackermann(m, n):
    from functools import lru_cache
    sys_limit = __import__("sys").getrecursionlimit()
    __import__("sys").setrecursionlimit(max(sys_limit, 100000))

    @lru_cache(maxsize=None)
    def a(m_, n_):
        if m_ == 0:
            return n_ + 1
        if n_ == 0:
            return a(m_ - 1, 1)
        return a(m_ - 1, a(m_, n_ - 1))

    return a(m, n)


# ---------------------------------------------------------------------------
# entries: (name, program, nin, out, reference function of the inputs)
# ---------------------------------------------------------------------------

Entry = Tuple[str, tuple, int, int, Callable]


def e_add() -> Entry:
    return "add", Prog([], Set(2, add(V(0), V(1)))), 2, 2, lambda x, y: x + y


def e_mul_loop() -> Entry:
    p = Prog([], Seq(Set(2, 0), While(Lt(0, V(0)), Seq(Set(2, add(V(2), V(1))), Set(0, sub(V(0), 1))))))
    return "mul_loop", p, 2, 2, lambda x, y: x * y


def e_mul_call() -> Entry:
    return "mul_call", Prog([MUL], Call([2], 0, [V(0), V(1)])), 2, 2, lambda x, y: x * y


def e_fact() -> Entry:
    return "fact", Prog([MUL, fact_proc(0)], Call([1], 1, [V(0)])), 1, 1, lambda n: math.factorial(n)


def e_gcd() -> Entry:
    p = Prog([], While(Not(Eq(V(0), V(1))), If(Lt(V(0), V(1)), Set(1, sub(V(1), V(0))), Set(0, sub(V(0), V(1))))))
    return "gcd", p, 2, 0, lambda x, y: math.gcd(x, y)


def _isprime(n):
    if n < 2:
        return 0
    d = 2
    while d * d <= n:
        if n % d == 0:
            return 0
        d += 1
    return 1


def e_prime() -> Entry:
    return "prime", Prog([MUL, DIVMOD, isprime_proc(0, 1)], Call([1], 2, [V(0)])), 1, 1, _isprime


def e_divmod() -> Entry:
    return "divmod", Prog([DIVMOD], Call([2, 3], 0, [V(0), V(1)])), 2, 2, lambda a, b: (a // b) if b else 0


def e_ack(m) -> Entry:
    return ("ack%d" % m, Prog([ack_level(k) for k in range(m + 1)], Call([1], m, [V(0)])), 1, 1,
            lambda n, m=m: ackermann(m, n))


# a sorting network for five inputs, nine comparators (checked below)
NET5 = [(0, 3), (1, 4), (0, 2), (1, 3), (0, 1), (2, 4), (1, 2), (3, 4), (2, 3)]


def _check_network():
    for bits in range(32):
        v = [(bits >> i) & 1 for i in range(5)]
        for i, j in NET5:
            if v[i] > v[j]:
                v[i], v[j] = v[j], v[i]
        assert v == sorted(v)


_check_network()

BASE = 4


def e_sort5() -> Entry:
    """A list of five digits base 4 packed in a number (first element lowest)
    is unpacked with divmod, sorted by a network of compare-exchanges, and
    packed again (smallest lowest)."""
    unpack = []
    for i in range(5):
        unpack += [Call([7, 1 + i], 1, [V(0), BASE]), Set(0, V(7))]
    net = []
    for i, j in NET5:
        net.append(If(Lt(V(1 + j), V(1 + i)), Seq(Set(6, V(1 + i)), Set(1 + i, V(1 + j)), Set(1 + j, V(6)))))

    def x4(e):
        return add(add(e, e), add(e, e))

    pack = Set(8, add(V(1), x4(add(V(2), x4(add(V(3), x4(add(V(4), x4(V(5))))))))))
    p = Prog([MUL, DIVMOD], Seq(*unpack, *net, pack))

    def ref(packed):
        ds = []
        for _ in range(5):
            ds.append(packed % BASE)
            packed //= BASE
        ds.sort()
        return sum(d * BASE ** i for i, d in enumerate(ds))

    return "sort5", p, 1, 8, ref


# the tiny interpreter: a program of four instructions (op, arg) in variables
# 0 .. 7 and the registers A, B in variables 8, 9. Instructions: 0 HALT,
# 1 INC A, 2 INC B, 3 DECA j (when A > 0: subtract 1 and go to j, else go
# on), 4 DECB j, 5 JMP j. An address outside 0 .. 3 halts.
INTERP_NVARS = 15


def e_tiny_interp() -> Entry:
    pc, op, arg, run = 10, 11, 12, 13
    fetch = "skip"
    for i in (3, 2, 1, 0):
        fetch = If(Eq(V(pc), i), Seq(Set(op, V(2 * i)), Set(arg, V(2 * i + 1))), fetch)
    # pc outside 0..3: stop
    fetch = If(Lt(3, V(pc)), Set(op, 0), fetch)
    exec_ = Seq(
        If(Eq(V(op), 0), Set(run, 0)),
        If(Eq(V(op), 1), Seq(Set(8, add(V(8), 1)), Set(pc, add(V(pc), 1)))),
        If(Eq(V(op), 2), Seq(Set(9, add(V(9), 1)), Set(pc, add(V(pc), 1)))),
        If(Eq(V(op), 3), If(Lt(0, V(8)), Seq(Set(8, sub(V(8), 1)), Set(pc, V(arg))), Set(pc, add(V(pc), 1)))),
        If(Eq(V(op), 4), If(Lt(0, V(9)), Seq(Set(9, sub(V(9), 1)), Set(pc, V(arg))), Set(pc, add(V(pc), 1)))),
        If(Eq(V(op), 5), Set(pc, V(arg))),
        If(Lt(5, V(op)), Set(run, 0)),
    )
    p = Prog([], Seq(Set(pc, 0), Set(run, 1), While(Eq(V(run), 1), Seq(fetch, exec_))))

    def ref(*xs):
        prog = [(xs[2 * i], xs[2 * i + 1]) for i in range(4)]
        a, b, pcv = xs[8], xs[9], 0
        for _ in range(100000):
            if not 0 <= pcv <= 3:
                return (a, b)
            o, g = prog[pcv]
            if o == 0 or o > 5:
                return (a, b)
            if o == 1:
                a += 1
                pcv += 1
            elif o == 2:
                b += 1
                pcv += 1
            elif o == 3:
                if a > 0:
                    a -= 1
                    pcv = g
                else:
                    pcv += 1
            elif o == 4:
                if b > 0:
                    b -= 1
                    pcv = g
                else:
                    pcv += 1
            else:
                pcv = g
        return None

    return "tiny_interp", p, 10, 9, ref


# machine programs for the tiny interpreter: (op, arg) x 4
MACHINES = {
    # B += A
    "adder": [(3, 2), (0, 0), (2, 0), (5, 0)],
    # B += 2 * A
    "doubler": [(3, 2), (0, 0), (2, 0), (2, 0)],
    # move A into B, one at a time, counting down (loops through 0..3)
    "mover": [(3, 2), (0, 0), (2, 0), (5, 0)],
    # A := 0 by counting down, then B up once
    "drain": [(3, 0), (2, 0), (0, 0), (0, 0)],
}


def machine_inputs(name, a, b):
    flat = [x for ins in MACHINES[name] for x in ins]
    return flat + [a, b]


# non-halting programs
def nonhalting():
    return [
        ("spin", Prog([], While("true", "skip")), 0, 0),
        ("count_up", Prog([], While(Lt(0, 1), Set(0, add(V(0), 1)))), 1, 0),
        ("after_work", Prog([], Seq(Set(1, add(V(0), 3)), While(Not(Eq(V(0), 5)), Set(1, add(V(1), 1))))), 1, 1),
    ]


def ill_formed():
    """Programs the shape check rejects: recursion, a call to a missing procedure."""
    return [
        ("self_call", Prog([Proc(1, Call([0], 0, [V(0)]), [V(0)])], "skip"), 1, 0),
        ("missing", Prog([], Call([0], 0, [V(0)])), 1, 0),
        ("forward_call", Prog([Proc(1, Call([0], 1, [V(0)]), [V(0)]), Proc(1, "skip", [V(0)])], "skip"), 1, 0),
    ]


# ---------------------------------------------------------------------------
# random programs
# ---------------------------------------------------------------------------


class Gen:
    """Random well-formed programs over variables 0 .. nvars - 1. A loop is a
    countdown: its counter is a variable that the body does not assign, and
    it is decreased at the end of every round, so it ends (unless the
    generator is asked for wild loops, which may not end)."""

    def __init__(self, rng: random.Random, nvars: int = 5, wild: float = 0.0):
        self.rng = rng
        self.nvars = nvars
        self.wild = wild

    def aexp(self, depth: int, ok_vars: Sequence[int]):
        r = self.rng
        if depth <= 0 or r.random() < 0.35:
            if r.random() < 0.5 and ok_vars:
                return V(r.choice(list(ok_vars)))
            return r.randint(0, 4)
        op = r.choice(["+", "-", "+", "-", "v"])
        if op == "v":
            return V(r.choice(list(ok_vars)))
        return (op, self.aexp(depth - 1, ok_vars), self.aexp(depth - 1, ok_vars))

    def bexp(self, depth: int, ok_vars: Sequence[int]):
        r = self.rng
        if depth <= 0 or r.random() < 0.5:
            k = r.choice(["=", "<", "<", "=", "true", "false"])
            if k in ("true", "false"):
                return k
            return (k, self.aexp(1, ok_vars), self.aexp(1, ok_vars))
        k = r.choice(["not", "and", "or"])
        if k == "not":
            return ("not", self.bexp(depth - 1, ok_vars))
        return (k, self.bexp(depth - 1, ok_vars), self.bexp(depth - 1, ok_vars))

    def stmt(self, depth: int, frame: int, nprocs: int, protected: frozenset, loops_left: int, procs_sigs):
        r = self.rng
        free = [v for v in range(frame) if v not in protected]
        allv = list(range(frame))
        choices = ["set", "set", "set", "seq", "seq", "if", "if"]
        if depth > 0 and loops_left > 0:
            choices += ["while", "while", "while"]
        if depth > 0 and nprocs > 0:
            choices += ["call", "call"]
        if depth <= 0:
            choices = ["set", "set", "skip"]
        k = r.choice(choices)
        if k == "skip":
            return "skip"
        if k == "set" and free:
            return Set(r.choice(free), self.aexp(2, allv))
        if k == "seq":
            n = r.randint(2, 3)
            return Seq(*[self.stmt(depth - 1, frame, nprocs, protected, loops_left, procs_sigs) for _ in range(n)])
        if k == "if":
            return If(self.bexp(1, allv), self.stmt(depth - 1, frame, nprocs, protected, loops_left, procs_sigs),
                      self.stmt(depth - 1, frame, nprocs, protected, loops_left, procs_sigs))
        if k == "while":
            wild = r.random() < self.wild
            if wild:
                return While(self.bexp(1, allv), self.stmt(depth - 1, frame, nprocs, protected, loops_left - 1, procs_sigs))
            cands = [v for v in free]
            if not cands:
                return "skip"
            c = r.choice(cands)
            body = self.stmt(depth - 1, frame, nprocs, protected | {c}, loops_left - 1, procs_sigs)
            loop = While(Lt(0, V(c)), Seq(body, Set(c, sub(V(c), 1))))
            if r.random() < 0.5:
                return Seq(Set(c, r.randint(1, 4)), loop)
            return loop
        if k == "call":
            p = r.randrange(nprocs)
            np_, nret = procs_sigs[p]
            args = [self.aexp(1, allv) for _ in range(np_)]
            ds = [r.choice(free) for _ in range(nret)] if free else []
            return Call(ds, p, args)
        return "skip"

    def program(self, nin: int):
        r = self.rng
        procs = []
        sigs = []
        for i in range(r.randint(0, 2)):
            np_ = r.randint(1, 2)
            frame = np_ + r.randint(1, 2)
            body = self.stmt(2, frame, i, frozenset(), 1, sigs)
            nret = r.randint(1, 2)
            rets = [self.aexp(1, list(range(frame))) for _ in range(nret)]
            procs.append(Proc(np_, body, rets))
            sigs.append((np_, nret))
        main = Seq(*[self.stmt(3, self.nvars, len(procs), frozenset(), 2, sigs) for _ in range(r.randint(3, 6))])
        return Prog(procs, main)
