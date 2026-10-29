"""The source language of the verified compiler (coq/kernel/foundation/CmpLang.v)
in python: syntax, a printer for the driver's s-expression input, an
INDEPENDENT interpreter (written from the semantics in the header of
CmpLang.v, not from the extracted code), a well-formedness check, the
variable bounds, and the pure-python virtual machines for the counter machine
and the host machine.

This is test scaffolding, not part of the trusted path. Nothing in it is used
by the compiler or the extracted runner; it only produces inputs and
independent expected values to compare with.

Syntax (python values):
  aexp   int | ("v", n) | ("+", a, b) | ("-", a, b)       ("-" truncated)
  bexp   "true" | "false" | ("=", a, b) | ("<", a, b) | ("not", b)
         | ("and", b, c) | ("or", b, c)
  stmt   "skip" | ("set", x, a) | ("seq", s, ...) | ("if", b, s, t)
         | ("while", b, s) | ("call", [d, ...], p, [a, ...])
  proc   ("proc", np, body, [r, ...])
  prog   ("prog", [proc, ...], main)

Operation counts (CmpLang.v, cmp_ceval): an assignment 1, every test of a
condition 1 (an if once, a loop each time it is tested), a call 1 plus its
body; skip 0.
"""

from __future__ import annotations

import sys
from typing import Dict, List, Optional, Sequence, Tuple

sys.setrecursionlimit(100000)

# ---------------------------------------------------------------------------
# printing for the driver
# ---------------------------------------------------------------------------


def sx(node) -> str:
    if isinstance(node, bool):
        raise TypeError("no booleans as numbers")
    if isinstance(node, int):
        return str(node)
    if isinstance(node, str):
        return node
    if isinstance(node, (list, tuple)):
        return "(" + " ".join(sx(n) for n in node) + ")"
    raise TypeError(node)


def case_text(cid, nin, out, ifuel, hfuel, xs, prog) -> str:
    return "(case %s %d %d %d %d (%s) %s)" % (cid, nin, out, ifuel, hfuel, " ".join(str(x) for x in xs), sx(prog))


def dump_text(nin, out, prog) -> str:
    return "(dump %d %d %s)" % (nin, out, sx(prog))


# ---------------------------------------------------------------------------
# bounds and shape
# ---------------------------------------------------------------------------


def avmax(a) -> int:
    if isinstance(a, int):
        return 0
    if a[0] == "v":
        return a[1] + 1
    return max(avmax(a[1]), avmax(a[2]))


def bvmax(b) -> int:
    if isinstance(b, str):
        return 0
    if b[0] in ("=", "<"):
        return max(avmax(b[1]), avmax(b[2]))
    if b[0] == "not":
        return bvmax(b[1])
    return max(bvmax(b[1]), bvmax(b[2]))


def svmax(s) -> int:
    if isinstance(s, str):
        return 0
    k = s[0]
    if k == "set":
        return max(s[1] + 1, avmax(s[2]))
    if k == "seq":
        return max([svmax(t) for t in s[1:]] + [0])
    if k == "if":
        return max(bvmax(s[1]), svmax(s[2]), svmax(s[3]))
    if k == "while":
        return max(bvmax(s[1]), svmax(s[2]))
    if k == "call":
        return max([d + 1 for d in s[1]] + [avmax(a) for a in s[3]] + [0])
    raise ValueError(s)


def nv0(prog, nin, out) -> int:
    """The number of variables of the main frame the compiler keeps."""
    return max(svmax(prog[2]), nin, out + 1)


def well_formed_stmt(s, n) -> bool:
    if isinstance(s, str):
        return True
    k = s[0]
    if k == "set":
        return True
    if k == "seq":
        return all(well_formed_stmt(t, n) for t in s[1:])
    if k == "if":
        return well_formed_stmt(s[2], n) and well_formed_stmt(s[3], n)
    if k == "while":
        return well_formed_stmt(s[2], n)
    if k == "call":
        return s[2] < n
    raise ValueError(s)


def well_formed(prog) -> bool:
    """Procedure i calls only procedures below i; main calls existing ones."""
    procs = prog[1]
    return all(well_formed_stmt(p[2], i) for i, p in enumerate(procs)) and well_formed_stmt(prog[2], len(procs))


# ---------------------------------------------------------------------------
# the independent interpreter
# ---------------------------------------------------------------------------


class Budget(Exception):
    pass


class _Interp:
    def __init__(self, procs, max_ops, max_value):
        self.procs = procs
        self.ops = 0
        self.max_ops = max_ops
        self.max_value = max_value

    def tick(self, n=1):
        self.ops += n
        if self.ops > self.max_ops:
            raise Budget()

    def aeval(self, e: Dict[int, int], a) -> int:
        if isinstance(a, int):
            return a
        k = a[0]
        if k == "v":
            return e.get(a[1], 0)
        x = self.aeval(e, a[1])
        y = self.aeval(e, a[2])
        if k == "+":
            return x + y
        return max(x - y, 0)

    def beval(self, e, b) -> bool:
        if b == "true":
            return True
        if b == "false":
            return False
        k = b[0]
        if k == "=":
            return self.aeval(e, b[1]) == self.aeval(e, b[2])
        if k == "<":
            return self.aeval(e, b[1]) < self.aeval(e, b[2])
        if k == "not":
            return not self.beval(e, b[1])
        if k == "and":
            return self.beval(e, b[1]) and self.beval(e, b[2])
        return self.beval(e, b[1]) or self.beval(e, b[2])

    def run(self, e: Dict[int, int], s) -> None:
        if s == "skip":
            return
        k = s[0]
        if k == "set":
            v = self.aeval(e, s[2])
            if v > self.max_value:
                raise Budget()
            e[s[1]] = v
            self.tick()
        elif k == "seq":
            for t in s[1:]:
                self.run(e, t)
        elif k == "if":
            c = self.beval(e, s[1])
            self.tick()
            self.run(e, s[2] if c else s[3])
        elif k == "while":
            while True:
                c = self.beval(e, s[1])
                self.tick()
                if not c:
                    break
                self.run(e, s[2])
        elif k == "call":
            _, ds, p, args = s
            np_, body, rets = self.procs[p][1], self.procs[p][2], self.procs[p][3]
            frame: Dict[int, int] = {}
            for i in range(np_):
                frame[i] = self.aeval(e, args[i]) if i < len(args) else 0
            self.tick()
            self.run(frame, body)
            vals = [self.aeval(frame, r) for r in rets]
            # sequential assignment; a longer list is cut to the shorter
            for d, v in zip(ds, vals):
                e[d] = v
        else:
            raise ValueError(s)


def interp(prog, xs: Sequence[int], max_ops: int = 10**7, max_value: int = 10**9):
    """Run the main statement from variables 0, 1, ... = xs. Returns
    (env, ops), or None when the budget of operations (or of the size of a
    value) is exceeded."""
    it = _Interp(prog[1], max_ops, max_value)
    e = {i: x for i, x in enumerate(xs)}
    try:
        it.run(e, prog[2])
    except Budget:
        return None
    return e, it.ops


def size_nodes(node) -> int:
    if isinstance(node, (list, tuple)):
        return 1 + sum(size_nodes(n) for n in node)
    return 1


# ---------------------------------------------------------------------------
# the virtual machines of the dumped programs
# ---------------------------------------------------------------------------


def parse_dump(text: str):
    """The output of (dump ...): (mm program, host program), instructions as
    ("inc", x) or ("dec", x, j)."""
    lines = text.strip().splitlines()
    if lines[0].startswith("wf"):
        return None
    out = []
    i = 0
    for _ in range(2):
        kind, n = lines[i].split()
        n = int(n)
        prog = []
        for l in lines[i + 1:i + 1 + n]:
            w = l.split()
            prog.append(("inc", int(w[1])) if w[0] == "inc" else ("dec", int(w[1]), int(w[2])))
        out.append(prog)
        i += 1 + n
    assert lines[i] == "END"
    return out[0], out[1]


def run_mm(prog, regs: Dict[int, int], max_steps: int) -> Tuple[bool, int, int, Dict[int, int]]:
    """The counter machine of the vendored library: INC x; DEC x j goes on
    when register x is positive (and subtracts 1) and jumps to j when it is 0.
    Starts at address 1; stops when the address leaves 1 .. len. Returns
    (halted, steps, pc, registers)."""
    regs = dict(regs)
    pc = 1
    n = len(prog)
    steps = 0
    while 1 <= pc <= n:
        if steps >= max_steps:
            return False, steps, pc, regs
        ins = prog[pc - 1]
        if ins[0] == "inc":
            regs[ins[1]] = regs.get(ins[1], 0) + 1
            pc += 1
        else:
            v = regs.get(ins[1], 0)
            if v > 0:
                regs[ins[1]] = v - 1
                pc += 1
            else:
                pc = ins[2]
        steps += 1
    return True, steps, pc, regs


def run_host(prog, regs: Dict[int, int], max_steps: int) -> Tuple[bool, int, int, Dict[int, int]]:
    """The host machine of minimal/EarnedMulti.v restricted to INC and DEC:
    DEC r j subtracts 1 and jumps to j when register r is positive, and goes
    on when it is 0."""
    regs = dict(regs)
    pc = 1
    n = len(prog)
    steps = 0
    while 1 <= pc <= n:
        if steps >= max_steps:
            return False, steps, pc, regs
        ins = prog[pc - 1]
        if ins[0] == "inc":
            regs[ins[1]] = regs.get(ins[1], 0) + 1
            pc += 1
        else:
            v = regs.get(ins[1], 0)
            if v > 0:
                regs[ins[1]] = v - 1
                pc = ins[2]
            else:
                pc += 1
        steps += 1
    return True, steps, pc, regs


def load_regs(xs: Sequence[int], nvf: int) -> Dict[int, int]:
    """Inputs in registers 1, 2, ...; as many as nvf of them."""
    return {i + 1: x for i, x in enumerate(xs) if i < nvf and x}
