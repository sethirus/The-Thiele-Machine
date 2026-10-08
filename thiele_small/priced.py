"""The two-counter guest machine over an open property language, with PAY:
minimal/EarnedGeneric.v (module G, parameters prop_eqb and eval) and
minimal/EarnedPriced.v (the same plus PAY, names pr_*).

This is the guest of the priced universal program U_P: UniversalPCodes.v
instantiates it at the universal property language cg_uprop of
CompilerChecker.v, which codes.py mirrors as cg_ueval and UPROP below.

Instructions are those of small.py plus ("PAY",), with properties of the
chosen language. The state is small.State.
"""

from __future__ import annotations

from typing import List, Optional, Sequence

from . import codes
from . import small
from .multi import Lang
from .small import State, CA, CB, FACT_CAP

# CompilerChecker.v: cg_uprop = UBase q | URun r, with cg_uprop_eqb and
# cg_ueval. snap is a printing code used only to compare states.


def _uprop_snap(p):
    """Printing code (kind, parameter): UBase q has q's code (0..2), URun r
    has kind 3 and parameter r."""
    return small.prop_snap(p[1]) if p[0] == "UBase" else (3, p[1])


UPROP = Lang("cg_uprop", lambda p, q: p == q, codes.cg_ueval, _uprop_snap)

# The counter language of EarnedGeneric.v (cprop, ceval, cprop_eqb); the same
# language as EarnedCore.v's prop.
CPROP = Lang("cprop", small.prop_eqb, small.eval_prop, small.prop_snap)


def cost(i) -> int:
    """Coq: G.cost / P.pr_cost: CHECK, COMMIT, CERTIFY and PAY cost 1."""
    return 1 if i[0] in ("CHECK", "COMMIT", "CERTIFY", "PAY") else 0


class Guest:
    """Machine G (priced=False) or machine P = G + PAY (priced=True) over
    a property language."""

    def __init__(self, lang: Lang, priced: bool = True):
        self.lang = lang
        self.priced = priced

    def start(self, a: int, b: int) -> State:
        """Coq: G.start a b = mkst (start_core a b) 0 false."""
        return small.start(a, b)

    def claim(self, k: State, p, c: int):
        """Coq: G.claim."""
        return (p, c, k.ver(c))

    def check_ok(self, k: State, p, c: int) -> bool:
        """Coq: G.check_ok eval k p c."""
        return ((not k.err) and self.lang.eval(p, k.val(c))
                and len(k.facts) < FACT_CAP)

    def commit_ok(self, k: State, p, c: int) -> bool:
        """Coq: G.commit_ok prop_eqb k p c."""
        if k.err:
            return False
        q, cc, vv = self.claim(k, p, c)
        return any(self.lang.eqb(q, fp) and cc == fc and vv == fv
                   for (fp, fc, fv) in k.facts)

    def certify_ok(self, k: State) -> bool:
        """Coq: G.certify_ok."""
        return (not k.err) and k.chan is not None

    def cexec_inplace(self, k: State, i) -> None:
        """Coq: G.cexec / P.pr_cexec, in place."""
        if k.err:
            return
        op = i[0]
        if op == "INC":
            small._write(k, i[1], k.val(i[1]) + 1, k.pc + 1)
        elif op == "DEC":
            c, j = i[1], i[2]
            n = k.val(c)
            if n == 0:
                k.pc += 1
            else:
                small._write(k, c, n - 1, j)
        elif op == "HALT":
            pass
        elif op == "CHECK":
            p, c = i[1], i[2]
            if self.check_ok(k, p, c):
                f = self.claim(k, p, c)
                k.pc += 1
                k.facts.insert(0, f)
            else:
                k.err = True
        elif op == "COMMIT":
            p, c = i[1], i[2]
            if self.commit_ok(k, p, c):
                f = self.claim(k, p, c)
                k.pc += 1
                k.chan = f
            else:
                k.err = True
        elif op == "CERTIFY":
            if self.certify_ok(k):
                k.pc += 1
            else:
                k.err = True
        elif op == "PAY" and self.priced:
            k.pc += 1
        else:
            raise ValueError("unknown instruction %r" % (i,))

    def fires(self, k: State, i) -> bool:
        """Coq: G.fires / P.pr_fires."""
        return i[0] == "CERTIFY" and self.certify_ok(k)

    def _apply(self, t: State, i) -> None:
        fl = self.fires(t, i)
        self.cexec_inplace(t, i)
        t.mu += cost(i)
        t.cert = t.cert or fl

    def exec(self, s: State, i) -> State:
        """Coq: G.exec / P.pr_exec."""
        t = s.copy()
        self._apply(t, i)
        return t

    def run(self, tr: Sequence, s: State) -> State:
        """Coq: G.run / P.pr_run."""
        t = s.copy()
        for i in tr:
            self._apply(t, i)
        return t

    def next_instr(self, P: Sequence, k: State):
        """Coq: G.next_instr / P.pr_next_instr."""
        if k.err:
            return None
        i = small.fetch(P, k.pc)
        if i is not None and i[0] == "HALT":
            return None
        return i

    def halted(self, P: Sequence, k: State) -> bool:
        """Coq: G.halted / P.pr_halted."""
        return self.next_instr(P, k) is None

    def step(self, P: Sequence, s: State) -> State:
        """Coq: G.step / P.pr_step."""
        t = s.copy()
        i = self.next_instr(P, t)
        if i is not None:
            self._apply(t, i)
        return t

    def run_prog(self, n: int, P: Sequence, s: State) -> State:
        """Coq: G.run_prog / P.pr_run_prog."""
        t = s.copy()
        for _ in range(n):
            i = self.next_instr(P, t)
            if i is None:
                break
            self._apply(t, i)
        return t

    def trace_of(self, n: int, P: Sequence, s: State) -> List:
        """Coq: G.trace_of / P.pr_trace_of."""
        t = s.copy()
        out: List = []
        for _ in range(n):
            i = self.next_instr(P, t)
            if i is None:
                break
            out.append(i)
            self._apply(t, i)
        return out

    def snapshot(self, s: State):
        """(pc, ca, cb, va, vb, facts, chan, err, mu, cert); the comparison
        format of small.snapshot with this language's property code."""
        def fs(f):
            if f is None:
                return None
            k, n = self.lang.snap(f[0])
            return (k, n, f[1], f[2])
        return (s.pc, s.ca, s.cb, s.va, s.vb, [fs(f) for f in s.facts],
                fs(s.chan), int(s.err), s.mu, int(s.cert))
