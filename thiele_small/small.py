"""The small Thiele machine: two counters, versions, a fact table of cap 16,
a commitment channel, a trap latch, a ledger mu and a certified flag.

Mirrors minimal/EarnedCore.v (module E). The same semantics, with a
property language chosen by the caller, is minimal/EarnedGeneric.v
(module G) and, with PAY added, minimal/EarnedPriced.v; the guest machines
of the universal program U_P are those. See priced.py.

Instructions are tuples:
    ("INC", c)            E.INC c
    ("DEC", c, j)         E.DEC c j
    ("HALT",)             E.HALT
    ("CHECK", p, c)       E.CHECK p c
    ("COMMIT", p, c)      E.COMMIT p c
    ("CERTIFY",)          E.CERTIFY
with counters c in {0, 1} for CA, CB, and properties p one of
    ("PZero",), ("PEven",), ("PGe", n)       E.prop

The state object is mutable for speed; every function that the Coq source
defines as a function from state to state returns a fresh state and leaves
its argument alone (exec, step, run, run_prog). The in-place helper
cexec_inplace is the one place the update is performed.
"""

from __future__ import annotations

from typing import List, Optional, Sequence, Tuple

CA, CB = 0, 1

# Coq: Definition fact_cap : nat := 16.   (EarnedCore.v)
FACT_CAP = 16

Prop_ = Tuple
Instr = Tuple
Fact = Tuple  # (prop, ctr, ver): E.mkfact


def prop_eqb(p: Prop_, q: Prop_) -> bool:
    """Coq: E.prop_eqb. Exact equality of properties."""
    return p == q


def eval_prop(p: Prop_, v: int) -> bool:
    """Coq: E.eval. The checker of the property language."""
    k = p[0]
    if k == "PZero":
        return v == 0
    if k == "PEven":
        return v % 2 == 0
    if k == "PGe":
        return p[1] <= v
    raise ValueError("unknown property %r" % (p,))


def cost(i: Instr) -> int:
    """Coq: E.cost. CHECK, COMMIT and CERTIFY cost 1, the rest 0."""
    return 1 if i[0] in ("CHECK", "COMMIT", "CERTIFY") else 0


class State:
    """Coq: E.state = mkst (core_of : core) (mu : nat) (cert : bool), with
    E.core = mkcore ca cb va vb pc facts chan err flattened into fields.

    Fields: ca, cb counters; va, vb versions; pc 1-based program counter;
    facts the fact table, NEWEST FIRST as in Coq's `f :: facts`; chan the
    commitment channel (None or a fact); err the trap latch; mu the ledger;
    cert the certified flag.
    """

    __slots__ = ("ca", "cb", "va", "vb", "pc", "facts", "chan", "err", "mu", "cert")

    def __init__(self, ca=0, cb=0, va=0, vb=0, pc=1, facts=(), chan=None,
                 err=False, mu=0, cert=False):
        self.ca, self.cb, self.va, self.vb, self.pc = ca, cb, va, vb, pc
        self.facts = list(facts)
        self.chan = chan
        self.err = err
        self.mu = mu
        self.cert = cert

    def copy(self) -> "State":
        return State(self.ca, self.cb, self.va, self.vb, self.pc, self.facts,
                     self.chan, self.err, self.mu, self.cert)

    def val(self, c: int) -> int:
        """Coq: E.val."""
        return self.ca if c == CA else self.cb

    def ver(self, c: int) -> int:
        """Coq: E.ver."""
        return self.va if c == CA else self.vb

    def key(self):
        """Full observable state as nested tuples (the comparison format)."""
        return snapshot(self)

    def __eq__(self, other):
        return isinstance(other, State) and self.key() == other.key()

    def __repr__(self):
        return "State%r" % (self.key(),)


def start(a: int, b: int) -> State:
    """Coq: E.start a b = mkst (start_core a b) 0 false, with
    start_core a b = mkcore a b 0 0 1 [] None false."""
    return State(a, b, 0, 0, 1, (), None, False, 0, False)


def claim(k: State, p: Prop_, c: int) -> Fact:
    """Coq: E.claim k p c = mkfact p c (ver k c)."""
    return (p, c, k.ver(c))


def check_ok(k: State, p: Prop_, c: int) -> bool:
    """Coq: E.check_ok: not trapped, p holds of the counter, and the fact
    table has room (length facts < fact_cap)."""
    return (not k.err) and eval_prop(p, k.val(c)) and len(k.facts) < FACT_CAP


def commit_ok(k: State, p: Prop_, c: int) -> bool:
    """Coq: E.commit_ok: not trapped and the table holds the claim at the
    current version of c (existsb (fact_eqb (claim k p c)) facts)."""
    f = claim(k, p, c)
    return (not k.err) and any(f == g for g in k.facts)


def certify_ok(k: State) -> bool:
    """Coq: E.certify_ok: not trapped and the channel names a commitment."""
    return (not k.err) and k.chan is not None


def _write(k: State, c: int, n: int, j: int) -> None:
    """Coq: E.write k c n j. Set a counter, bump its version, pc := j."""
    if c == CA:
        k.ca = n
        k.va += 1
    else:
        k.cb = n
        k.vb += 1
    k.pc = j


def cexec_inplace(k: State, i: Instr) -> None:
    """Coq: E.cexec, applied to k in place. A trapped core is left as it is
    by every instruction."""
    if k.err:
        return
    op = i[0]
    if op == "INC":
        _write(k, i[1], k.val(i[1]) + 1, k.pc + 1)
    elif op == "DEC":
        c, j = i[1], i[2]
        n = k.val(c)
        if n == 0:
            k.pc = k.pc + 1  # E.goto k (S (pc k))
        else:
            _write(k, c, n - 1, j)
    elif op == "HALT":
        pass
    elif op == "CHECK":
        p, c = i[1], i[2]
        if check_ok(k, p, c):
            f = claim(k, p, c)
            k.pc += 1
            k.facts.insert(0, f)  # E.record_fact: f :: facts
        else:
            k.err = True  # E.trap
    elif op == "COMMIT":
        p, c = i[1], i[2]
        if commit_ok(k, p, c):
            f = claim(k, p, c)
            k.pc += 1
            k.chan = f  # E.commit_to
        else:
            k.err = True
    elif op == "CERTIFY":
        if certify_ok(k):
            k.pc += 1
        else:
            k.err = True
    else:
        raise ValueError("unknown instruction %r" % (i,))


def fires(k: State, i: Instr) -> bool:
    """Coq: E.fires. The one event that raises the flag."""
    return i[0] == "CERTIFY" and certify_ok(k)


def exec_(s: State, i: Instr) -> State:
    """Coq: E.exec s i = mkst (cexec (core_of s) i) (mu s + cost i)
    (cert s || fires (core_of s) i). Returns a new state."""
    t = s.copy()
    fl = fires(s, i)
    cexec_inplace(t, i)
    t.mu = s.mu + cost(i)
    t.cert = s.cert or fl
    return t


def run(tr: Sequence[Instr], s: State) -> State:
    """Coq: E.run tr s. Execute a trace instruction by instruction."""
    t = s.copy()
    for i in tr:
        fl = fires(t, i)
        cexec_inplace(t, i)
        t.mu += cost(i)
        t.cert = t.cert or fl
    return t


def total_cost(tr: Sequence[Instr]) -> int:
    """Coq: E.total_cost."""
    return sum(cost(i) for i in tr)


def fetch(P: Sequence, n: int):
    """Coq: E.fetch P n. 1-based; fetch P 0 = None."""
    if n == 0:
        return None
    return P[n - 1] if n - 1 < len(P) else None


def next_instr(P: Sequence[Instr], k: State) -> Optional[Instr]:
    """Coq: E.next_instr. None when trapped, off the program, or at HALT."""
    if k.err:
        return None
    i = fetch(P, k.pc)
    if i is not None and i[0] == "HALT":
        return None
    return i


def halted(P: Sequence[Instr], k: State) -> bool:
    """Coq: E.halted P k := next_instr P k = None."""
    return next_instr(P, k) is None


def _step_inplace(P: Sequence[Instr], t: State) -> None:
    i = next_instr(P, t)
    if i is None:
        return
    fl = fires(t, i)
    cexec_inplace(t, i)
    t.mu += cost(i)
    t.cert = t.cert or fl


def step(P: Sequence[Instr], s: State) -> State:
    """Coq: E.step P s. One step of a stored program; a stopped program
    leaves the state alone."""
    t = s.copy()
    _step_inplace(P, t)
    return t


def run_prog(n: int, P: Sequence[Instr], s: State) -> State:
    """Coq: E.run_prog n P s. n steps of a stored program."""
    t = s.copy()
    for _ in range(n):
        _step_inplace(P, t)
    return t


def trace_of(n: int, P: Sequence[Instr], s: State) -> List[Instr]:
    """Coq: E.trace_of n P s. The instructions a run actually executes."""
    t = s.copy()
    out: List[Instr] = []
    for _ in range(n):
        i = next_instr(P, t)
        if i is None:
            break
        out.append(i)
        _step_inplace(P, t)
    return out


# ---- the two-counter (Minsky) fragment: E.compile ----

def compile_instr(m) -> Instr:
    """Coq: E.compile_instr. MINC c -> INC c, MDEC c j -> DEC c j."""
    return ("INC", m[1]) if m[0] == "MINC" else ("DEC", m[1], m[2])


def compile_(M: Sequence) -> List[Instr]:
    """Coq: E.compile M = map compile_instr M."""
    return [compile_instr(m) for m in M]


def prop_snap(p: Prop_):
    """Printing code of a property, matching the Coq harness' pe:
    PZero (0,0), PEven (1,0), PGe n (2,n). Not a Coq definition; a
    serialisation used only to compare states."""
    k = p[0]
    return (0, 0) if k == "PZero" else (1, 0) if k == "PEven" else (2, p[1])


def fact_snap(f: Optional[Fact]):
    if f is None:
        return None
    k, n = prop_snap(f[0])
    return (k, n, f[1], f[2])


def snapshot(s: State):
    """The full observable state: (pc, ca, cb, va, vb, facts, chan, err, mu,
    cert), facts newest first, booleans as 0/1."""
    return (s.pc, s.ca, s.cb, s.va, s.vb,
            [fact_snap(f) for f in s.facts], fact_snap(s.chan),
            int(s.err), s.mu, int(s.cert))
