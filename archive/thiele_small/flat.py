"""The flat integer form of states, and the token form of programs, used to
talk to the extracted OCaml runner (ocaml/realize_driver.ml).

The layouts are those of the rlz_view_* helpers of
ocaml/RealizeExtract.v, which only flatten a state into a
list of numbers:

  small / priced guest:  pc ca cb va vb err mu cert  CHAN  FACTS
  host:                  pc err mu cert  CHAN  FACTS  nregs vals... vers...
  CHAN  = 0 | 1 k n c v
  FACTS = count (k n c v)*          newest first, c a counter or register

A property is the pair (k, n): kinds 0 PZero, 1 PEven, 2 PGe n, 3 URun n.
The host over PSlot uses (0, 0).
"""

from __future__ import annotations

from typing import List, Sequence

from . import multi, priced, small


def _chan(c) -> List[int]:
    return [0] if c is None else [1, *c]


def _facts(facts) -> List[int]:
    out = [len(facts)]
    for f in facts:
        out.extend(f)
    return out


def flat_small(s: small.State) -> List[int]:
    """The rlz_view_small layout of a small-machine state."""
    snap = small.snapshot(s)
    pc, ca, cb, va, vb, facts, chan, err, mu, cert = snap
    return [pc, ca, cb, va, vb, err, mu, cert, *_chan(chan), *_facts(facts)]


def flat_guest(g: priced.Guest, s: small.State) -> List[int]:
    """The layout of a guest state over any property language."""
    pc, ca, cb, va, vb, facts, chan, err, mu, cert = g.snapshot(s)
    return [pc, ca, cb, va, vb, err, mu, cert, *_chan(chan), *_facts(facts)]


def flat_host(h: multi.Host, s: multi.HState, nregs: int) -> List[int]:
    """The rlz_view_multi / rlz_view_slot / rlz_view_pslot layout."""
    pc, vals, vers, facts, chan, err, mu, cert = h.snapshot(s, nregs)
    return [pc, err, mu, cert, *_chan(chan), *_facts(facts), nregs, *vals, *vers]


# ---- programs as tokens ----------------------------------------------------


def prop_kind(p):
    """(kind, parameter) of a property: counter language, universal language
    (UBase q / URun r) or PSlot."""
    k = p[0]
    if k == "PZero":
        return (0, 0)
    if k == "PEven":
        return (1, 0)
    if k == "PGe":
        return (2, p[1])
    if k == "UBase":
        return prop_kind(p[1])
    if k == "URun":
        return (3, p[1])
    if k == "PSlot":
        return (0, 0)
    raise ValueError(p)


def instr_tokens(i, host: bool) -> List[int]:
    """(op, a, b, c) of an instruction. For a host instruction a is the
    register, for a guest instruction the counter."""
    op = i[0]
    if op == "INC":
        return [0, i[1], 0, 0]
    if op == "DEC":
        return [1, i[1], i[2], 0]
    if op == "HALT":
        return [2, 0, 0, 0]
    if op in ("CHECK", "COMMIT"):
        k, n = prop_kind(i[1])
        return [3 if op == "CHECK" else 4, i[2], k, n]
    if op == "CERTIFY":
        return [5, 0, 0, 0]
    if op == "PAY":
        return [6, 0, 0, 0]
    raise ValueError(i)


def prog_tokens(P: Sequence, host: bool = False) -> List[int]:
    out = [len(P)]
    for i in P:
        out.extend(instr_tokens(i, host))
    return out


def regs_tokens(vs) -> List[int]:
    items = sorted(vs.items())
    out = [len(items)]
    for r, v in items:
        out.extend([r, v])
    return out
