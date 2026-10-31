"""Case generators and Coq renderers for the differential tests.

A case is data (program, start, steps). Each machine has
  * a Python evaluator that returns the list of per-step snapshots, using
    thiele_small;
  * a Coq renderer: a `Compute` of the same list of snapshots, written with
    the definitions of minimal/ (or the rlz_ entry points) and test-only
    wrappers that flatten a state into nested tuples.
The two lists are compared state by state.

Everything random is seeded; the exhaustive sets are listed in
SMALL_EXHAUSTIVE etc. below.
"""

from __future__ import annotations

import itertools
import random
from typing import Dict, List, Sequence, Tuple

from thiele_small import small, multi, priced, codes

# ---------------------------------------------------------------------------
# Coq text for programs
# ---------------------------------------------------------------------------


def coq_nat(n: int) -> str:
    return str(n)


def e_prop(p) -> str:
    k = p[0]
    return "E.PZero" if k == "PZero" else "E.PEven" if k == "PEven" else "(E.PGe %d)" % p[1]


def g_prop(p) -> str:
    k = p[0]
    return "G.PZero" if k == "PZero" else "G.PEven" if k == "PEven" else "(G.PGe %d)" % p[1]


def e_ctr(c: int) -> str:
    return "E.CA" if c == 0 else "E.CB"


def g_ctr(c: int) -> str:
    return "G.CA" if c == 0 else "G.CB"


def small_instr(i) -> str:
    op = i[0]
    if op == "INC":
        return "E.INC %s" % e_ctr(i[1])
    if op == "DEC":
        return "E.DEC %s %d" % (e_ctr(i[1]), i[2])
    if op == "HALT":
        return "E.HALT"
    if op == "CHECK":
        return "E.CHECK %s %s" % (e_prop(i[1]), e_ctr(i[2]))
    if op == "COMMIT":
        return "E.COMMIT %s %s" % (e_prop(i[1]), e_ctr(i[2]))
    if op == "CERTIFY":
        return "E.CERTIFY"
    raise ValueError(i)


def gen_instr(i, ns: str) -> str:
    """Instruction of EarnedGeneric (ns = 'G') or EarnedPriced (ns = 'PG'):
    constructors G.INC / PG.INC with cprop properties."""
    op = i[0]
    if op == "INC":
        return "%s.INC %s" % (ns, g_ctr(i[1]))
    if op == "DEC":
        return "%s.DEC %s %d" % (ns, g_ctr(i[1]), i[2])
    if op == "HALT":
        return "%s.HALT" % ns
    if op == "CHECK":
        return "%s.CHECK %s %s" % (ns, g_prop(i[1]), g_ctr(i[2]))
    if op == "COMMIT":
        return "%s.COMMIT %s %s" % (ns, g_prop(i[1]), g_ctr(i[2]))
    if op == "CERTIFY":
        return "%s.CERTIFY" % ns
    if op == "PAY":
        return "%s.PAY" % ns
    raise ValueError(i)


def host_instr(i, ns: str, slot: str = "") -> str:
    """Host instruction of EarnedMulti (ns = 'M') or EarnedMultiPriced
    (ns = 'PM'). Properties: E.prop, or PSlot when slot is its Coq name."""
    op = i[0]
    if op == "INC":
        return "%s.INC %d" % (ns, i[1])
    if op == "DEC":
        return "%s.DEC %d %d" % (ns, i[1], i[2])
    if op == "HALT":
        return "%s.HALT" % ns
    if op == "CHECK":
        return "%s.CHECK %s %d" % (ns, slot or e_prop(i[1]), i[2])
    if op == "COMMIT":
        return "%s.COMMIT %s %d" % (ns, slot or e_prop(i[1]), i[2])
    if op == "CERTIFY":
        return "%s.CERTIFY" % ns
    if op == "PAY":
        return "%s.PAY" % ns
    raise ValueError(i)


def coq_list(items: Sequence[str]) -> str:
    return "[" + "; ".join(items) + "]"


# ---------------------------------------------------------------------------
# normalisation of Coq results
# ---------------------------------------------------------------------------


def norm(v):
    """Make a parsed Coq value comparable with a Python snapshot."""
    from realize_harness import Con
    if isinstance(v, Con):
        if v.name == "None" and not v.args:
            return None
        if v.name == "Some" and len(v.args) == 1:
            return norm(v.args[0])
        raise ValueError("unexpected constructor %r" % (v,))
    if isinstance(v, bool):
        return int(v)
    if isinstance(v, tuple):
        return tuple(norm(x) for x in v)
    if isinstance(v, list):
        return [norm(x) for x in v]
    return v


def pynorm(v):
    if isinstance(v, (tuple, list)):
        t = [pynorm(x) for x in v]
        return tuple(t) if isinstance(v, tuple) else t
    return v


# ---------------------------------------------------------------------------
# Python evaluators: lists of per-step snapshots
# ---------------------------------------------------------------------------


def py_small(P, a, b, n):
    s = small.start(a, b)
    out = [small.snapshot(s)]
    for _ in range(n):
        s = small.step(P, s)
        out.append(small.snapshot(s))
    return out


def py_guest(machine: priced.Guest, P, a, b, n):
    s = machine.start(a, b)
    out = [machine.snapshot(s)]
    for _ in range(n):
        s = machine.step(P, s)
        out.append(machine.snapshot(s))
    return out


def py_host(host: multi.Host, P, vs: Dict[int, int], n, nregs):
    s = host.start(vs)
    out = [host.snapshot(s, nregs)]
    for _ in range(n):
        s = host.step(P, s)
        out.append(host.snapshot(s, nregs))
    return out


# ---------------------------------------------------------------------------
# Coq prelude and per-case terms
# ---------------------------------------------------------------------------

PRELUDE_MIN = r"""
From Coq Require Import List Arith Bool.
Import ListNotations.
Require Minimal.EarnedCore Minimal.EarnedGeneric Minimal.EarnedMulti
  Minimal.EarnedMultiPriced Minimal.EarnedPriced.
Module E := Minimal.EarnedCore.
Module G := Minimal.EarnedGeneric.
Module PG := Minimal.EarnedPriced.
Module M := Minimal.EarnedMulti.
Module PM := Minimal.EarnedMultiPriced.
Set Printing Width 100000000.
Set Printing Depth 100000000.

Definition b2n (b : bool) : nat := if b then 1 else 0.
Definition pe (p : E.prop) : nat * nat :=
  match p with E.PZero => (0, 0) | E.PEven => (1, 0) | E.PGe n => (2, n) end.
Definition pg (p : G.cprop) : nat * nat :=
  match p with G.PZero => (0, 0) | G.PEven => (1, 0) | G.PGe n => (2, n) end.
Definition ce (c : E.ctr) : nat := match c with E.CA => 0 | E.CB => 1 end.
Definition cg (c : G.ctr) : nat := match c with G.CA => 0 | G.CB => 1 end.

(* small machine *)
Definition ef (f : E.fact) := (fst (pe (E.f_prop f)), snd (pe (E.f_prop f)), ce (E.f_ctr f), E.f_ver f).
Definition snapS (s : E.state) :=
  let k := E.core_of s in
  (E.pc k, E.ca k, E.cb k, E.va k, E.vb k, map ef (E.facts k),
   option_map ef (E.chan k), b2n (E.err k), E.mu s, b2n (E.cert s)).
Fixpoint trS (n : nat) (P : list E.instr) (s : E.state) :=
  match n with 0 => [snapS s] | S m => snapS s :: trS m P (E.step P s) end.

(* generic / priced guest over cprop *)
Definition gf (f : @G.fact G.cprop) := (fst (pg (G.f_prop f)), snd (pg (G.f_prop f)), cg (G.f_ctr f), G.f_ver f).
Definition snapG (s : @G.state G.cprop) :=
  let k := G.core_of s in
  (G.pc k, G.ca k, G.cb k, G.va k, G.vb k, map gf (G.facts k),
   option_map gf (G.chan k), b2n (G.err k), G.mu s, b2n (G.cert s)).
Fixpoint trG (n : nat) (P : list (@G.instr G.cprop)) (s : @G.state G.cprop) :=
  match n with 0 => [snapG s]
  | S m => snapG s :: trG m P (G.step G.cprop_eqb G.ceval P s) end.
Fixpoint trPG (n : nat) (P : list (@PG.pr_instr G.cprop)) (s : @G.state G.cprop) :=
  match n with 0 => [snapG s]
  | S m => snapG s :: trPG m P (PG.pr_step G.cprop_eqb G.ceval P s) end.

(* multi-register host over E.prop *)
Definition mf (f : @M.fact E.prop) := (fst (pe (M.f_prop f)), snd (pe (M.f_prop f)), M.f_reg f, M.f_ver f).
Definition snapM (nr : nat) (s : @M.state E.prop) :=
  let k := M.core_of s in
  (M.pc k, map (M.vals k) (seq 0 nr), map (M.vers k) (seq 0 nr), map mf (M.facts k),
   option_map mf (M.chan k), b2n (M.err k), M.mu s, b2n (M.cert s)).
Fixpoint trM (nr n : nat) (P : list (@M.instr E.prop)) (s : @M.state E.prop) :=
  match n with 0 => [snapM nr s]
  | S m => snapM nr s :: trM nr m P (M.step E.prop_eqb E.eval P s) end.

Definition pmf (f : @PM.pu_fact E.prop) := (fst (pe (PM.f_prop f)), snd (pe (PM.f_prop f)), PM.f_reg f, PM.f_ver f).
Definition snapPM (nr : nat) (s : @PM.pu_state E.prop) :=
  let k := PM.core_of s in
  (PM.pc k, map (PM.vals k) (seq 0 nr), map (PM.vers k) (seq 0 nr), map pmf (PM.facts k),
   option_map pmf (PM.chan k), b2n (PM.err k), PM.mu s, b2n (PM.cert s)).
Fixpoint trPM (nr n : nat) (P : list (@PM.pu_instr E.prop)) (s : @PM.pu_state E.prop) :=
  match n with 0 => [snapPM nr s]
  | S m => snapPM nr s :: trPM nr m P (PM.pu_step E.prop_eqb E.eval P s) end.

Definition regs (l : list nat) : nat -> nat := fun r => nth r l 0.
"""



def r_small(P, a, b, n) -> str:
    return "Compute (trS %d %s (E.start %d %d))." % (n, coq_list([small_instr(i) for i in P]), a, b)


def r_gen(P, a, b, n, priced_: bool) -> str:
    ns = "PG" if priced_ else "G"
    fn = "trPG" if priced_ else "trG"
    return "Compute (%s %d %s (@G.start G.cprop %d %d))." % (
        fn, n, coq_list([gen_instr(i, ns) for i in P]), a, b)


def r_multi(P, vs: Dict[int, int], n, nr, priced_: bool) -> str:
    ns = "PM" if priced_ else "M"
    fn = "trPM" if priced_ else "trM"
    start = "@PM.pu_start E.prop" if priced_ else "@M.start E.prop"
    regl = coq_list([str(vs.get(r, 0)) for r in range(max(vs) + 1 if vs else 0)])
    return "Compute (%s %d %d %s (%s (regs %s)))." % (
        fn, nr, n, coq_list([host_instr(i, ns) for i in P]), start, regl)


# ---------------------------------------------------------------------------
# case sets
# ---------------------------------------------------------------------------

PROPS = [("PZero",), ("PEven",), ("PGe", 1), ("PGe", 2)]


def small_alphabet(L: int):
    al = []
    for c in (0, 1):
        al.append(("INC", c))
    for c in (0, 1):
        for j in range(1, L + 2):
            al.append(("DEC", c, j))
    al.append(("HALT",))
    for p in PROPS:
        for c in (0, 1):
            al.append(("CHECK", p, c))
    for p in PROPS:
        for c in (0, 1):
            al.append(("COMMIT", p, c))
    al.append(("CERTIFY",))
    return al


SMALL_REDUCED = [("INC", 0), ("DEC", 0, 1), ("DEC", 1, 2), ("CHECK", ("PZero",), 0),
                 ("CHECK", ("PGe", 1), 1), ("COMMIT", ("PZero",), 0),
                 ("COMMIT", ("PGe", 1), 1), ("CERTIFY",), ("HALT",)]

SMALL_STARTS = [(0, 0), (1, 0), (0, 1), (2, 3)]


def small_exhaustive():
    """Every program of length 1 or 2 over the 26-instruction alphabet with
    DEC targets 1..3, from four starts, 6 steps; every program of length 3
    over a 9-instruction alphabet, from two starts, 8 steps."""
    cases = []
    al = small_alphabet(2)
    for ln in (1, 2):
        for P in itertools.product(al, repeat=ln):
            for (a, b) in SMALL_STARTS:
                cases.append((list(P), a, b, 6))
    for P in itertools.product(SMALL_REDUCED, repeat=3):
        for (a, b) in ((0, 0), (1, 2)):
            cases.append((list(P), a, b, 8))
    return cases


def small_random(seed: int, count: int, maxlen: int = 14, steps: int = 40):
    rng = random.Random(seed)
    cases = []
    for _ in range(count):
        ln = rng.randint(3, maxlen)
        al = small_alphabet(ln)
        w = rng.choice([1, 1, 2, 3])  # bias toward the record instructions
        P = [rng.choice(al) for _ in range(ln)]
        a, b = rng.randint(0, 4), rng.randint(0, 4)
        cases.append((P, a, b, steps))
    return cases


def small_cap_cases():
    """Programs that fill the fact table (cap 16) and then overflow it."""
    chk = [("CHECK", ("PZero",), 0)] * 20 + [("HALT",)]
    chk2 = ([("CHECK", ("PZero",), 0), ("CHECK", ("PEven",), 0)] * 9) + [("HALT",)]
    inc_chk = [("CHECK", ("PGe", 0), 0), ("INC", 0)] * 10 + [("COMMIT", ("PGe", 0), 0), ("CERTIFY",)]
    return [(chk, 0, 0, 30), (chk2, 0, 0, 30), (inc_chk, 0, 0, 40),
            ([("CHECK", ("PZero",), 0)] * 16 + [("COMMIT", ("PZero",), 0), ("CERTIFY",)], 0, 0, 25)]


def host_alphabet(L: int, nr: int, priced_: bool):
    al = []
    for r in range(nr):
        al.append(("INC", r))
    for r in range(nr):
        for j in range(1, L + 2):
            al.append(("DEC", r, j))
    al.append(("HALT",))
    for p in PROPS[:3]:
        for r in range(nr):
            al.append(("CHECK", p, r))
    for p in PROPS[:3]:
        for r in range(nr):
            al.append(("COMMIT", p, r))
    al.append(("CERTIFY",))
    if priced_:
        al.append(("PAY",))
    return al


HOST_STARTS = [{}, {0: 1}, {1: 2}, {0: 3, 1: 1}]


def host_exhaustive(priced_: bool):
    cases = []
    al = host_alphabet(2, 2, priced_)
    for ln in (1, 2):
        for P in itertools.product(al, repeat=ln):
            for vs in HOST_STARTS:
                cases.append((list(P), dict(vs), 5, 6))
    return cases


def host_random(seed: int, count: int, priced_: bool, maxlen: int = 12, steps: int = 40):
    rng = random.Random(seed)
    cases = []
    for _ in range(count):
        ln = rng.randint(3, maxlen)
        nr = rng.randint(2, 5)
        al = host_alphabet(ln, nr, priced_)
        P = [rng.choice(al) for _ in range(ln)]
        vs = {r: rng.randint(0, 4) for r in range(nr) if rng.random() < 0.6}
        cases.append((P, vs, 6, steps))
    return cases


def host_cap_cases(priced_: bool):
    chk = [("CHECK", ("PZero",), 0)] * 20 + [("HALT",)]
    return [(chk, {}, 4, 30)]


# ---------------------------------------------------------------------------
# the host over PSlot (UniversalCodes.v) and the universal program U
# ---------------------------------------------------------------------------

PRELUDE_FULL = PRELUDE_MIN + r"""
Require Import Kernel.RealizeNames.
Require Kernel.Realize.
Module R := Kernel.Realize.

Definition smf (f : @M.fact UC.hprop) := (0, 0, M.f_reg f, M.f_ver f).
Definition snapSlot (nr : nat) (s : @M.state UC.hprop) :=
  let k := M.core_of s in
  (M.pc k, map (M.vals k) (seq 0 nr), map (M.vers k) (seq 0 nr), map smf (M.facts k),
   option_map smf (M.chan k), b2n (M.err k), M.mu s, b2n (M.cert s)).
Fixpoint trSlot (nr n : nat) (P : list (@M.instr UC.hprop)) (s : @M.state UC.hprop) :=
  match n with 0 => [snapSlot nr s]
  | S m => snapSlot nr s :: trSlot nr m P (R.rlz_host_step P s) end.
(* U: the host after each further stride steps of U *)
Fixpoint chkU (nr stride k : nat) (s : @M.state UC.hprop) :=
  match k with 0 => []
  | S k' => let s' := R.rlz_host_run_prog stride R.rlz_host_program s in
            snapSlot nr s' :: chkU nr stride k' s' end.
"""


def r_slot(P, vs, n, nr) -> str:
    regl = coq_list([str(vs.get(r, 0)) for r in range(max(vs) + 1 if vs else 0)])
    return "Compute (trSlot %d %d %s (R.rlz_host_start (regs %s)))." % (
        nr, n, coq_list([host_instr(i, "M", "UC.PSlot") for i in P]), regl)


def r_universal(P, x, y, stride, k, nr) -> str:
    st = "(R.rlz_host_load %s %d %d)" % (coq_list([small_instr(i) for i in P]), x, y)
    return "Compute (snapSlot %d %s :: chkU %d %d %d %s)." % (nr, st, nr, stride, k, st)


def py_slot(host: multi.Host, P, vs, n, nr):
    return py_host(host, P, vs, n, nr)


def py_universal(P, x, y, stride, k, nr):
    from thiele_small import universal
    s = universal.hload(P, x, y)
    out = [universal.HOST.snapshot(s, nr)]
    for _ in range(k):
        s = universal.HOST.run_prog(stride, universal.U, s)
        out.append(universal.HOST.snapshot(s, nr))
    return out


# PSlot values: x = pair (pcode p) v holds exactly when p holds of v.
SLOT_VALUES = [0, 1, 5, 7, 10, 22]   # 0: none; 1 = (PZero,0) true; 5 = (PZero,2) false;
#                                      7 = (PZero,3) false; 10 = (PEven,2) true; 22 = (PEven,5) false


def slot_alphabet(L: int, nr: int):
    al = []
    for r in range(nr):
        al.append(("INC", r))
    for r in range(nr):
        for j in range(1, L + 2):
            al.append(("DEC", r, j))
    al.append(("HALT",))
    for r in range(nr):
        al.append(("CHECK", ("PSlot",), r))
    for r in range(nr):
        al.append(("COMMIT", ("PSlot",), r))
    al.append(("CERTIFY",))
    return al


def slot_exhaustive():
    cases = []
    al = slot_alphabet(2, 2)
    starts = [{0: a, 1: b} for a in (0, 1, 7, 10) for b in (0, 1, 22)]
    for ln in (1, 2):
        for P in itertools.product(al, repeat=ln):
            for vs in starts:
                cases.append((list(P), dict(vs), 5, 4))
    # chains on a register holding a true claim, a false claim and no claim
    for a in (1, 10, 7, 0):
        chain = [("CHECK", ("PSlot",), 0), ("COMMIT", ("PSlot",), 0), ("CERTIFY",)]
        cases.append((chain, {0: a}, 6, 4))
        cases.append(([("CHECK", ("PSlot",), 0), ("INC", 0), ("COMMIT", ("PSlot",), 0), ("CERTIFY",)],
                      {0: a}, 8, 4))
    return cases


def slot_random(seed: int, count: int, maxlen: int = 12, steps: int = 40):
    rng = random.Random(seed)
    cases = []
    for _ in range(count):
        ln = rng.randint(3, maxlen)
        nr = rng.randint(2, 4)
        al = slot_alphabet(ln, nr)
        P = [rng.choice(al) for _ in range(ln)]
        vs = {r: rng.choice(SLOT_VALUES) for r in range(nr)}
        cases.append((P, vs, steps, 6))
    return cases


def slot_cap_cases():
    chk = [("CHECK", ("PSlot",), 0)] * 20 + [("HALT",)]
    return [(chk, {0: 1}, 30, 4)]


# Guests small enough for U (see data/programs.json and the status notes:
# U does unary loops over the program code, a power of two of the sum of the
# instruction codes, so only guests of INC, HALT and DEC A 1 are practical).
UGUEST_ALPHABET = [("INC", 0), ("INC", 1), ("DEC", 0, 1), ("HALT",)]
UGUEST_STARTS = [(0, 0), (2, 1)]


def universal_cases(max_len: int = 3, max_code_bits: int = 14):
    out = []
    for ln in range(1, max_len + 1):
        for P in itertools.product(UGUEST_ALPHABET, repeat=ln):
            if codes.prog_code(P).bit_length() > max_code_bits:
                continue
            for (x, y) in UGUEST_STARTS:
                out.append((list(P), x, y))
    return out


def coq_instr_to_py(v):
    """Turn a parsed Coq `option instr` (None / Some (E.INC E.CA) ...) of the
    small machine into the Python instruction tuple, or None."""
    from realize_harness import Con
    if isinstance(v, Con) and v.name == "None":
        return None
    assert isinstance(v, Con) and v.name == "Some", v
    i = v.args[0]
    if not isinstance(i, Con):
        raise ValueError(v)

    def ctr(c):
        return 0 if c.name == "CA" else 1

    def prop(p):
        if p.name == "PGe":
            return ("PGe", p.args[0])
        return (p.name,)

    n, a = i.name, i.args
    if n == "INC":
        return ("INC", ctr(a[0]))
    if n == "DEC":
        return ("DEC", ctr(a[0]), a[1])
    if n == "HALT":
        return ("HALT",)
    if n in ("CHECK", "COMMIT"):
        return (n, prop(a[0]), ctr(a[1]))
    if n == "CERTIFY":
        return ("CERTIFY",)
    raise ValueError(v)
