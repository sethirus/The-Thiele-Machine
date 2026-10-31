"""The multi-register host: the machine of minimal/EarnedMulti.v, and with
PAY the machine of minimal/EarnedMultiPriced.v.

A counter for every register r : nat, held as two functions vals and vers.
Here both are dicts with default 0, so only finitely supported start
functions can be represented. Every start used by the universal program
(hload) and every test is finitely supported. The Coq definition takes any
function nat -> nat; that generality is not represented.

Instructions are tuples:
    ("INC", r)         M.INC r
    ("DEC", r, j)      M.DEC r j
    ("HALT",)          M.HALT
    ("CHECK", p, r)    M.CHECK p r
    ("COMMIT", p, r)   M.COMMIT p r
    ("CERTIFY",)       M.CERTIFY
    ("PAY",)           pu_instr PAY (priced hosts only)

The property language is a Lang: a boolean equality eqb and a boolean
checker eval, the two parameters prop_eqb and eval of the Coq section.

Names. EarnedMulti.v and EarnedMultiPriced.v define the same functions
under different names (exec / pu_exec, run_prog / pu_run_prog, and so on);
the docstrings give the unpriced name, and the priced one is the same with
the prefix pu_. The priced machine differs only in the extra instruction
PAY (cost 1, pc := pc + 1, nothing else, nothing at all on a trapped
machine but the ledger), so one implementation serves both; a Host built
with priced=False rejects PAY.
"""

from __future__ import annotations

from typing import Callable, Dict, List, Optional, Sequence, Tuple

from . import small
from . import codes

FACT_CAP = 16  # Coq: fact_cap / pu_fact_cap := 16


class Lang:
    """The open property language of EarnedMulti.v: prop_eqb and eval
    (the Variables of the Coq Section), plus snap, a printing code used
    only to compare states (not a Coq definition)."""

    def __init__(self, name: str, eqb: Callable, eval_: Callable, snap: Callable):
        self.name = name
        self.eqb = eqb
        self.eval = eval_
        self.snap = snap


# The counter language of EarnedCore.v used as the host's property language.
SMALL = Lang("E.prop", small.prop_eqb, small.eval_prop, small.prop_snap)

# UniversalCodes.v: hprop = PSlot, eval is heval (the counter holds
# pair (pcode p) v and p holds of v).
SLOT = Lang("hprop", lambda p, q: p == q, lambda p, x: codes.heval(x),
            lambda p: (0, 0))

# UniversalPCodes.v: pu_hprop = PSlot, eval is pu_heval (the universal
# checker cg_ueval).
PSLOT = Lang("pu_hprop", lambda p, q: p == q, lambda p, x: codes.pu_heval(x),
             lambda p: (0, 0))


class HState:
    """Coq: state = mkst (core_of : core) (mu : nat) (cert : bool) with
    core = mkcore vals vers pc facts chan err, flattened.

    vals, vers: dict register -> nat, absent keys are 0. facts: NEWEST FIRST.
    """

    __slots__ = ("vals", "vers", "pc", "facts", "chan", "err", "mu", "cert")

    def __init__(self, vals=None, vers=None, pc=1, facts=(), chan=None,
                 err=False, mu=0, cert=False):
        self.vals = dict(vals) if vals else {}
        self.vers = dict(vers) if vers else {}
        self.pc = pc
        self.facts = list(facts)
        self.chan = chan
        self.err = err
        self.mu = mu
        self.cert = cert

    def copy(self) -> "HState":
        return HState(self.vals, self.vers, self.pc, self.facts, self.chan,
                      self.err, self.mu, self.cert)

    def val(self, r: int) -> int:
        """Coq: vals (core_of s) r."""
        return self.vals.get(r, 0)

    def ver(self, r: int) -> int:
        """Coq: vers (core_of s) r."""
        return self.vers.get(r, 0)


def cost(i) -> int:
    """Coq: cost / pu_cost. CHECK, COMMIT, CERTIFY (and PAY) cost 1."""
    return 1 if i[0] in ("CHECK", "COMMIT", "CERTIFY", "PAY") else 0


class Host:
    """The host machine over a property language, priced (with PAY) or not."""

    def __init__(self, lang: Lang, priced: bool = False):
        self.lang = lang
        self.priced = priced

    # -- start ---------------------------------------------------------

    def start(self, vs: Optional[Dict[int, int]] = None) -> HState:
        """Coq: start vs = mkst (start_core vs) 0 false, with
        start_core vs = mkcore vs (fun _ => 0) 1 [] None false."""
        return HState(vs or {}, {}, 1, (), None, False, 0, False)

    # -- the checks ------------------------------------------------------

    def claim(self, k: HState, p, r: int):
        """Coq: claim k p r = mkfact p r (vers k r)."""
        return (p, r, k.ver(r))

    def check_ok(self, k: HState, p, r: int) -> bool:
        """Coq: check_ok k p r := negb (err k) && eval p (vals k r)
        && Nat.ltb (length (facts k)) fact_cap."""
        return ((not k.err) and self.lang.eval(p, k.val(r))
                and len(k.facts) < FACT_CAP)

    def commit_ok(self, k: HState, p, r: int) -> bool:
        """Coq: commit_ok k p r := negb (err k) &&
        existsb (fact_eqb (claim k p r)) (facts k), with fact_eqb comparing
        prop (prop_eqb), register and version."""
        if k.err:
            return False
        q, rr, vv = self.claim(k, p, r)
        for (fp, fr, fv) in k.facts:
            if self.lang.eqb(q, fp) and rr == fr and vv == fv:
                return True
        return False

    def certify_ok(self, k: HState) -> bool:
        """Coq: certify_ok k := negb (err k) && (chan k is Some _)."""
        return (not k.err) and k.chan is not None

    # -- one instruction -------------------------------------------------

    def cexec_inplace(self, k: HState, i) -> None:
        """Coq: cexec k i, applied in place."""
        if k.err:
            return
        op = i[0]
        if op == "INC":
            r = i[1]
            n = k.val(r) + 1
            k.vals[r] = n  # write k r (S (vals k r)) (S (pc k))
            k.vers[r] = k.ver(r) + 1
            k.pc += 1
        elif op == "DEC":
            r, j = i[1], i[2]
            n = k.val(r)
            if n == 0:
                k.pc += 1  # goto k (S (pc k))
            else:
                k.vals[r] = n - 1  # write k r n' j
                k.vers[r] = k.ver(r) + 1
                k.pc = j
        elif op == "HALT":
            pass
        elif op == "CHECK":
            p, r = i[1], i[2]
            if self.check_ok(k, p, r):
                f = self.claim(k, p, r)
                k.pc += 1
                k.facts.insert(0, f)  # record_fact: f :: facts
            else:
                k.err = True  # trap
        elif op == "COMMIT":
            p, r = i[1], i[2]
            if self.commit_ok(k, p, r):
                f = self.claim(k, p, r)
                k.pc += 1
                k.chan = f  # commit_to
            else:
                k.err = True
        elif op == "CERTIFY":
            if self.certify_ok(k):
                k.pc += 1
            else:
                k.err = True
        elif op == "PAY" and self.priced:
            k.pc += 1  # pu_goto k (S (pc k))
        else:
            raise ValueError("unknown instruction %r" % (i,))

    def fires(self, k: HState, i) -> bool:
        """Coq: fires k i := match i with CERTIFY => certify_ok k | _ => false."""
        return i[0] == "CERTIFY" and self.certify_ok(k)

    def exec(self, s: HState, i) -> HState:
        """Coq: exec s i = mkst (cexec (core_of s) i) (mu s + cost i)
        (cert s || fires (core_of s) i). Returns a new state."""
        t = s.copy()
        self._apply(t, i)
        return t

    def _apply(self, t: HState, i) -> None:
        fl = self.fires(t, i)
        self.cexec_inplace(t, i)
        t.mu += cost(i)
        t.cert = t.cert or fl

    def run(self, tr: Sequence, s: HState) -> HState:
        """Coq: run tr s."""
        t = s.copy()
        for i in tr:
            self._apply(t, i)
        return t

    def total_cost(self, tr: Sequence) -> int:
        """Coq: total_cost tr."""
        return sum(cost(i) for i in tr)

    # -- stored programs -------------------------------------------------

    @staticmethod
    def fetch(P: Sequence, n: int):
        """Coq: fetch P n; 1-based, fetch P 0 = None."""
        if n == 0:
            return None
        return P[n - 1] if n - 1 < len(P) else None

    def next_instr(self, P: Sequence, k: HState):
        """Coq: next_instr P k: None when trapped, off the program or at HALT."""
        if k.err:
            return None
        i = self.fetch(P, k.pc)
        if i is not None and i[0] == "HALT":
            return None
        return i

    def halted(self, P: Sequence, k: HState) -> bool:
        """Coq: halted P k := next_instr P k = None."""
        return self.next_instr(P, k) is None

    def _step_inplace(self, P: Sequence, t: HState) -> bool:
        i = self.next_instr(P, t)
        if i is None:
            return False
        self._apply(t, i)
        return True

    def step(self, P: Sequence, s: HState) -> HState:
        """Coq: step P s."""
        t = s.copy()
        self._step_inplace(P, t)
        return t

    def run_prog(self, n: int, P: Sequence, s: HState) -> HState:
        """Coq: run_prog n P s: n steps of a stored program."""
        t = s.copy()
        for _ in range(n):
            if not self._step_inplace(P, t):
                break  # a stopped program stays stopped (run_prog_halted)
        return t

    def trace_of(self, n: int, P: Sequence, s: HState) -> List:
        """Coq: trace_of n P s: the instructions a run executes."""
        t = s.copy()
        out: List = []
        for _ in range(n):
            i = self.next_instr(P, t)
            if i is None:
                break
            out.append(i)
            self._apply(t, i)
        return out

    # -- comparison format ----------------------------------------------

    def snapshot(self, s: HState, nregs: int):
        """(pc, [vals 0..nregs-1], [vers 0..nregs-1], facts newest first,
        chan, err, mu, cert). Not a Coq definition. Registers at or above
        nregs are not shown; see outside_regs."""
        def fs(f):
            if f is None:
                return None
            k, n = self.lang.snap(f[0])
            return (k, n, f[1], f[2])
        return (s.pc,
                [s.val(r) for r in range(nregs)],
                [s.ver(r) for r in range(nregs)],
                [fs(f) for f in s.facts], fs(s.chan),
                int(s.err), s.mu, int(s.cert))

    @staticmethod
    def outside_regs(s: HState, nregs: int):
        """Registers at or above nregs that differ from the start values 0
        in value or version (a check that a snapshot window is wide enough)."""
        return sorted(set(r for r, v in s.vals.items() if r >= nregs and v != 0)
                      | set(r for r, v in s.vers.items() if r >= nregs and v != 0))
