"""Numbers as data: the pairing of UniversalCodes.v, the list code of
EarnedGeneric.v, the guest-instruction codes, the host property PSlot, and
the priced variants of UniversalPCodes.v with the routine checker of
CompilerCodes.v and CompilerChecker.v.

Python integers are unbounded, as Coq's nat is. Nothing here truncates.

Two families, as in Coq:
  * unpriced (UniversalCodes.v): guest = small.py; icode, pcode, prog_code,
    heval.
  * priced (UniversalPCodes.v): guest = priced.py over the universal
    property language cg_uprop = UBase q | URun r; pu_icode, pu_pcode,
    pu_prog_code, pu_heval.
"""

from __future__ import annotations

from typing import List, Optional, Sequence, Tuple

from . import small

# ---------------------------------------------------------------------------
# pairing and the list code.  UniversalCodes.v / EarnedGeneric.v
# ---------------------------------------------------------------------------


def pair(m: int, n: int) -> int:
    """Coq: Definition pair (m n : nat) := (n + n + 1) * 2 ^ m.
    (UniversalCodes.v; UniversalPCodes.v calls it pu_pair.)"""
    return (n + n + 1) * (2 ** m)


def unp(fuel: int, x: int, m: int) -> Optional[Tuple[int, int]]:
    """Coq: Fixpoint unp (fuel x m : nat) : option (nat * nat).
    Strip factors of 2 from x, counting them in m, until x is odd."""
    while True:
        if fuel == 0:
            return None
        if x == 0:
            return None
        if x % 2 == 1:  # Nat.odd x
            return (m, x // 2)  # Nat.div2 x
        fuel -= 1
        x = x // 2
        m += 1


def unpair(x: int) -> Optional[Tuple[int, int]]:
    """Coq: Definition unpair (x : nat) := unp x x 0."""
    return unp(x, x, 0)


def encode(l: Sequence[int]) -> int:
    """Coq: G.encode (EarnedGeneric.v): [] -> 0, x :: t -> 2^x * (2 * encode t + 1)."""
    acc = 0
    for x in reversed(list(l)):
        acc = (2 ** x) * (2 * acc + 1)
    return acc


def decode(v: int) -> List[int]:
    """Coq: G.decode v := dec v v 0 (EarnedGeneric.v), the list a counter
    stands for."""
    fuel, acc = v, 0
    out: List[int] = []
    while True:
        if fuel == 0:
            return out
        if v == 0:
            return out
        fuel -= 1
        if v % 2 == 1:  # Nat.odd v
            out.append(acc)
            acc = 0
        else:
            acc += 1
        v = v // 2  # Nat.div2


# ---------------------------------------------------------------------------
# unpriced guest codes.  UniversalCodes.v
# ---------------------------------------------------------------------------


def pcode(p) -> int:
    """Coq: pcode (UniversalCodes.v): PZero 0, PEven 1, PGe n (n + 2)."""
    k = p[0]
    return 0 if k == "PZero" else 1 if k == "PEven" else p[1] + 2


def pdec(n: int):
    """Coq: pdec (UniversalCodes.v)."""
    if n == 0:
        return ("PZero",)
    if n == 1:
        return ("PEven",)
    return ("PGe", n - 2)


def ccode(c: int) -> int:
    """Coq: ccode: CA -> 0, CB -> 1."""
    return c


def cdec(n: int) -> Optional[int]:
    """Coq: cdec: 0 -> Some CA, 1 -> Some CB, else None."""
    return n if n in (0, 1) else None


def icode(i) -> int:
    """Coq: icode (UniversalCodes.v)."""
    op = i[0]
    if op == "INC":
        return pair(0, ccode(i[1]))
    if op == "DEC":
        return pair(1, pair(ccode(i[1]), i[2]))
    if op == "HALT":
        return pair(2, 0)
    if op == "CHECK":
        return pair(3, pair(ccode(i[2]), pcode(i[1])))
    if op == "COMMIT":
        return pair(4, pair(ccode(i[2]), pcode(i[1])))
    if op == "CERTIFY":
        return pair(5, 0)
    raise ValueError("no code for %r" % (i,))


def idecode(x: int):
    """Coq: idecode (UniversalCodes.v). None when x codes no instruction."""
    u = unpair(x)
    if u is None:
        return None
    o, a = u
    if o == 0:
        c = cdec(a)
        return None if c is None else ("INC", c)
    if o == 1:
        w = unpair(a)
        if w is None:
            return None
        c = cdec(w[0])
        return None if c is None else ("DEC", c, w[1])
    if o == 2 and a == 0:
        return ("HALT",)
    if o in (3, 4):
        w = unpair(a)
        if w is None:
            return None
        c = cdec(w[0])
        if c is None:
            return None
        return (("CHECK" if o == 3 else "COMMIT"), pdec(w[1]), c)
    if o == 5 and a == 0:
        return ("CERTIFY",)
    return None


def prog_code(P: Sequence) -> int:
    """Coq: Definition prog_code (P : list E.instr) := G.encode (map icode P)."""
    return encode([icode(i) for i in P])


def heval(x: int) -> bool:
    """Coq: heval PSlot x (UniversalCodes.v): x codes (pcode p, v) and p
    holds of v. A counter holding 0 satisfies nothing."""
    u = unpair(x)
    if u is None:
        return False
    m, v = u
    return small.eval_prop(pdec(m), v)


# ---------------------------------------------------------------------------
# primes and routines.  CompilerCodes.v, CompilerChecker.v
# ---------------------------------------------------------------------------

_primes: List[int] = [2]


def nthprime(n: int) -> int:
    """Coq: nthprime n = iter nxtprime 2 n (vendored FRACTRAN/Util/prime_seq.v):
    the (n+1)-th prime, nthprime 0 = 2."""
    while len(_primes) <= n:
        c = _primes[-1] + 1
        while any(c % p == 0 for p in _primes if p * p <= c):
            c += 1
        _primes.append(c)
    return _primes[n]


def qs(i: int) -> int:
    """Coq: qs i = nthprime (1 + 2 * i) (prime_seq.v, `qs : primestream`)."""
    return nthprime(1 + 2 * i)


def cg_expo(p: int, n: int) -> int:
    """Coq: cg_expo p n := cg_expo_fuel n p n (CompilerCodes.v). The number of
    times p divides n, with n itself as fuel."""
    f = n
    cnt = 0
    while f > 0:
        # (n mod p = 0) && (0 < n) && (1 < p); with 1 < p the mod is the
        # ordinary one, and with p <= 1 the test fails whatever n mod p is.
        if p > 1 and n > 0 and n % p == 0:
            cnt += 1
            f -= 1
            n = n // p
        else:
            return cnt
    return cnt


def cg_icode(I) -> int:
    """Coq: cg_icode (CompilerCodes.v): mm_inc x -> encode [0; x],
    mm_dec x j -> encode [1; x; j]."""
    return encode([0, I[1]]) if I[0] == "INC" else encode([1, I[1], I[2]])


def cg_penc(R: Sequence) -> int:
    """Coq: cg_penc R := G.encode (map cg_icode R)."""
    return encode([cg_icode(I) for I in R])


def cg_renc(ig: int, R: Sequence, xS: int, xB: int, xT: int, m: int) -> int:
    """Coq: cg_renc ig R xS xB xT m := G.encode [ig; xS; xB; xT; m; cg_penc R]."""
    return encode([ig, xS, xB, xT, m, cg_penc(R)])


def cg_idec(n: int):
    """Coq: cg_idec (CompilerCodes.v): a counter-program instruction from a
    code. ("INC", x) is mm_inc x; ("DEC", x, j) is mm_dec x j."""
    l = decode(n)
    if len(l) == 2 and l[0] == 0:
        return ("INC", l[1])
    if len(l) == 3 and l[0] == 1:
        return ("DEC", l[1], l[2])
    return None


def cg_pdec(n: int):
    """Coq: cg_pdec n := cg_pdec_list (G.decode n) (CompilerCodes.v)."""
    out = []
    for x in decode(n):
        j = cg_idec(x)
        if j is None:
            return None
        out.append(j)
    return out


def cg_rdec(r: int):
    """Coq: cg_rdec (CompilerCodes.v): a routine (ig, R, xS, xB, xT, m) from
    its code, or None."""
    l = decode(r)
    if len(l) != 6:
        return None
    ig, xS, xB, xT, m, rc = l
    R = cg_pdec(rc)
    if R is None:
        return None
    return (ig, R, xS, xB, xT, m)


def cg_run_check(rc, v: int) -> bool:
    """Coq: cg_run_check rc v (CompilerChecker.v). Run the counter program R
    from the environment read off v, for at most cg_expo (qs xT) v steps
    (cg_mme_run_fuel, CompilerCodes.v), and accept when the run is out of
    the code and register xB holds 1."""
    ig, R, xS, xB, xT, m = rc
    env: dict = {}

    def get(x: int) -> int:
        # cg_env_chk m v x = if x < m then cg_expo (qs x) v else 0
        if x in env:
            return env[x]
        return cg_expo(qs(x), v) if x < m else 0

    fuel = cg_expo(qs(xT), v)
    pc = ig
    while fuel > 0:
        # cg_mme_step: fetch at pc if ig <= pc
        if ig <= pc and (pc - ig) < len(R):
            J = R[pc - ig]
        else:
            break
        if J[0] == "INC":
            x = J[1]
            env[x] = get(x) + 1
            pc += 1
        else:
            x, j = J[1], J[2]
            n = get(x)
            if n == 0:
                pc = j
            else:
                env[x] = n - 1
                pc += 1
        fuel -= 1
    out_code = pc < ig or ig + len(R) <= pc  # cg_out_codeb
    return out_code and get(xB) == 1


def cg_ueval(p, v: int) -> bool:
    """Coq: cg_ueval p v (CompilerChecker.v). p is ("UBase", q) with q a small
    property, or ("URun", r)."""
    if p[0] == "UBase":
        return small.eval_prop(p[1], v)
    rc = cg_rdec(p[1])
    return False if rc is None else cg_run_check(rc, v)


# ---------------------------------------------------------------------------
# priced guest codes.  UniversalPCodes.v
# ---------------------------------------------------------------------------


def pu_pair(m: int, n: int) -> int:
    """Coq: pu_pair; the same number as pair."""
    return pair(m, n)


pu_unpair = unpair


def pu_cpcode(q) -> int:
    """Coq: pu_cpcode: PZero 0, PEven 1, PGe n (n + 2)."""
    return pcode(q)


def pu_cpdec(n: int):
    """Coq: pu_cpdec."""
    return pdec(n)


def pu_pcode(p) -> int:
    """Coq: pu_pcode: UBase q -> 2 * cpcode q; URun r -> S (2 * r)."""
    return 2 * pu_cpcode(p[1]) if p[0] == "UBase" else 2 * p[1] + 1


def pu_pdec(n: int):
    """Coq: pu_pdec n := if even n then UBase (cpdec (div2 n)) else URun (div2 n)."""
    return ("UBase", pu_cpdec(n // 2)) if n % 2 == 0 else ("URun", n // 2)


def pu_icode(i) -> int:
    """Coq: pu_icode (UniversalPCodes.v). PAY has code pair 6 0."""
    op = i[0]
    if op == "INC":
        return pair(0, i[1])
    if op == "DEC":
        return pair(1, pair(i[1], i[2]))
    if op == "HALT":
        return pair(2, 0)
    if op == "CHECK":
        return pair(3, pair(i[2], pu_pcode(i[1])))
    if op == "COMMIT":
        return pair(4, pair(i[2], pu_pcode(i[1])))
    if op == "CERTIFY":
        return pair(5, 0)
    if op == "PAY":
        return pair(6, 0)
    raise ValueError("no code for %r" % (i,))


def pu_idecode(x: int):
    """Coq: pu_idecode (UniversalPCodes.v)."""
    u = unpair(x)
    if u is None:
        return None
    o, a = u
    if o == 0:
        c = cdec(a)
        return None if c is None else ("INC", c)
    if o == 1:
        w = unpair(a)
        if w is None:
            return None
        c = cdec(w[0])
        return None if c is None else ("DEC", c, w[1])
    if o == 2 and a == 0:
        return ("HALT",)
    if o in (3, 4):
        w = unpair(a)
        if w is None:
            return None
        c = cdec(w[0])
        if c is None:
            return None
        return (("CHECK" if o == 3 else "COMMIT"), pu_pdec(w[1]), c)
    if o == 5 and a == 0:
        return ("CERTIFY",)
    if o == 6 and a == 0:
        return ("PAY",)
    return None


def pu_prog_code(P: Sequence) -> int:
    """Coq: pu_prog_code P := G.encode (map pu_icode P)."""
    return encode([pu_icode(i) for i in P])


def pu_heval(x: int) -> bool:
    """Coq: pu_heval PSlot x (UniversalPCodes.v): x codes (pu_pcode p, v) and
    cg_ueval p v."""
    u = unpair(x)
    if u is None:
        return False
    m, v = u
    return cg_ueval(pu_pdec(m), v)
