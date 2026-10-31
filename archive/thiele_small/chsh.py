"""CHSH tolerance CHECK for the versioned multi-register machine.

Mirrors Kernel.SmallChshTolerance: p/q is fixed for a machine instance,
counts are encoded using EarnedGeneric's list code, and certification
establishes the relaxed bound S^2 <= 8 (1 + p/q)^2. This hand-written
Python implementation is not extracted Coq code.
"""

from .codes import decode, encode
from .multi import Host, Lang

PCHSH = ("PCHSH",)


def tolerance_check(counts, p=0, q=1):
    """The integer test nec_e_tol_check; p >= 0 and q > 0 are required."""
    counts = tuple(counts)
    if len(counts) != 8 or any(type(x) is not int or x < 0 for x in counts):
        raise ValueError("a tally must contain eight natural-number counts")
    if type(p) is not int or type(q) is not int:
        raise ValueError("the tolerance numerator and denominator must be integers")
    if p < 0 or q <= 0:
        return False
    n00, n01, n10, n11 = (counts[i] + counts[i + 1] for i in range(0, 8, 2))
    d00, d01, d10, d11 = (counts[i] - counts[i + 1] for i in range(0, 8, 2))
    if min(n00, n01, n10, n11) == 0:
        return False
    k, scale = (q + p) ** 2, q ** 2
    a = k * n00**2 * n10**2 - scale * (d00**2 * n10**2 + d10**2 * n00**2)
    b = k * n01**2 * n11**2 - scale * (d01**2 * n11**2 + d11**2 * n01**2)
    cross = d00 * d01 * n10 * n11 + d10 * d11 * n00 * n01
    return a >= 0 and b >= 0 and scale**2 * cross**2 <= a * b


def tally_of(value):
    """Decode eight counts; missing entries read as zero, as in Coq."""
    if type(value) is not int or value < 0:
        raise ValueError("a register value must be a natural number")
    return tuple((decode(value) + [0] * 8)[:8])


def tally_code(counts):
    counts = tuple(counts)
    tolerance_check(counts)  # Validate the count domain, including rejected tallies.
    return encode(counts)


def tolerance_host(p=0, q=1):
    """Create a host whose PCHSH instruction checks the fixed tolerance p/q."""
    tolerance_check((0,) * 8, p, q)  # Validate the integer parameter types.

    def evaluate(prop, value):
        if prop != PCHSH:
            raise ValueError("unknown CHSH property")
        return tolerance_check(tally_of(value), p, q)

    return Host(Lang("CHSH(%s/%s)" % (p, q), lambda a, b: a == b,
                     evaluate, lambda prop: (0, 0)))


def chain(register=0):
    return [("CHECK", PCHSH, register), ("COMMIT", PCHSH, register), ("CERTIFY",)]
