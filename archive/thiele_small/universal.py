"""The universal host programs U and U_P, their loaders, and runs.

The instruction lists are DATA, printed by Coq from the definitions
U (UniversalLayout.v) and U_P (UniversalPLayout.v) by
scripts/realize_gen_programs.py, and stored in data/programs.json as
[op, a, b] triples (op 0 INC a, 1 DEC a b, 2 HALT, 3 CHECK PSlot a,
4 COMMIT PSlot a, 5 CERTIFY, 6 PAY). They are not retyped here.
tests/test_realize.py regenerates the table from Coq and compares it with
this file's data.

The loaders mirror UniversalSim.v (hregs, hload) and UniversalPSim.v
(pu_hregs, pu_hload).
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Dict, List, Sequence

from . import codes, multi, small, priced

_DATA = json.loads((Path(__file__).parent / "data" / "programs.json").read_text(encoding="utf-8"))

LAYOUT: Dict[str, int] = _DATA["layout"]

# Coq: UniversalLayout.v RA RB PROG GPC, and UniversalPLayout.v pu_RA ...
RA, RB, PROG, GPC = LAYOUT["RA"], LAYOUT["RB"], LAYOUT["PROG"], LAYOUT["GPC"]

PSLOT = ("PSlot",)


def _decode(trips: Sequence[Sequence[int]]) -> List[tuple]:
    out = []
    for op, a, b in trips:
        if op == 0:
            out.append(("INC", a))
        elif op == 1:
            out.append(("DEC", a, b))
        elif op == 2:
            out.append(("HALT",))
        elif op == 3:
            out.append(("CHECK", PSLOT, a))
        elif op == 4:
            out.append(("COMMIT", PSLOT, a))
        elif op == 5:
            out.append(("CERTIFY",))
        elif op == 6:
            out.append(("PAY",))
        else:
            raise ValueError(op)
    return out


# Coq: Definition U : list hinstr := concat Usecs.   (UniversalLayout.v)
U: List[tuple] = _decode(_DATA["U"])

# Coq: Definition U_P : list hinstr := concat pu_Usecs.   (UniversalPLayout.v)
U_P: List[tuple] = _decode(_DATA["U_P"])

HOST = multi.Host(multi.SLOT, priced=False)
HOST_P = multi.Host(multi.PSLOT, priced=True)
GUEST_P = priced.Guest(priced.UPROP, priced=True)


def hregs(P: Sequence, x: int, y: int) -> Dict[int, int]:
    """Coq: hregs P x y (UniversalSim.v). RA and RB hold the guest's inputs,
    PROG the program code, GPC the guest pc 1; every other register 0.
    Returned as the finite support of the function."""
    return {RA: x, RB: y, PROG: codes.prog_code(P), GPC: 1}


def hload(P: Sequence, x: int, y: int):
    """Coq: hload P x y := M.start (hregs P x y)."""
    return HOST.start(hregs(P, x, y))


def pu_hregs(P: Sequence, x: int, y: int) -> Dict[int, int]:
    """Coq: pu_hregs P x y (UniversalPSim.v)."""
    return {RA: x, RB: y, PROG: codes.pu_prog_code(P), GPC: 1}


def pu_hload(P: Sequence, x: int, y: int):
    """Coq: pu_hload P x y := M.pu_start (pu_hregs P x y)."""
    return HOST_P.start(pu_hregs(P, x, y))


def grun(P: Sequence, x: int, y: int, m: int):
    """The guest after m steps from E.start x y (UniversalRun.v grun)."""
    return small.run_prog(m, P, small.start(x, y))


def hrun(P: Sequence, x: int, y: int, n: int):
    """The host after n steps of U from hload P x y (UniversalRun.v hrun)."""
    return HOST.run_prog(n, U, hload(P, x, y))


def pu_grun(P: Sequence, x: int, y: int, m: int):
    """The priced guest after m steps from G.start x y (UniversalPRun.v)."""
    return GUEST_P.run_prog(m, P, GUEST_P.start(x, y))


def pu_hrun(P: Sequence, x: int, y: int, n: int):
    """The host after n steps of U_P from pu_hload P x y."""
    return HOST_P.run_prog(n, U_P, pu_hload(P, x, y))


def host_run_to_halt(host: multi.Host, prog: Sequence, s, limit: int):
    """Step until the host program stops or limit steps have run. Returns
    (state, steps taken, stopped)."""
    t = s.copy()
    n = 0
    while n < limit:
        if host._step_inplace(prog, t) is False:
            return t, n, True
        n += 1
    return t, n, host.halted(prog, t)
