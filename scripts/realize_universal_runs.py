#!/usr/bin/env python3
"""Run the universal programs U and U_P, extracted from Coq, on guest programs
and check the relations the theorems of UniversalRun.v and UniversalPRun.v
state, reporting the measured host steps and wall time of each run.

    python scripts/realize_universal_runs.py DRIVER [--case NAME ...] [--jobs N] [--json OUT]

DRIVER is the executable built by scripts/realize_extract.sh
(build/realize/realize_driver). Each case names a guest program and a start.
The driver (ocaml/realize_driver.ml, commands urun and purun) steps the
extracted host one step at a time until the host program stops, and returns
the number of steps, the number of visits of the loop head and the host state
at each visit and at the stop.

What is checked, against the python realisation of the guest machine
(thiele_small/, itself compared with Coq in tests/test_realize.py):

  * the host stops exactly when the guest stops (universal_halting);
  * the k-th visit of the loop head shows the guest after k steps (a guest that
    traps is stopped by the host in the same step, so its trapped state has no visit): the guest
    counters in the registers RA and RB, the guest pc in GPC, and the same
    ledger, flag and trap latch (U_simulation);
  * at the stop RA, RB, the trap latch, the ledger and the flag equal the
    guest's (universal_output, universal_flag_iff, universal_ledger_exact),
    and the host's table of facts has as many entries as the guest's.

The cost of a run. U decodes the guest program from its program code, a power
of two of the sum of the instruction codes, by a loop in unary: the host takes
about twelve steps per unit of the program code at each visit of the loop
head. The codes of the instructions are INC A 1, INC B 3, HALT 4, DEC A 1 14,
CHECK PZero A 24, COMMIT PZero A 48, CERTIFY 32, PAY 64. A guest with a record
instruction therefore has a program code of at least 2^24, and CHECK PZero A
alone is a run of about 4 * 10^8 host steps (a few minutes). CERTIFY alone
(2^32) is about 5 * 10^10 host steps, seventeen hours at the measured rate;
COMMIT (2^48), PAY (2^64) and the chain CHECK, COMMIT, CERTIFY (about 2^100) are
beyond any machine. The cases below are the ones that finish.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

from thiele_small import codes, flat, small, universal  # noqa: E402

NR = 96  # registers shown in a state line; U uses fewer (see universal.LAYOUT)

Z = ("PZero",)
EV = ("PEven",)

# name -> (machine, guest program, start A, start B, a note)
CASES = {
    "inc-halt": ("U", [("INC", 0), ("HALT",)], 0, 0, "no record instruction"),
    "inc-inc-halt": ("U", [("INC", 0), ("INC", 1), ("HALT",)], 0, 0, "two writes, then HALT"),
    "dec-loop": ("U", [("DEC", 0, 1), ("HALT",)], 2, 0, "a loop that counts A down from 2"),
    "check-true": ("U", [("CHECK", Z, 0)], 0, 0, "CHECK that holds: a fact, ledger 1"),
    "check-false": ("U", [("CHECK", Z, 0)], 1, 0, "CHECK that fails: the trap latch"),
    "inc-check": ("U", [("INC", 0), ("CHECK", Z, 0)], 0, 0, "INC then a CHECK that fails"),
    "check-inc": ("U", [("CHECK", Z, 0), ("INC", 0)], 0, 0, "CHECK that holds, then INC"),
    "p-inc-halt": ("UP", [("INC", 0), ("HALT",)], 0, 0, "priced guest, no record instruction"),
    "p-inc-inc-halt": ("UP", [("INC", 0), ("INC", 1), ("HALT",)], 0, 0, "priced guest, two writes"),
    "p-check-true": ("UP", [("CHECK", ("UBase", Z), 0)], 0, 0, "CHECK that holds on the priced guest"),
    "p-check-false": ("UP", [("CHECK", ("UBase", Z), 0)], 1, 0, "CHECK that fails on the priced guest"),
}

QUICK = ["inc-halt", "inc-inc-halt", "dec-loop", "p-inc-halt", "p-inc-inc-halt"]


def _ints(line):
    return [int(t) for t in line.split()]


def _parse_host(line):
    """pc err mu cert, CHAN, FACTS, nregs, vals, vers (flat.flat_host)."""
    v = _ints(line)
    pc, err, mu, cert = v[:4]
    i = 4
    if v[i] == 0:
        i += 1
    else:
        i += 5
    nf = v[i]
    i += 1 + 4 * nf
    nr = v[i]
    vals = v[i + 1:i + 1 + nr]
    return {"pc": pc, "err": err, "mu": mu, "cert": cert, "nfacts": nf, "vals": vals}


def _guest_states(machine, P, x, y, cap=500):
    """The guest's states from the start to its stop, as flat lists."""
    if machine == "U":
        s = small.start(x, y)
        out = [flat.flat_small(s)]
        while not small.halted(P, s) and len(out) < cap:
            s = small.step(P, s)
            out.append(flat.flat_small(s))
        return out, small.halted(P, s)
    g = universal.GUEST_P
    s = g.start(x, y)
    out = [flat.flat_guest(g, s)]
    while not g.halted(P, s) and len(out) < cap:
        s = g.step(P, s)
        out.append(flat.flat_guest(g, s))
    return out, g.halted(P, s)


def run_case(driver, name, max_steps=10 ** 12, max_heads=1000, timeout=None):
    machine, P, x, y, note = CASES[name]
    cmd = "urun" if machine == "U" else "purun"
    toks = [cmd, NR, max_heads, max_steps, x, y] + flat.prog_tokens(P)
    pcode = codes.prog_code(P) if machine == "U" else codes.pu_prog_code(P)
    t0 = time.time()
    p = subprocess.run([str(driver)], input=" ".join(str(t) for t in toks),
                       capture_output=True, text=True, timeout=timeout)
    wall = time.time() - t0
    if p.returncode != 0:
        raise RuntimeError("driver failed on %s: %s" % (name, p.stderr[-1000:]))
    lines = [ln for ln in p.stdout.splitlines() if ln != "END"]
    _, steps, stopped = lines[0].split()
    steps, stopped = int(steps), bool(int(stopped))
    nheads = int(lines[1].split()[1])
    head_lines = lines[2:-1]
    final = _parse_host(lines[-1])
    gs, guest_stopped = _guest_states(machine, P, x, y)
    problems = []
    if stopped != guest_stopped:
        problems.append("host stopped %s, guest stopped %s" % (stopped, guest_stopped))
    if stopped:
        # A guest that traps is stopped by the host in the same step, inside the
        # host's own CHECK, COMMIT or CERTIFY: the host never returns to the loop
        # head with the trapped guest, so that guest state has no head visit.
        trapped = gs[-1][5] == 1
        want_heads = len(gs) - 1 if trapped else len(gs)
        if nheads != want_heads:
            problems.append("%d loop head visits, expected %d" % (nheads, want_heads))
        for k, (hl, g) in enumerate(zip(head_lines, gs)):
            h = _parse_host(hl)
            gpc, gca, gcb, _va, _vb, gerr, gmu, gcert = g[:8]
            got = (h["vals"][universal.RA], h["vals"][universal.RB], h["vals"][universal.GPC],
                   h["mu"], h["cert"], h["err"])
            want = (gca, gcb, gpc, gmu, gcert, gerr)
            if got != want:
                problems.append("head %d: host %r guest %r" % (k, got, want))
                break
        g = gs[-1]
        want = (g[1], g[2], g[6], g[7], g[5])
        got = (final["vals"][universal.RA], final["vals"][universal.RB], final["mu"], final["cert"], final["err"])
        if got != want:
            problems.append("stop: host %r guest %r" % (got, want))
        gfacts = _facts_count(g)
        if final["nfacts"] != gfacts:
            problems.append("host has %d facts, guest %d" % (final["nfacts"], gfacts))
    return {
        "case": name, "machine": machine, "note": note, "guest": [list(map(str, i)) for i in P],
        "start": [x, y], "program_code_bits": pcode.bit_length() - 1 if pcode else 0,
        "host_steps": steps, "host_stopped": stopped, "guest_steps": len(gs) - 1,
        "loop_head_visits": nheads, "wall_seconds": round(wall, 1),
        "steps_per_second": round(steps / wall) if wall > 0 else None,
        "final": {"RA": final["vals"][universal.RA], "RB": final["vals"][universal.RB],
                  "ledger": final["mu"], "flag": final["cert"], "trap": final["err"],
                  "facts": final["nfacts"]},
        "guest_final": {"A": gs[-1][1], "B": gs[-1][2], "ledger": gs[-1][6], "flag": gs[-1][7],
                        "trap": gs[-1][5], "facts": _facts_count(gs[-1])},
        "ok": not problems, "problems": problems,
    }


def _facts_count(g):
    """Number of facts in a flat guest state (flat.flat_small layout)."""
    i = 8
    i += 1 if g[i] == 0 else 5
    return g[i]


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("driver")
    ap.add_argument("--case", action="append", help="case name (default: the quick ones); 'all' for every case")
    ap.add_argument("--json")
    ap.add_argument("--jobs", type=int, default=1,
                    help="how many cases to run at the same time (each is a separate driver process)")
    a = ap.parse_args(argv)
    names = a.case or QUICK
    if names == ["all"]:
        names = list(CASES)

    def one(n):
        r = run_case(a.driver, n)
        print("%-14s %-2s code 2^%-3d host steps %-12d guest steps %-3d %7.1fs  %s%s" % (
            n, r["machine"], r["program_code_bits"], r["host_steps"], r["guest_steps"],
            r["wall_seconds"], "ok" if r["ok"] else "FAIL ", "; ".join(r["problems"])), flush=True)
        return r

    if a.jobs > 1:
        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(max_workers=a.jobs) as pool:
            results = list(pool.map(one, names))
    else:
        results = [one(n) for n in names]
    ok = all(r["ok"] for r in results)
    if a.json:
        Path(a.json).write_text(json.dumps(results, indent=1), encoding="utf-8")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
