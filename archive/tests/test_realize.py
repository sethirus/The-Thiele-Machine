"""Differential tests of the Python realisation (thiele_small/) against the
Coq definitions.

What is compared, and what each test proves
-------------------------------------------
Every Coq value below is computed by coqc 8.18 with vm_compute from the
definitions of minimal/ and coq/kernel/foundation/ themselves (the rlz_
entry points where the universal files are involved); the Python side is
thiele_small/. A comparison is of the FULL state after EVERY step: program
counter, every register or counter, every version, the fact table (order
included), the channel, the trap latch, the ledger and the flag.

  small machine (EarnedCore.v)     4266 exhaustive-small programs + 300 random
                                   + 4 fact-table-cap programs
  generic / priced guest           1700 + 567 programs over the counter language
  multi host / priced host         2325 / 2509 programs, registers 0..5
  PSlot host (UniversalCodes.v)    2829 programs, registers holding pair codes
  U on guests (UniversalSim.v)     every guest over {INC A, INC B, DEC A 1,
                                   HALT} with code below 2^14, from two starts,
                                   checked at 16 checkpoints, 96 registers
  priced host over PSlot with a    host programs whose registers hold URun
  URun routine                     routines (the prime stream)
  tables                           costs, fact cap, codes, instruction codes,
                                   the layout constants and the programs U
                                   and U_P

Bounds. Exhaustive: all programs of length 1 and 2 over the 26-instruction
alphabet (DEC targets 1..3), four starts, 6 steps; all programs of length 3
over a 9-instruction alphabet, two starts, 8 steps; hosts: length 1 and 2,
registers 0..1, four starts, 5 steps. Random: seeded (20261005 + k), program
length 3..14, up to 60 steps. U: the guest code is a power of two of the sum
of the instruction codes and U loops in unary over it, so only guests with
very small codes can be run; see realize-status for the bound.

These tests need coqc 8.18 (skipped with a reason otherwise). Tests that need
the universal files need a tree where they are compiled: set THIELE_COQ_BUILD
and THIELE_UNDEC (see tests/realize_harness.py), or run in the CI build tree.
"""

from __future__ import annotations

import itertools
import json
import random
import sys
from pathlib import Path

import pytest

TESTS = Path(__file__).resolve().parent
REPO = TESTS.parent
sys.path.insert(0, str(TESTS))
sys.path.insert(0, str(REPO))

import realize_cases as rc  # noqa: E402
import realize_harness as rh  # noqa: E402
from thiele_small import codes, multi, priced, small, universal  # noqa: E402

SEED = 20261005

coq = pytest.mark.coq


# ---------------------------------------------------------------------------
# fixtures
# ---------------------------------------------------------------------------


@pytest.fixture(scope="session")
def coqc():
    c = rh.find_coqc()
    if not c:
        pytest.skip("coqc 8.18 not found (set THIELE_COQC)")
    return c


@pytest.fixture(scope="session")
def min_flags(coqc, tmp_path_factory):
    """minimal/ files compiled into a temporary directory (standard library
    only)."""
    d = tmp_path_factory.mktemp("realize_min")
    rh.build_minimal(coqc, d)
    return ["-Q", str(d / "minimal"), "Minimal"]


@pytest.fixture(scope="session")
def full_flags():
    flags, why = rh.prebuilt_flags()
    if flags is None:
        pytest.skip(why)
    return flags


@pytest.fixture(scope="session")
def workdir(tmp_path_factory):
    return tmp_path_factory.mktemp("realize_coq")


def compare(cases, values, pyfn, label):
    """Return (n compared, list of first mismatches). pyfn maps a case to the
    list of per-step Python snapshots."""
    assert len(cases) == len(values), "%s: %d cases, %d Coq values" % (label, len(cases), len(values))
    bad = []
    for c, v in zip(cases, values):
        exp = rc.pynorm(pyfn(c))
        got = rc.pynorm(rc.norm(v))
        if exp != got:
            for i, (x, y) in enumerate(zip(exp, got)):
                if x != y:
                    bad.append((c, i, x, y))
                    break
            else:
                bad.append((c, min(len(exp), len(got)), "length", (len(exp), len(got))))
    return len(cases), bad


def assert_no_mismatch(n, bad, label):
    assert n > 0
    assert not bad, "%s: %d of %d cases differ; first: case=%r step=%r python=%r coq=%r" % (
        label, len(bad), n, bad[0][0], bad[0][1], bad[0][2], bad[0][3])


# ---------------------------------------------------------------------------
# Coq results, computed once per session and shared by the tests and their
# mutation checks
# ---------------------------------------------------------------------------

_cache = {}


def _small_cases():
    return (rc.small_exhaustive() + rc.small_random(SEED, 300) + rc.small_cap_cases())


@pytest.fixture(scope="session")
def small_coq(coqc, min_flags, workdir):
    cases = _small_cases()
    text = rc.PRELUDE_MIN + "\n" + "\n".join(rc.r_small(*c) for c in cases) + "\n"
    return cases, rh.coq_values(coqc, min_flags, text, workdir, "small")


@pytest.fixture(scope="session")
def multi_coq(coqc, min_flags, workdir):
    out = {}
    for pr in (False, True):
        cases = rc.host_exhaustive(pr) + rc.host_random(SEED + 1, 300, pr) + rc.host_cap_cases(pr)
        text = rc.PRELUDE_MIN + "\n" + "\n".join(
            rc.r_multi(c[0], c[1], c[3], c[2], pr) for c in cases) + "\n"
        out[pr] = (cases, rh.coq_values(coqc, min_flags, text, workdir, "multi_%d" % pr))
    return out


def _guest_cases():
    base = rc.small_exhaustive()[:1500] + rc.small_random(SEED + 3, 200)
    rng = random.Random(SEED + 4)
    priced_cases = []
    for (P, a, b, n) in base[::3]:
        P2 = list(P)
        for _ in range(2):
            P2.insert(rng.randint(0, len(P2)), ("PAY",))
        priced_cases.append((P2, a, b, n))
    return base, priced_cases


@pytest.fixture(scope="session")
def guest_coq(coqc, min_flags, workdir):
    base, pcases = _guest_cases()
    t1 = rc.PRELUDE_MIN + "\n" + "\n".join(rc.r_gen(c[0], c[1], c[2], c[3], False) for c in base) + "\n"
    t2 = rc.PRELUDE_MIN + "\n" + "\n".join(rc.r_gen(c[0], c[1], c[2], c[3], True) for c in pcases) + "\n"
    return {
        False: (base, rh.coq_values(coqc, min_flags, t1, workdir, "gen")),
        True: (pcases, rh.coq_values(coqc, min_flags, t2, workdir, "pgen")),
    }


@pytest.fixture(scope="session")
def slot_coq(coqc, full_flags, workdir):
    cases = rc.slot_exhaustive() + rc.slot_random(SEED + 2, 300) + rc.slot_cap_cases()
    text = rc.PRELUDE_FULL + "\n" + "\n".join(rc.r_slot(c[0], c[1], c[2], c[3]) for c in cases) + "\n"
    return cases, rh.coq_values(coqc, full_flags, text, workdir, "slot")


UNIVERSAL_STRIDE, UNIVERSAL_K, UNIVERSAL_NREGS = 200, 15, 96


@pytest.fixture(scope="session")
def universal_coq(coqc, full_flags, workdir):
    cases = rc.universal_cases()
    text = rc.PRELUDE_FULL + "\n" + "\n".join(
        rc.r_universal(P, x, y, UNIVERSAL_STRIDE, UNIVERSAL_K, UNIVERSAL_NREGS)
        for (P, x, y) in cases) + "\n"
    return cases, rh.coq_values(coqc, full_flags, text, workdir, "universal")


# ---------------------------------------------------------------------------
# small machine
# ---------------------------------------------------------------------------


@coq
def test_small_machine_matches_coq_every_step(small_coq):
    cases, vals = small_coq
    n, bad = compare(cases, vals, lambda c: rc.py_small(*c), "small")
    assert n >= 4500
    assert_no_mismatch(n, bad, "small machine vs EarnedCore.v")


@coq
def test_small_machine_cap_cases_reach_the_cap(small_coq):
    """The fact-table-cap programs really end in a trap with 16 facts."""
    cases, vals = small_coq
    caps = [(c, v) for c, v in zip(cases, vals) if len(c[0]) in (21, 19) and c[0][0][0] == "CHECK"]
    assert caps
    c, v = caps[0]
    final = rc.norm(v[-1])
    assert final[5] and len(final[5]) == 16 and final[7] == 1, final  # 16 facts, trapped


@coq
def test_mutations_of_the_small_machine_are_caught(small_coq, monkeypatch):
    """The comparison is not vacuous: each of these deliberate changes to the
    Python machine makes it differ from Coq on the same cases."""
    cases, vals = small_coq
    allp = list(zip(cases, vals))
    sub = allp[::4] + allp[-4:]  # a quarter of the cases and the fact-table-cap cases
    cs, vs = [c for c, _ in sub], [v for _, v in sub]

    def mismatches():
        return compare(cs, vs, lambda c: rc.py_small(*c), "mutant")[1]

    assert not mismatches()
    with monkeypatch.context() as m:
        m.setattr(small, "FACT_CAP", 15)
        assert mismatches(), "cap 15 not detected"
    with monkeypatch.context() as m:
        m.setattr(small, "cost", lambda i: 0)
        assert mismatches(), "free instructions not detected"
    with monkeypatch.context() as m:
        orig = small.commit_ok
        m.setattr(small, "commit_ok", lambda k, p, c: (not k.err) and any(
            f[0] == p and f[1] == c for f in k.facts))  # ignores the version
        assert mismatches(), "version-blind commit not detected"
    with monkeypatch.context() as m:
        orig_w = small._write

        def no_bump(k, c, n, j):
            va, vb = k.va, k.vb
            orig_w(k, c, n, j)
            k.va, k.vb = va, vb
        m.setattr(small, "_write", no_bump)
        assert mismatches(), "version-free writes not detected"


# ---------------------------------------------------------------------------
# generic and priced guests, multi-register hosts
# ---------------------------------------------------------------------------


@coq
def test_generic_and_priced_guest_match_coq(guest_coq):
    g = priced.Guest(priced.CPROP, priced=False)
    cases, vals = guest_coq[False]
    n, bad = compare(cases, vals, lambda c: rc.py_guest(g, c[0], c[1], c[2], c[3]), "generic")
    assert_no_mismatch(n, bad, "generic guest vs EarnedGeneric.v")
    pg = priced.Guest(priced.CPROP, priced=True)
    cases, vals = guest_coq[True]
    n, bad = compare(cases, vals, lambda c: rc.py_guest(pg, c[0], c[1], c[2], c[3]), "priced guest")
    assert_no_mismatch(n, bad, "priced guest vs EarnedPriced.v")
    # PAY actually occurs and is paid for
    assert any(("PAY",) in c[0] for c in cases)


@coq
@pytest.mark.parametrize("priced_host", [False, True])
def test_multi_register_host_matches_coq(multi_coq, priced_host):
    cases, vals = multi_coq[priced_host]
    h = multi.Host(multi.SMALL, priced=priced_host)
    n, bad = compare(cases, vals,
                     lambda c: rc.py_host(h, c[0], c[1], c[3], c[2]),
                     "multi" + (" priced" if priced_host else ""))
    assert n >= 2300
    assert_no_mismatch(n, bad, "host vs " + ("EarnedMultiPriced.v" if priced_host else "EarnedMulti.v"))
    if priced_host:
        assert any(("PAY",) in c[0] for c in cases)


@coq
def test_host_registers_outside_the_window_stay_untouched(multi_coq):
    """The snapshot window (registers 0..5) hides nothing: the generated
    programs only name registers 0..4."""
    for pr in (False, True):
        cases, _ = multi_coq[pr]
        for (P, vs, nr, n) in cases:
            regs = {i[1] for i in P if i[0] in ("INC", "DEC")} | {i[2] for i in P if i[0] in ("CHECK", "COMMIT")}
            assert all(r < nr for r in regs), (P, nr)


# ---------------------------------------------------------------------------
# the host over PSlot, and U
# ---------------------------------------------------------------------------


@coq
def test_pslot_host_matches_coq(slot_coq):
    cases, vals = slot_coq
    h = multi.Host(multi.SLOT, priced=False)
    n, bad = compare(cases, vals, lambda c: rc.py_host(h, c[0], c[1], c[2], c[3]), "slot")
    assert n >= 2800
    assert_no_mismatch(n, bad, "PSlot host vs UniversalCodes.v / rlz_host_*")
    # the property is exercised both ways: some CHECK passes, some traps
    finals = [rc.norm(v[-1]) for v in vals]
    assert any(f[3] for f in finals) and any(f[5] for f in finals)


@coq
def test_universal_program_matches_coq_on_tiny_guests(universal_coq):
    cases, vals = universal_coq
    n, bad = compare(
        cases, vals,
        lambda c: rc.py_universal(c[0], c[1], c[2], UNIVERSAL_STRIDE, UNIVERSAL_K, UNIVERSAL_NREGS),
        "universal")
    assert n >= 70
    assert_no_mismatch(n, bad, "U on tiny guests vs rlz_host_run_prog rlz_host_program")


# ---------------------------------------------------------------------------
# tables: costs, caps, codes, program text
# ---------------------------------------------------------------------------

TABLE_PRELUDE = rc.PRELUDE_MIN + r"""
Compute (map E.cost [E.INC E.CA; E.DEC E.CA 3; E.HALT; E.CHECK E.PZero E.CB;
                     E.COMMIT E.PEven E.CA; E.CERTIFY]).
Compute (map M.cost [M.INC 7; M.DEC 7 3; M.HALT; @M.CHECK E.prop E.PZero 4;
                     @M.COMMIT E.prop E.PEven 4; M.CERTIFY]).
Compute (map PM.pu_cost [PM.INC 7; PM.DEC 7 3; PM.HALT; @PM.CHECK E.prop E.PZero 4;
                     @PM.COMMIT E.prop E.PEven 4; PM.CERTIFY; PM.PAY]).
Compute (map G.cost [@G.INC G.cprop G.CA; @G.DEC G.cprop G.CB 3; @G.HALT G.cprop;
                     @G.CHECK G.cprop G.PZero G.CA; @G.COMMIT G.cprop G.PZero G.CA; @G.CERTIFY G.cprop]).
Compute (map PG.pr_cost [@PG.INC G.cprop G.CA; @PG.DEC G.cprop G.CB 3; @PG.HALT G.cprop;
                     @PG.CHECK G.cprop G.PZero G.CA; @PG.COMMIT G.cprop G.PZero G.CA;
                     @PG.CERTIFY G.cprop; @PG.PAY G.cprop]).
Compute (E.fact_cap, M.fact_cap, PM.pu_fact_cap).
"""


@coq
def test_cost_and_cap_tables_equal_coq(coqc, min_flags, workdir):
    vals = rh.coq_values(coqc, min_flags, TABLE_PRELUDE, workdir, "tables_cost")
    costs_small, costs_multi, costs_pm, costs_g, costs_pg, caps = [rc.norm(v) for v in vals]
    S = [("INC", 0), ("DEC", 0, 3), ("HALT",), ("CHECK", ("PZero",), 1), ("COMMIT", ("PEven",), 0), ("CERTIFY",)]
    assert costs_small == [small.cost(i) for i in S]
    assert costs_multi == [multi.cost(i) for i in S]
    assert costs_pm == [multi.cost(i) for i in S] + [multi.cost(("PAY",))]
    assert costs_g == [priced.cost(i) for i in S]
    assert costs_pg == [priced.cost(i) for i in S] + [priced.cost(("PAY",))]
    assert caps == (small.FACT_CAP, multi.FACT_CAP, multi.FACT_CAP) == (16, 16, 16)


CODE_PRELUDE = rc.PRELUDE_MIN + r"""
Require Minimal.UniversalCodes.
Module UC := Minimal.UniversalCodes.
Compute (map (fun p => UC.pair (fst p) (snd p))
           (list_prod (seq 0 6) (seq 0 6))).
Compute (map UC.unpair (seq 0 130)).
Compute (map UC.pcode [E.PZero; E.PEven; E.PGe 0; E.PGe 5]).
Compute (map UC.icode [E.INC E.CA; E.INC E.CB; E.DEC E.CA 1; E.DEC E.CB 3; E.HALT;
                       E.CHECK E.PZero E.CA; E.CHECK (E.PGe 2) E.CB; E.COMMIT E.PEven E.CB; E.CERTIFY]).
Compute (map UC.idecode (seq 0 200)).
Compute (map UC.prog_code [[]; [E.HALT]; [E.INC E.CA; E.HALT]; [E.INC E.CA; E.INC E.CB; E.HALT];
                           [E.INC E.CB; E.INC E.CB]]).
Compute (map (fun x => UC.heval UC.PSlot x) (seq 0 70)).
Compute (map G.encode [[]; [0]; [3]; [1; 2]; [2; 0; 1]]).
Compute (map G.decode (seq 0 70)).
"""


def _py_idecode_tuple(x):
    i = codes.idecode(x)
    return None if i is None else i


@coq
def test_code_tables_equal_coq(coqc, min_flags, workdir):
    # UniversalCodes.v needs only the standard library (and minimal/)
    d = workdir / "codes_tree"
    d.mkdir(exist_ok=True)
    flags = ["-Q", str(d), "Minimal"]
    for f in ("EarnedCore", "EarnedGeneric", "EarnedMulti", "EarnedPriced", "EarnedMultiPriced", "UniversalCodes"):
        src = rh.SRC_ROOT / "minimal" / (f + ".v")
        dst = d / (f + ".v")
        dst.write_bytes(src.read_bytes())
        if not (d / (f + ".vo")).exists():
            rh.run_coqc(coqc, flags, dst)
    vals = rh.coq_values(coqc, flags, CODE_PRELUDE, workdir, "tables_codes")
    pairs, unp, pcodes, icodes, idecs, pcs, hevals, encs, decs = vals
    assert rc.norm(pairs) == [codes.pair(m, n) for m, n in itertools.product(range(6), range(6))]
    assert [rc.norm(x) for x in unp] == [codes.unpair(x) for x in range(130)]
    assert rc.norm(pcodes) == [codes.pcode(p) for p in (("PZero",), ("PEven",), ("PGe", 0), ("PGe", 5))]
    ins = [("INC", 0), ("INC", 1), ("DEC", 0, 1), ("DEC", 1, 3), ("HALT",), ("CHECK", ("PZero",), 0),
           ("CHECK", ("PGe", 2), 1), ("COMMIT", ("PEven",), 1), ("CERTIFY",)]
    assert rc.norm(icodes) == [codes.icode(i) for i in ins]
    # idecode: Some instruction or None; render Coq's result as a Python instruction
    assert len(idecs) == 200
    for x, v in enumerate(idecs):
        assert rc.coq_instr_to_py(v) == _py_idecode_tuple(x), x
    progs = [[], [("HALT",)], [("INC", 0), ("HALT",)], [("INC", 0), ("INC", 1), ("HALT",)], [("INC", 1), ("INC", 1)]]
    assert rc.norm(pcs) == [codes.prog_code(P) for P in progs]
    assert [int(bool(x)) for x in rc.norm(hevals)] == [int(codes.heval(x)) for x in range(70)]
    assert rc.norm(encs) == [codes.encode(l) for l in ([], [0], [3], [1, 2], [2, 0, 1])]
    assert [rc.norm(x) for x in decs] == [codes.decode(x) for x in range(70)]


@coq
def test_layout_and_program_tables_equal_coq(coqc, full_flags, workdir):
    """thiele_small/data/programs.json is what scripts/realize_gen_programs.py
    prints from Coq today, and coq/kernel/foundation/RealizePrograms.v is the
    file it writes (so the Python tables and the Coq literals are U and U_P)."""
    import subprocess
    out = workdir / "gen"
    proc = subprocess.run(
        [sys.executable, str(REPO / "scripts" / "realize_gen_programs.py"), "--coqc", coqc,
         "--flags-json", json.dumps([str(f) for f in full_flags]), "--out-dir", str(out)],
        capture_output=True, text=True, timeout=1200)
    assert proc.returncode == 0, proc.stdout + proc.stderr
    new = json.loads((out / "programs.json").read_text(encoding="utf-8"))
    old = json.loads((REPO / "thiele_small" / "data" / "programs.json").read_text(encoding="utf-8"))
    assert new == old
    assert (out / "RealizePrograms.v").read_text(encoding="utf-8") == \
        (REPO / "coq" / "kernel" / "foundation" / "RealizePrograms.v").read_text(encoding="utf-8")
    assert universal.LAYOUT == new["layout"]


# ---------------------------------------------------------------------------
# the universal checker (URun) and the priced host
# ---------------------------------------------------------------------------

PRICED_PRELUDE = rc.PRELUDE_FULL + r"""
Require Kernel.RealizePriced.
Module RP := Kernel.RealizePriced.
(* a prime stream Coq can evaluate: the search of RealizePriced.v with a small
   fuel, proved equal to qs wherever the gap to the next prime is below 100
   (rlz_nxtprime_with_eq) *)
Definition tqs : nat -> nat := RP.rlz_qs_with (RP.rlz_nxtprime_with 100).
Definition pdf (f : @PM.pu_fact UPC.pu_hprop) := (0, 0, PM.f_reg f, PM.f_ver f).
Definition snapPS (nr : nat) (s : @PM.pu_state UPC.pu_hprop) :=
  let k := PM.core_of s in
  (PM.pc k, map (PM.vals k) (seq 0 nr), map (PM.vers k) (seq 0 nr), map pdf (PM.facts k),
   option_map pdf (PM.chan k), b2n (PM.err k), PM.mu s, b2n (PM.cert s)).
Fixpoint trPS (nr n : nat) (P : list (@PM.pu_instr UPC.pu_hprop)) (s : @PM.pu_state UPC.pu_hprop) :=
  match n with 0 => [snapPS nr s]
  | S m => snapPS nr s :: trPS nr m P (PM.pu_step UPC.pu_hprop_eqb (RP.rlz_pu_heval_with tqs) P s) end.
Fixpoint chkUP (nr stride k : nat) (s : @PM.pu_state UPC.pu_hprop) :=
  match k with 0 => []
  | S k' => let s' := RP.rlz_phost_run_prog stride RP.rlz_phost_program s in
            snapPS nr s' :: chkUP nr stride k' s' end.
"""


def _pslot_instr_coq(i):
    op = i[0]
    if op == "INC":
        return "PM.INC %d" % i[1]
    if op == "DEC":
        return "PM.DEC %d %d" % (i[1], i[2])
    if op == "HALT":
        return "PM.HALT"
    if op == "CHECK":
        return "PM.CHECK UPC.PSlot %d" % i[2]
    if op == "COMMIT":
        return "PM.COMMIT UPC.PSlot %d" % i[2]
    if op == "CERTIFY":
        return "PM.CERTIFY"
    return "PM.PAY"


def _claim_values():
    """PSlot register values coding a UBase claim about a number: pair
    (pu_pcode p) v. (A URun claim would be coded by 2^(2r+1) times an odd
    number, which Coq cannot hold; it is tested in the extracted runner.)"""
    vals = [0]
    for q in (("PZero",), ("PEven",), ("PGe", 2)):
        for v in (0, 1, 2, 3, 4):
            vals.append(codes.pair(codes.pu_pcode(("UBase", q)), v))
    return sorted(set(vals))


def _priced_slot_cases():
    xs = _claim_values()
    rng = random.Random(SEED + 7)
    cases = []
    chain = [("CHECK", ("PSlot",), 0), ("COMMIT", ("PSlot",), 0), ("CERTIFY",)]
    for x in xs:
        cases.append((chain, {0: x}, 5, 3))
        cases.append(([("CHECK", ("PSlot",), 0), ("PAY",), ("COMMIT", ("PSlot",), 0), ("CERTIFY",)],
                      {0: x}, 7, 3))
    for _ in range(150):
        ln = rng.randint(3, 9)
        al = ([("INC", r) for r in range(3)] + [("DEC", r, j) for r in range(3) for j in range(1, ln + 2)]
              + [("HALT",), ("CERTIFY",), ("PAY",)]
              + [("CHECK", ("PSlot",), r) for r in range(3)] + [("COMMIT", ("PSlot",), r) for r in range(3)])
        P = [rng.choice(al) for _ in range(ln)]
        vs = {r: rng.choice(xs) for r in range(3)}
        cases.append((P, vs, 25, 3))
    return cases


@pytest.fixture(scope="session")
def priced_slot_coq(coqc, full_flags, workdir):
    cases = _priced_slot_cases()
    lines = []
    for (P, vs, n, nr) in cases:
        regl = rc.coq_list([str(vs.get(r, 0)) for r in range(max(vs) + 1 if vs else 0)])
        lines.append("Compute (trPS %d %d %s (@PM.pu_start UPC.pu_hprop (regs %s)))." % (
            nr, n, rc.coq_list([_pslot_instr_coq(i) for i in P]), regl))
    return cases, rh.coq_values(coqc, full_flags, PRICED_PRELUDE + "\n" + "\n".join(lines) + "\n",
                                workdir, "priced_slot")


@coq
def test_priced_pslot_host_with_urun_routines_matches_coq(priced_slot_coq):
    """The priced host over PSlot, whose checker is the universal checker
    cg_ueval: registers hold claims about numbers, including URun routines
    whose run needs the prime stream (qs) and the counter-program interpreter."""
    cases, vals = priced_slot_coq
    h = multi.Host(multi.PSLOT, priced=True)
    n, bad = compare(cases, vals, lambda c: rc.py_host(h, c[0], c[1], c[2], c[3]), "priced slot")
    assert n >= 100
    assert_no_mismatch(n, bad, "priced PSlot host vs rlz_pu_heval_with / pu_heval")
    # some CERTIFY on a true claim succeeds in the data, some trap
    finals = [rc.norm(v[-1]) for v in vals]
    assert any(f[7] for f in finals), "no case raised the flag"
    assert any(f[5] for f in finals), "no case trapped"


def _routines():
    """Routines (cg_renc ig R xS xB xT m) with R of at most two INC
    instructions, whose codes Coq can hold in unary."""
    out = []
    for ig in (0, 1):
        for R in ([], [("INC", 0)], [("INC", 1)], [("INC", 0), ("INC", 1)], [("INC", 0), ("INC", 0)]):
            for (xS, xB, xT, m) in ((0, 0, 0, 1), (0, 1, 0, 2), (0, 1, 1, 2), (0, 0, 1, 2), (0, 2, 1, 3)):
                r = codes.cg_renc(ig, R, xS, xB, xT, m)
                if r < 200000:
                    out.append(r)
    return sorted(set(out))


@coq
def test_universal_checker_agrees_on_urun_routines(coqc, full_flags, workdir):
    """cg_ueval of the Python realisation equals the Coq checker built on the
    computable prime stream (rlz_ueval_with, proved equal to cg_ueval), on URun
    routines (the counter-program interpreter and the prime stream) and on UBase
    claims. The routines have at most two INC instructions: Coq must hold their
    codes in unary."""
    rs = _routines()
    vs = (0, 1, 2, 3, 7, 9, 21, 27, 49, 63, 81, 147, 343)
    pairs = [(r, v) for r in rs for v in vs]
    assert len(rs) >= 15
    items = ["(RP.RURun %d, %d)" % (r, v) for (r, v) in pairs]
    for q in ("RP.RUBase G.PZero", "RP.RUBase G.PEven", "RP.RUBase (G.PGe 2)"):
        for v in (0, 1, 2, 5):
            items.append("(%s, %d)" % (q, v))
    expected = [codes.cg_ueval(("URun", r), v) for (r, v) in pairs]
    for q in (("PZero",), ("PEven",), ("PGe", 2)):
        for v in (0, 1, 2, 5):
            expected.append(codes.cg_ueval(("UBase", q), v))
    lines = ["Compute (map (fun pv => RP.rlz_ueval_with tqs (fst pv) (snd pv)) %s)." % rc.coq_list(items)]
    vals = rh.coq_values(coqc, full_flags, PRICED_PRELUDE + "\n" + "\n".join(lines) + "\n", workdir, "ueval")
    got = [bool(b) for b in vals[0]]
    assert got == expected
    assert any(expected) and not all(expected), "the cases do not exercise both answers"


# ---------------------------------------------------------------------------
# U_P on tiny priced guests
# ---------------------------------------------------------------------------

PU_STRIDE, PU_K, PU_NREGS = 200, 12, 96


def _pu_guest_cases():
    out = []
    al = [("INC", 0), ("INC", 1), ("HALT",)]
    for ln in (1, 2, 3):
        for P in itertools.product(al, repeat=ln):
            if codes.pu_prog_code(P).bit_length() > 12:
                continue
            for (x, y) in ((0, 0), (2, 1)):
                out.append((list(P), x, y))
    return out


def _coq_pguest(i):
    # rlz_pinstr constructors of RealizePriced.v
    op = i[0]
    c = "RP.RCA" if (len(i) > 1 and i[1] == 0) else "RP.RCB"
    if op == "INC":
        return "RP.PINC %s" % c
    if op == "HALT":
        return "RP.PHALT"
    raise ValueError(i)


@pytest.fixture(scope="session")
def pu_coq(coqc, full_flags, workdir):
    cases = _pu_guest_cases()
    lines = []
    for (P, x, y) in cases:
        st = "(RP.rlz_phost_load %s %d %d)" % (rc.coq_list([_coq_pguest(i) for i in P]), x, y)
        lines.append("Compute (snapPS %d %s :: chkUP %d %d %d %s)." % (PU_NREGS, st, PU_NREGS, PU_STRIDE, PU_K, st))
    return cases, rh.coq_values(coqc, full_flags, PRICED_PRELUDE + "\n" + "\n".join(lines) + "\n", workdir, "pu")


@coq
def test_priced_universal_program_matches_coq_on_tiny_guests(pu_coq):
    cases, vals = pu_coq

    def py(c):
        P, x, y = c
        s = universal.pu_hload(P, x, y)
        out = [universal.HOST_P.snapshot(s, PU_NREGS)]
        for _ in range(PU_K):
            s = universal.HOST_P.run_prog(PU_STRIDE, universal.U_P, s)
            out.append(universal.HOST_P.snapshot(s, PU_NREGS))
        return out
    n, bad = compare(cases, vals, py, "U_P")
    assert n >= 10
    assert_no_mismatch(n, bad, "U_P on tiny guests vs rlz_phost_run_prog rlz_phost_program")


@coq
def test_realize_files_compile_axiom_free(coqc, full_flags, workdir):
    """Every theorem of Realize.v and RealizePriced.v is closed under the
    global context."""
    text = """Require Import Kernel.Realize Kernel.RealizePriced Kernel.RealizePrograms.
Print Assumptions Kernel.Realize.rlz_small_halting_correspondence.
Print Assumptions Kernel.Realize.rlz_small_mu_conservation_trace.
Print Assumptions Kernel.Realize.rlz_host_at_is.
Print Assumptions Kernel.Realize.rlz_host_program_is.
Print Assumptions Kernel.RealizePriced.rlz_qs_eq.
Print Assumptions Kernel.RealizePriced.rlz_ueval_eq.
Print Assumptions Kernel.RealizePriced.rlz_pu_heval_eq.
Print Assumptions Kernel.RealizePriced.rlz_phost_load_eq.
Print Assumptions Kernel.RealizePriced.rlz_phost_run_prog_eq.
Print Assumptions Kernel.RealizePriced.rlz_phost_at_eq.
Print Assumptions Kernel.RealizePriced.rlz_pguest_run_prog_eq.
Print Assumptions Kernel.RealizePrograms.rlz_phost_program_is.
"""
    v = workdir / "assumptions.v"
    v.write_text(text, encoding="utf-8")
    out = rh.run_coqc(coqc, full_flags, v)
    assert out.count("Closed under the global context") == text.count("Print Assumptions"), out
    assert "Axioms" not in out


# ---------------------------------------------------------------------------
# U against its guest, in Python alone: the statements of UniversalRun.v
# ---------------------------------------------------------------------------


def _head_states(P, x, y, limit):
    """The host states at U's loop head (pc 1), in order, until the host
    halts or limit steps have run."""
    h = universal.HOST
    s = universal.hload(P, x, y)
    heads = []
    n = 0
    while True:
        if s.pc == 1 and not s.err:
            heads.append(s.copy())
        if h.halted(universal.U, s) or n >= limit:
            break
        h._step_inplace(universal.U, s)
        n += 1
    return s, heads, n, h.halted(universal.U, s)


def _guest_trajectory(P, x, y, limit):
    gs = [small.start(x, y)]
    while len(gs) <= limit and not small.halted(P, gs[-1]):
        gs.append(small.step(P, gs[-1]))
    return gs


def _tiny_guests():
    return [(P, x, y) for (P, x, y) in rc.universal_cases()]


@pytest.mark.parametrize("case", _tiny_guests(), ids=lambda c: "%s-%d-%d" % ("".join(i[0][0] for i in c[0]), c[1], c[2]))
def test_U_simulates_its_guest_exactly(case):
    """For every tiny guest P and start (x, y), the statements of
    UniversalRun.v hold of the Python runs:
      * the k-th visit of U's loop head shows the guest after k steps: the
        guest counters are in registers RA and RB, the guest pc in GPC, the
        ledgers and flags are equal (U_simulation, rw_greg, rw_gpc, rw_mu,
        rw_cert, with no facts so the slot registers are all 0);
      * the host halts exactly when the guest halts (universal_halting);
      * at the halt the host registers RA, RB, the trap latch, the ledger and
        the flag equal the guest's (universal_output, universal_flag_iff,
        universal_ledger_exact: at matching points the ledgers are equal and
        every host ledger lies between the guest ledgers at m and m + 1)."""
    P, x, y = case
    gs = _guest_trajectory(P, x, y, 40)
    guest_halts = small.halted(P, gs[-1])
    s, heads, n, host_halts = _head_states(P, x, y, 3_000_000)
    assert host_halts == guest_halts  # the guest halts iff the host halts
    assert guest_halts, "guest does not halt within 40 steps"
    # the loop head is visited once per guest step, plus the visit at which
    # the guest stops
    assert len(heads) == len(gs)
    for k, (hs, g) in enumerate(zip(heads, gs)):
        assert hs.val(universal.RA) == g.ca and hs.val(universal.RB) == g.cb, k
        assert hs.val(universal.GPC) == g.pc, k
        assert hs.mu == g.mu and hs.cert == g.cert and hs.err == g.err, k
        assert hs.facts == [] and g.facts == []  # no record instruction
    final = gs[-1]
    assert s.val(universal.RA) == final.ca and s.val(universal.RB) == final.cb
    assert s.err == final.err and s.mu == final.mu and s.cert == final.cert
    # the ledger relation of universal_ledger_exact: at every host step the
    # host ledger lies between two consecutive guest ledgers
    assert s.mu == 0 and final.mu == 0


def test_the_loop_head_visit_count_is_one_per_guest_step_on_a_longer_guest():
    P = [("INC", 0), ("INC", 0), ("INC", 1), ("HALT",)]
    gs = _guest_trajectory(P, 0, 0, 40)
    s, heads, n, host_halts = _head_states(P, 0, 0, 3_000_000)
    assert host_halts and len(heads) == len(gs) == 4
    assert (s.val(universal.RA), s.val(universal.RB)) == (2, 1)


def test_U_P_simulates_its_guest_on_tiny_priced_guests():
    """The priced program U_P on the priced guest machine: the same relation
    at U_P's loop head."""
    h = universal.HOST_P
    for (P, x, y) in (([("INC", 0), ("HALT",)], 0, 0), ([("INC", 0), ("INC", 1), ("INC", 0), ("HALT",)], 2, 1),
                      ([("HALT",)], 1, 1)):
        gs = [universal.GUEST_P.start(x, y)]
        while not universal.GUEST_P.halted(P, gs[-1]):
            gs.append(universal.GUEST_P.step(P, gs[-1]))
        s = universal.pu_hload(P, x, y)
        heads = []
        n = 0
        while True:
            if s.pc == 1 and not s.err:
                heads.append(s.copy())
            if h.halted(universal.U_P, s) or n > 3_000_000:
                break
            h._step_inplace(universal.U_P, s)
            n += 1
        assert h.halted(universal.U_P, s)
        assert len(heads) == len(gs)
        for hs, g in zip(heads, gs):
            assert (hs.val(universal.RA), hs.val(universal.RB), hs.val(universal.GPC)) == (g.ca, g.cb, g.pc)
            assert hs.mu == g.mu and hs.cert == g.cert
        assert (s.val(universal.RA), s.val(universal.RB), s.mu, s.cert, s.err) == \
            (gs[-1].ca, gs[-1].cb, gs[-1].mu, gs[-1].cert, gs[-1].err)


# ---------------------------------------------------------------------------
# properties of the Python realisation that need no Coq
# ---------------------------------------------------------------------------


def test_codes_round_trip():
    for m in range(8):
        for n in range(8):
            assert codes.unpair(codes.pair(m, n)) == (m, n)
    assert codes.unpair(0) is None
    for l in ([], [0], [3, 1], [2, 0, 5], [0, 0, 0]):
        assert codes.decode(codes.encode(l)) == l
    for P in ([("INC", 0), ("DEC", 1, 3), ("HALT",), ("CHECK", ("PGe", 4), 1), ("COMMIT", ("PEven",), 0),
               ("CERTIFY",)],):
        for i in P:
            assert codes.idecode(codes.icode(i)) == i
    for i in (("PAY",), ("CHECK", ("UBase", ("PGe", 3)), 1), ("COMMIT", ("URun", 9), 0)):
        assert codes.pu_idecode(codes.pu_icode(i)) == i


def test_program_data_is_U_with_the_expected_instruction_set():
    assert len(universal.U) == len(universal.U_P) - 7
    ops = {i[0] for i in universal.U}
    assert ops <= {"INC", "DEC", "HALT", "CHECK", "COMMIT", "CERTIFY"}
    assert "PAY" in {i[0] for i in universal.U_P}


def test_trapped_machine_is_inert_but_pays():
    """EarnedCore.v: a trapped core is left alone by every instruction and
    the ledger still moves (exec charges the cost of the instruction)."""
    s = small.start(0, 0)
    s = small.exec_(s, ("COMMIT", ("PZero",), 0))  # no fact: traps
    assert s.err and s.mu == 1
    t = small.exec_(s, ("CERTIFY",))
    assert t.err and t.mu == 2 and not t.cert and t.pc == s.pc
    assert small.halted([("INC", 0)], s)


def test_python_host_start_is_clean():
    h = multi.Host(multi.SMALL)
    s = h.start({0: 5})
    assert s.facts == [] and s.chan is None and not s.cert and not s.err and s.mu == 0 and s.pc == 1
    assert s.val(0) == 5 and s.ver(0) == 0
