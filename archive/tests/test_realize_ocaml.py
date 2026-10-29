"""The Python realisation against the machines EXTRACTED from Coq.

ocaml/RealizeExtract.v extracts the small machine, the
multi-register host with and without PAY, the programs U and U_P, their
loaders, and the PSlot evaluation (with the universal checker and the prime
stream) to OCaml. This test extracts them, compiles the extraction with the
driver ocaml/realize_driver.ml, runs the same programs on the extracted code
and on thiele_small/, and compares every state of every step as lists of
integers (thiele_small/flat.py gives the layout).

The test needs coqc 8.18 with the project compiled (see tests/test_realize.py
for THIELE_COQ_BUILD and THIELE_UNDEC), and OCaml: ocamlfind, ocamlopt and the
zarith library (Ubuntu: apt install ocaml libzarith-ocaml-dev; on the
Windows development PC the opam switch under %LOCALAPPDATA%/opam/default is
found without touching PATH). A missing OCaml toolchain fails the test when
CI=true, under GitHub Actions, with --strict-backends and with
THIELE_STRICT_BACKENDS, so a skip cannot hide a lost install; the python job
of ci.yml installs OCaml. Without CI=true the tests skip with the reason.

Bounds: the same exhaustive-small and seeded random program sets as the Coq
comparison, plus U and U_P run on guests to their stop, up to a program code
of 2^19 (about 26 million host steps) here and 2^26 in the CI job
realize-universal.
"""

from __future__ import annotations

import os
import random
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

TESTS = Path(__file__).resolve().parent
REPO = TESTS.parent
sys.path.insert(0, str(TESTS))
sys.path.insert(0, str(REPO))

import realize_cases as rc  # noqa: E402
import realize_harness as rh  # noqa: E402
from thiele_small import codes, flat, multi, priced, small, universal  # noqa: E402

SEED = 20261005
LIMIT_R = 1 << 16

# Register values here are written in decimal and some have hundreds of thousands
# of digits (a URun claim is 2^(2r+1) times an odd number).
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

coq = pytest.mark.coq


def _strict(config) -> bool:
    return bool(
        os.environ.get("GITHUB_ACTIONS")
        or config.getoption("--strict-backends", default=False)
        or os.environ.get("THIELE_STRICT_BACKENDS", "0").strip().lower() in {"1", "true", "yes", "on"}
    )


def _skip_or_fail(config, why, toolchain=False):
    """A missing OCaml toolchain fails whenever CI=true (every automated run sets
    it), so a skip cannot hide a lost install; other missing pieces fail under
    the strict settings only."""
    ci = os.environ.get("CI", "").strip().lower() in {"1", "true", "yes", "on"}
    if _strict(config) or (toolchain and ci):
        pytest.fail(why)
    pytest.skip(why)


def _opam_dirs():
    """The tool directories of the default opam switch on Windows (where
    ocamlfind is not on PATH): the switch's bin and the mingw runtime."""
    base = os.environ.get("LOCALAPPDATA")
    if not base:
        return []
    root = Path(base) / "opam"
    dirs = [root / "default" / "bin",
            root / ".cygwin" / "root" / "usr" / "x86_64-w64-mingw32" / "sys-root" / "mingw" / "bin"]
    return [str(d) for d in dirs if d.is_dir()]


def _ocaml_env():
    """The environment to run the OCaml tools in: the one given, unless that has no
    working ocamlfind with ocamlopt and zarith and the opam switch of the Windows
    development PC does (a second ocamlfind there belongs to Coq Platform, which
    ships no native compiler)."""
    env = dict(os.environ)
    if _ocaml_missing(env):
        extra = _opam_dirs()
        if extra:
            alt = dict(env, PATH=os.pathsep.join(extra + [env.get("PATH", "")]))
            if not _ocaml_missing(alt):
                return alt
    return env


def _ocamlfind(env):
    """The ocamlfind this environment's PATH names, as a full path (Windows looks
    a bare program name up on the PATH of this process, not of env)."""
    return shutil.which("ocamlfind", path=env.get("PATH"))


def _ocaml_missing(env):
    ocamlfind = _ocamlfind(env)
    if not ocamlfind:
        return "ocamlfind not installed (apt install ocaml ocaml-findlib libzarith-ocaml-dev)"
    r = subprocess.run([ocamlfind, "query", "zarith"], capture_output=True, text=True, env=env)
    if r.returncode != 0:
        return "the OCaml library zarith is not installed (apt install libzarith-ocaml-dev)"
    r = subprocess.run([ocamlfind, "ocamlopt", "-version"], capture_output=True, text=True, env=env)
    if r.returncode != 0:
        return "ocamlopt is not available (apt install ocaml)"
    return ""


@pytest.fixture(scope="session")
def runner(request, tmp_path_factory):
    env = _ocaml_env()
    why = _ocaml_missing(env)
    if why:
        _skip_or_fail(request.config, why, toolchain=True)
    coqc = rh.find_coqc()
    if not coqc:
        _skip_or_fail(request.config, "coqc 8.18 not found (set THIELE_COQC)")
    flags, why = rh.prebuilt_flags()
    if flags is None:
        _skip_or_fail(request.config, why)
    d = tmp_path_factory.mktemp("realize_ocaml")
    src = REPO / "ocaml" / "RealizeExtract.v"
    shutil.copyfile(src, d / "RealizeExtract.v")
    # extraction writes realize_extracted.ml and .mli into the working directory
    rh.run_coqc(coqc, flags, d / "RealizeExtract.v")
    for f in ("realize_extracted.ml", "realize_extracted.mli"):
        assert (d / f).exists(), f
    shutil.copyfile(REPO / "ocaml" / "realize_driver.ml", d / "realize_driver.ml")
    proc = subprocess.run(
        [_ocamlfind(env), "ocamlopt", "-package", "zarith", "-linkpkg",
         "realize_extracted.mli", "realize_extracted.ml", "realize_driver.ml", "-o", "realize_driver"],
        cwd=str(d), capture_output=True, text=True, env=env)
    assert proc.returncode == 0, proc.stdout + proc.stderr
    exe = d / ("realize_driver.exe" if (d / "realize_driver.exe").exists() else "realize_driver")

    def run(tokens, timeout=1800, extra_env=None):
        text = " ".join(str(t) for t in tokens)
        p = subprocess.run([str(exe)], input=text, capture_output=True, text=True, timeout=timeout,
                           env={**env, **(extra_env or {})})
        assert p.returncode == 0, p.stderr[-2000:]
        blocks, cur = [], []
        for line in p.stdout.splitlines():
            if line == "END":
                blocks.append(cur)
                cur = []
            else:
                cur.append(line)
        assert not cur
        return blocks
    run.exe = exe
    return run


def ints(line):
    return [int(x) for x in line.split()]


def _check_blocks(cases, blocks, expected_fn, label):
    assert len(blocks) == len(cases), (label, len(blocks), len(cases))
    bad = []
    for c, b in zip(cases, blocks):
        exp = expected_fn(c)
        got = [ints(l) for l in b]
        if exp != got:
            for i, (x, y) in enumerate(zip(exp, got)):
                if x != y:
                    bad.append((c, i, x, y))
                    break
            else:
                bad.append((c, "length", len(exp), len(got)))
    assert not bad, "%s: %d of %d differ; first %r" % (label, len(bad), len(cases), bad[0])


# ---------------------------------------------------------------------------


@coq
def test_extracted_small_machine_matches_python(runner):
    cases = rc.small_exhaustive()[::3] + rc.small_random(SEED, 300) + rc.small_cap_cases()
    toks = []
    for (P, a, b, n) in cases:
        toks += ["small", n, a, b] + flat.prog_tokens(P)

    def exp(c):
        P, a, b, n = c
        s = small.start(a, b)
        out = [flat.flat_small(s)]
        for _ in range(n):
            s = small.step(P, s)
            out.append(flat.flat_small(s))
        return out
    _check_blocks(cases, runner(toks), exp, "small")


@coq
@pytest.mark.parametrize("priced_host", [False, True])
def test_extracted_multi_register_host_matches_python(runner, priced_host):
    cases = (rc.host_exhaustive(priced_host)[::2] + rc.host_random(SEED + 1, 300, priced_host)
             + rc.host_cap_cases(priced_host))
    toks = []
    for (P, vs, nr, n) in cases:
        toks += ["pmulti" if priced_host else "multi", n, nr] + flat.regs_tokens(vs) + flat.prog_tokens(P, True)
    h = multi.Host(multi.SMALL, priced=priced_host)

    def exp(c):
        P, vs, nr, n = c
        s = h.start(vs)
        out = [flat.flat_host(h, s, nr)]
        for _ in range(n):
            s = h.step(P, s)
            out.append(flat.flat_host(h, s, nr))
        return out
    _check_blocks(cases, runner(toks), exp, "multi")


@coq
def test_extracted_pslot_hosts_match_python(runner):
    cases = rc.slot_exhaustive()[::2] + rc.slot_random(SEED + 2, 300) + rc.slot_cap_cases()
    toks = []
    for (P, vs, n, nr) in cases:
        toks += ["slot", n, nr] + flat.regs_tokens(vs) + flat.prog_tokens(P, True)
    h = multi.Host(multi.SLOT, priced=False)

    def exp(c):
        P, vs, n, nr = c
        s = h.start(vs)
        out = [flat.flat_host(h, s, nr)]
        for _ in range(n):
            s = h.step(P, s)
            out.append(flat.flat_host(h, s, nr))
        return out
    _check_blocks(cases, runner(toks), exp, "slot")


def _urun_claim_values(rng):
    """PSlot register values coding claims about numbers, UBase and URun
    (the URun values are 2^(2r+1) times an odd number: only the extracted code
    can hold them)."""
    xs = [0]
    for q in (("PZero",), ("PEven",), ("PGe", 2)):
        for v in (0, 1, 2, 3, 4):
            xs.append(codes.pair(codes.pu_pcode(("UBase", q)), v))
    routines = []
    for ig in (0, 1):
        for R in ([], [("INC", 0)], [("INC", 1)], [("INC", 0), ("INC", 1)], [("INC", 0), ("INC", 0)]):
            for (xS, xB, xT, m) in ((0, 0, 0, 1), (0, 1, 0, 2), (0, 1, 1, 2), (0, 0, 1, 2), (0, 2, 1, 3)):
                r = codes.cg_renc(ig, R, xS, xB, xT, m)
                # The register holds 2^(2r+1) times an odd number, so r must be
                # a number a machine can write down: a routine with a DEC has
                # r near 2^(2^38), one with two INC instructions r near 2^520; and unpair takes time proportional to r times the length of the register.
                if r < LIMIT_R:
                    routines.append(r)
    routines = sorted(set(routines))
    for r in routines:
        for v in (0, 1, 3, 9, 27, 49, 3 * 7 * 13, 3 ** 4):
            xs.append(codes.pair(codes.pu_pcode(("URun", r)), v))
    return xs


@coq
def test_extracted_priced_pslot_host_with_urun_routines_matches_python(runner):
    rng = random.Random(SEED + 9)
    xs = _urun_claim_values(rng)
    cases = []
    chain = [("CHECK", ("PSlot",), 0), ("COMMIT", ("PSlot",), 0), ("CERTIFY",)]
    for x in xs:
        cases.append((chain, {0: x}, 5, 3))
    for _ in range(300):
        ln = rng.randint(3, 10)
        al = ([("INC", r) for r in range(3)] + [("DEC", r, j) for r in range(3) for j in range(1, ln + 2)]
              + [("HALT",), ("CERTIFY",), ("PAY",)]
              + [("CHECK", ("PSlot",), r) for r in range(3)] + [("COMMIT", ("PSlot",), r) for r in range(3)])
        P = [rng.choice(al) for _ in range(ln)]
        vs = {r: rng.choice(xs) for r in range(3)}
        cases.append((P, vs, 25, 3))
    toks = []
    for (P, vs, n, nr) in cases:
        toks += ["pslot", n, nr] + flat.regs_tokens(vs) + flat.prog_tokens(P, True)
    h = multi.Host(multi.PSLOT, priced=True)

    def exp(c):
        P, vs, n, nr = c
        s = h.start(vs)
        out = [flat.flat_host(h, s, nr)]
        for _ in range(n):
            s = h.step(P, s)
            out.append(flat.flat_host(h, s, nr))
        return out
    _check_blocks(cases, runner(toks), exp, "pslot")
    finals = [exp(c)[-1] for c in cases]
    assert any(f[3] == 1 for f in finals), "no CERTIFY succeeded"


@coq
def test_extracted_codes_and_prime_stream_match_python(runner):
    toks, expect = [], []
    for m in range(0, 7):
        for n in range(0, 7):
            toks += ["pair", m, n]
            expect.append([str(codes.pair(m, n))])
    for x in list(range(0, 80)) + [2 ** 70 + 2 ** 5, 3 * 2 ** 40, 2 ** 100]:
        toks += ["unpair", x]
        u = codes.unpair(x)
        expect.append(["-"] if u is None else ["%d %d" % u])
    for i in range(0, 8):
        toks += ["qs", i]
        expect.append([str(codes.qs(i))])
    for x in range(0, 60):
        toks += ["heval", x]
        expect.append([str(int(codes.heval(x)))])
        toks += ["puheval", x]
        expect.append([str(int(codes.pu_heval(x)))])
    progs = [[], [("HALT",)], [("INC", 0), ("HALT",)], [("DEC", 0, 3), ("CHECK", ("PGe", 3), 1), ("COMMIT", ("PEven",), 0), ("CERTIFY",)]]
    for P in progs:
        toks += ["progcode"] + flat.prog_tokens(P)
        expect.append([str(codes.prog_code(P))])
    pprogs = [[("PAY",)], [("INC", 0), ("PAY",), ("CHECK", ("UBase", ("PGe", 2)), 1), ("COMMIT", ("URun", 77), 0)]]
    for P in pprogs:
        toks += ["puprogcode"] + flat.prog_tokens(P)
        expect.append([str(codes.pu_prog_code(P))])
    blocks = runner(toks)
    assert [b for b in blocks] == expect


@coq
def test_extracted_U_matches_python_on_tiny_guests(runner):
    cases = rc.universal_cases()
    nr, stride, k = 96, 200, 15
    toks = []
    for (P, x, y) in cases:
        toks += ["uhost", nr, stride, k, x, y] + flat.prog_tokens(P)
    h = universal.HOST

    def exp(c):
        P, x, y = c
        s = universal.hload(P, x, y)
        out = [flat.flat_host(h, s, nr)]
        for _ in range(k):
            s = h.run_prog(stride, universal.U, s)
            out.append(flat.flat_host(h, s, nr))
        return out
    _check_blocks(cases, runner(toks), exp, "U")


@coq
def test_extracted_U_P_matches_python_on_tiny_priced_guests(runner):
    cases = []
    al = [("INC", 0), ("INC", 1), ("DEC", 0, 1), ("HALT",)]
    for ln in (1, 2, 3):
        for P in __import__("itertools").product(al, repeat=ln):
            if codes.pu_prog_code(P).bit_length() <= 14:
                for (x, y) in ((0, 0), (3, 1)):
                    cases.append((list(P), x, y))
    nr, stride, k = 96, 200, 15
    toks = []
    for (P, x, y) in cases:
        toks += ["puhost", nr, stride, k, x, y] + flat.prog_tokens(P)
    h = universal.HOST_P

    def exp(c):
        P, x, y = c
        s = universal.pu_hload(P, x, y)
        out = [flat.flat_host(h, s, nr)]
        for _ in range(k):
            s = h.run_prog(stride, universal.U_P, s)
            out.append(flat.flat_host(h, s, nr))
        return out
    _check_blocks(cases, runner(toks), exp, "U_P")


# The guests below run U and U_P to their stop. scripts/realize_universal_runs.py
# holds the guests and checks, against the python guest machine, that the host
# stops when the guest stops, that each visit of U's loop head shows the guest
# after one more step, and that at the stop the counters, ledger, flag and trap
# latch are the guest's. The quick cases are in this test; the cases with a
# record instruction (program code at least 2^24, hundreds of millions of host
# steps) are run by the CI job `realize-universal` and by hand, see
# ocaml/README-ci.txt.

sys.path.insert(0, str(REPO / "scripts"))
import realize_universal_runs as rur  # noqa: E402


@coq
@pytest.mark.parametrize("name", rur.QUICK)
def test_extracted_U_and_U_P_run_their_guests_to_the_stop(runner, name):
    r = rur.run_case(runner.exe, name, timeout=900)
    assert r["ok"], r["problems"]
    assert r["host_stopped"]
    assert r["final"]["trap"] == 0


@coq
def test_extracted_U_counts_a_guest_loop_exactly(runner):
    """dec-loop: A counts down from 2 over a program code of 2^19. The host
    must end with RA = RB = 0 after exactly three guest steps and a host step
    count that is the same however often the register storage is compacted."""
    r = rur.run_case(runner.exe, "dec-loop", timeout=900)
    assert r["ok"], r["problems"]
    assert r["guest_steps"] == 3 and r["final"]["RA"] == 0 and r["final"]["RB"] == 0
    assert r["host_steps"] == 25953317


NEVER = 10 ** 9  # compact every NEVER steps: the register storage is never replaced


@coq
@pytest.mark.parametrize("every", [1, 7, 1000])
def test_compacting_the_register_storage_changes_no_result(runner, every):
    """RealizeCompact.v proves that replacing the register storage by a table
    changes nothing. The extracted driver compacts every REALIZE_COMPACT_EVERY
    steps; here it compacts every step, every seventh step and every thousandth
    step, and everything it prints (the host state at each visit of the loop
    head, the step count, the final state) must equal a run that never
    compacts. The final state must also equal the state the plain extracted
    host run (uhost, which is rlz_host_run_prog and does not use the schedule
    function) reaches after the same number of steps."""
    for name in ("inc-halt", "inc-inc-halt", "p-inc-halt", "p-inc-inc-halt"):
        machine, P, x, y, _note = rur.CASES[name]
        urun, uhost = ("urun", "uhost") if machine == "U" else ("purun", "puhost")
        gp = flat.prog_tokens(P)
        args = [urun, rur.NR, 1000, 10 ** 9, x, y] + gp
        reference = runner(args, extra_env={"REALIZE_COMPACT_EVERY": str(NEVER)})
        got = runner(args, extra_env={"REALIZE_COMPACT_EVERY": str(every)})
        assert got == reference, (name, every)
        steps = int(reference[0][0].split()[1])
        assert steps > 0 and reference[0][0].split()[2] == "1", name
        # state 0, then the state after `steps` steps, from the plain run
        plain = runner([uhost, rur.NR, steps, 1, x, y] + gp)[0]
        assert len(plain) == 2
        assert plain[-1] == reference[0][-1], (name, every)
