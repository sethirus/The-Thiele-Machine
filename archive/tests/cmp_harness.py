"""Harness for the compiler tests: build the extracted driver, run it, parse
what it prints, and evaluate terms with coqc.

This is test scaffolding, not part of the trusted path. It never defines a
machine or a compiler: every evaluation calls the extracted OCaml or the Coq
definitions themselves, and only wraps their results so they can be printed
and compared.

Where things live (as for the realisation tests, tests/test_realize*.py):
  THIELE_COQC         coqc 8.18 (default: coqc on PATH)
  THIELE_COQ_BUILD    a directory laid out like the repository with
                      minimal/*.vo and coq/kernel/foundation/*.vo built
                      (default: the repository, as in the CI build)
  THIELE_UNDEC        the compiled coq-undecidability theories (default:
                      vendor/coq-undecidability/theories)
  THIELE_CMP_DRIVER   an already built cmp_driver executable, to skip the
                      extraction (used while developing)
OCaml is found on PATH (apt ocaml libzarith-ocaml-dev) or, on the development
PC, in the opam switch under %LOCALAPPDATA%/opam/default.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

REPO = Path(os.environ.get("THIELE_SRC_ROOT", str(Path(__file__).resolve().parent.parent)))


def find_coqc() -> Optional[str]:
    cand = []
    if os.environ.get("THIELE_COQC"):
        cand.append(os.environ["THIELE_COQC"])
    w = shutil.which("coqc")
    if w:
        cand.append(w)
    for c in cand:
        if c and (shutil.which(c) or os.path.exists(c)):
            return c
    return None


def ocaml_env() -> Optional[Tuple[dict, str]]:
    """(environment, path of ocamlfind) in which ocamlfind, ocamlopt and zarith work, or None.
    On the development PC the opam switch under %LOCALAPPDATA% is tried
    first (the Coq Platform install on PATH has no working ocamlfind)."""
    env = dict(os.environ)
    paths = []
    local = os.environ.get("LOCALAPPDATA")
    if local and (Path(local) / "opam" / "default" / "bin").exists():
        paths.append(str(Path(local) / "opam" / "default" / "bin"))
    paths.append(None)
    for extra in paths:
        e = dict(env)
        if extra:
            e["PATH"] = extra + os.pathsep + e.get("PATH", "")
        of = shutil.which("ocamlfind", path=e.get("PATH"))
        if not of:
            continue
        ok = True
        for cmd in ([of, "query", "zarith"], [of, "ocamlopt", "-version"]):
            r = subprocess.run(cmd, capture_output=True, text=True, env=e)
            if r.returncode != 0:
                ok = False
                break
        if ok:
            return e, of
    return None


def prebuilt_flags() -> Tuple[Optional[List[str]], str]:
    b = os.environ.get("THIELE_COQ_BUILD")
    root = Path(b) if b else REPO
    undec = Path(os.environ.get("THIELE_UNDEC", str(REPO / "vendor" / "coq-undecidability" / "theories")))
    kf = root / "coq" / "kernel" / "foundation"
    if not (kf / "CmpRun.vo").exists():
        return None, "no compiled coq/kernel/foundation/CmpRun.vo under %s; set THIELE_COQ_BUILD" % root
    if not undec.exists():
        return None, "coq-undecidability theories not found at %s; set THIELE_UNDEC" % undec
    return ["-Q", str(undec), "Undecidability", "-Q", str(root / "minimal"), "Minimal", "-R", str(kf), "Kernel"], ""


def run_coqc(coqc: str, flags: Sequence[str], vfile: Path, timeout: int = 3000) -> str:
    proc = subprocess.run([coqc, "-w", "-notation-overridden,-opaque-let", *flags, str(vfile)],
                          capture_output=True, text=True, timeout=timeout, cwd=str(vfile.parent))
    if proc.returncode != 0:
        raise RuntimeError("coqc failed on %s:\n%s\n%s" % (vfile, proc.stdout[-3000:], proc.stderr[-3000:]))
    return proc.stdout


def build_driver(workdir: Path) -> Path:
    """Extract the compiler and runner with coqc and build the OCaml driver
    in workdir; returns the executable."""
    pre = os.environ.get("THIELE_CMP_DRIVER")
    if pre and Path(pre).exists():
        return Path(pre)
    coqc = find_coqc()
    if not coqc:
        raise RuntimeError("coqc 8.18 not found (set THIELE_COQC)")
    flags, why = prebuilt_flags()
    if flags is None:
        raise RuntimeError(why)
    found = ocaml_env()
    if found is None:
        raise RuntimeError("ocamlfind with zarith not found (apt install ocaml libzarith-ocaml-dev)")
    env, ocamlfind = found
    workdir.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(REPO / "ocaml" / "CmpExtract.v", workdir / "CmpExtract.v")
    shutil.copyfile(REPO / "ocaml" / "cmp_driver.ml", workdir / "cmp_driver.ml")
    run_coqc(coqc, flags, workdir / "CmpExtract.v")
    for f in ("cmp_extracted.ml", "cmp_extracted.mli"):
        assert (workdir / f).exists(), f
    exe = workdir / "cmp_driver"
    proc = subprocess.run([ocamlfind, "ocamlopt", "-package", "zarith", "-linkpkg",
                           "cmp_extracted.mli", "cmp_extracted.ml", "cmp_driver.ml", "-o", str(exe)],
                          cwd=str(workdir), capture_output=True, text=True, env=env)
    assert proc.returncode == 0, proc.stdout + proc.stderr
    if not exe.exists() and (workdir / "cmp_driver.exe").exists():
        exe = workdir / "cmp_driver.exe"
    return exe


def run_driver(exe: Path, text: str, timeout: int = 3600) -> List[List[str]]:
    """Run the driver on text; returns the blocks of lines (each ends at END)."""
    p = subprocess.run([str(exe)], input=text, capture_output=True, text=True, timeout=timeout)
    if p.returncode != 0:
        raise RuntimeError("driver failed: %s" % p.stderr[-2000:])
    blocks, cur = [], []
    for line in p.stdout.splitlines():
        if line == "END":
            blocks.append(cur)
            cur = []
        else:
            cur.append(line)
    assert not cur, cur
    return blocks


class Result:
    """A parsed block of the driver's output for a (case ...) command."""

    def __init__(self, block: List[str]):
        self.id = block[0].split()[1]
        self.wf = block[1].split()[1] == "1"
        self.nv0 = self.nvf = self.mm_len = self.host_len = None
        self.interp_ok = None
        self.interp_ops = None
        self.interp_vars = None
        self.halted = None
        self.steps = None
        self.pc = None
        self.answer = None
        self.vars = None
        self.t_compile = self.t_interp = self.t_run = None
        if not self.wf:
            return
        for l in block[2:]:
            w = l.split()
            if w[0] == "sizes":
                self.nv0, self.nvf, self.mm_len, self.host_len = map(int, w[1:5])
            elif w[0] == "interp":
                if w[1] == "none":
                    self.interp_ok = False
                else:
                    self.interp_ok = True
                    self.interp_ops = int(w[1])
                    self.interp_vars = [int(x) for x in w[2:]]
            elif w[0] == "host":
                self.halted = w[2] == "1"
                self.steps = int(w[3])
                self.pc = int(w[4])
                self.answer = int(w[5])
                self.vars = [int(x) for x in w[6:]]
            elif w[0] == "time":
                self.t_compile, self.t_interp, self.t_run = map(float, w[1:4])


# ---------------------------------------------------------------------------
# Coq evaluation
# ---------------------------------------------------------------------------


def coq_aexp(a) -> str:
    if isinstance(a, int):
        return "(CNum %d)" % a
    if a[0] == "v":
        return "(CVar %d)" % a[1]
    return "(%s %s %s)" % ("CAdd" if a[0] == "+" else "CSub", coq_aexp(a[1]), coq_aexp(a[2]))


def coq_bexp(b) -> str:
    if b == "true":
        return "BTrue"
    if b == "false":
        return "BFalse"
    k = b[0]
    if k == "=":
        return "(BEq %s %s)" % (coq_aexp(b[1]), coq_aexp(b[2]))
    if k == "<":
        return "(BLt %s %s)" % (coq_aexp(b[1]), coq_aexp(b[2]))
    if k == "not":
        return "(BNot %s)" % coq_bexp(b[1])
    return "(%s %s %s)" % ("BAnd" if k == "and" else "BOr", coq_bexp(b[1]), coq_bexp(b[2]))


def coq_stmt(s) -> str:
    if s == "skip":
        return "SSkip"
    k = s[0]
    if k == "set":
        return "(SAssign %d %s)" % (s[1], coq_aexp(s[2]))
    if k == "seq":
        items = [coq_stmt(t) for t in s[1:]]
        if not items:
            return "SSkip"
        acc = items[-1]
        for t in reversed(items[:-1]):
            acc = "(SSeq %s %s)" % (t, acc)
        return acc
    if k == "if":
        return "(SIf %s %s %s)" % (coq_bexp(s[1]), coq_stmt(s[2]), coq_stmt(s[3]))
    if k == "while":
        return "(SWhile %s %s)" % (coq_bexp(s[1]), coq_stmt(s[2]))
    if k == "call":
        return "(SCall [%s] %d [%s])" % ("; ".join(str(d) for d in s[1]), s[2], "; ".join(coq_aexp(a) for a in s[3]))
    raise ValueError(s)


def coq_prog(p) -> str:
    procs = "; ".join("(mk_cmp_proc %d %s [%s])" % (q[1], coq_stmt(q[2]), "; ".join(coq_aexp(r) for r in q[3]))
                      for q in p[1])
    return "(mk_cmp_prog [%s] %s)" % (procs, coq_stmt(p[2]))


def coq_eval_cases(coqc: str, flags: Sequence[str], cases, workdir: Path, name: str = "cmp_eval"):
    """cases: list of (prog, nin, out, xs, ifuel, hfuel). For each, coqc
    vm_compute evaluates the wf check, the interpreter and the runner of the
    Coq definitions and returns
      (wf, interp_result, (halted, steps, answer, vars)).
    interp_result is None or (ops, vars)."""
    workdir.mkdir(parents=True, exist_ok=True)
    lines = ["From Coq Require Import List Arith.", "Import ListNotations.",
             "Require Import Kernel.CmpLang Kernel.CmpCompile Kernel.CmpHost Kernel.CmpRun.", ""]
    for p, nin, out, xs, ifuel, hfuel in cases:
        cp = coq_prog(p)
        xl = "[" + "; ".join(str(x) for x in xs) + "]"
        lines.append("Eval vm_compute in (cmp_wf_b %s)." % cp)
        lines.append("Eval vm_compute in (match cmp_interp (cp_procs %s) %d %s (cp_main %s) 0 with "
                     "Some (l, k) => (true, k, map (cmp_lget l) (seq 0 (cmp_nv0 %s %d %d))) | None => (false, 0, nil) end)."
                     % (cp, ifuel, xl, cp, cp, nin, out))
        lines.append("Eval vm_compute in (let r := cmp_exec %s %d %d %s %d in (cr_halted r, %d - cr_left r, cmp_answer %d r, "
                     "cmp_vars (cmp_nv0 %s %d %d) r))." % (cp, nin, out, xl, hfuel, hfuel, out, cp, nin, out))
    v = workdir / (name + ".v")
    v.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    outtxt = run_coqc(coqc, flags, v)
    vals = parse_values(outtxt)
    assert len(vals) == 3 * len(cases), (len(vals), len(cases))
    res = []
    for i in range(len(cases)):
        wf, interp, run = vals[3 * i:3 * i + 3]
        res.append((wf, interp, run))
    return res


def parse_values(text: str):
    """Values printed by consecutive Eval commands (numerals, true/false,
    lists, tuples)."""
    vals = []
    for m in re.finditer(r"^\s*=\s(.*?)\n\s*:\s", text, re.S | re.M):
        vals.append(_parse(" ".join(m.group(1).split())))
    return vals


def _parse(s: str):
    toks = re.findall(r"\d+|true|false|\(|\)|\[|\]|;|,|nil", s)
    pos = [0]

    def peek():
        return toks[pos[0]] if pos[0] < len(toks) else None

    def atom():
        t = peek()
        pos[0] += 1
        if t == "true":
            return True
        if t == "false":
            return False
        if t == "nil":
            return []
        if t == "(":
            items = [atom()]
            while peek() == ",":
                pos[0] += 1
                items.append(atom())
            assert peek() == ")", s
            pos[0] += 1
            return items[0] if len(items) == 1 else tuple(items)
        if t == "[":
            items = []
            if peek() != "]":
                items.append(atom())
                while peek() == ";":
                    pos[0] += 1
                    items.append(atom())
            assert peek() == "]", s
            pos[0] += 1
            return items
        return int(t)

    v = atom()
    assert pos[0] == len(toks), s
    return v
