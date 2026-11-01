"""Harness shared by the realisation tests: compile Coq, evaluate terms with
vm_compute, parse the printed result.

This is test scaffolding, not part of the trusted path. It never defines a
machine: every Coq evaluation calls the definitions of minimal/ and
coq/kernel/foundation/ themselves, and only wraps their results in tuples so
they can be printed.

Where Coq lives. The tests need compiled .vo files for the files they
import. Set THIELE_COQ_BUILD to a directory laid out like the repository
(minimal/*.vo, coq/kernel/foundation/*.vo, plus the undecidability library
under vendor/ or wherever THIELE_UNDEC points) to use a prebuilt tree;
otherwise the standard-library-only files of minimal/ are compiled into a
temporary directory (a minute or two). Tests that need the universal
program or the priced guest require the prebuilt tree and say so when
skipped.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

REPO_ROOT = Path(__file__).resolve().parent.parent
# Where minimal/*.v are read from. The repository itself, unless THIELE_SRC_ROOT
# names another checkout (used when this directory is developed outside it).
SRC_ROOT = Path(os.environ.get("THIELE_SRC_ROOT", str(REPO_ROOT)))

COQC_ENV = "THIELE_COQC"


def find_coqc() -> Optional[str]:
    """coqc 8.18 if available. THIELE_COQC overrides; on the Windows
    development PC the Coq-8.18 install is tried before PATH (the CI image
    has apt Coq 8.18.0 on PATH)."""
    cand = []
    if os.environ.get(COQC_ENV):
        cand.append(os.environ[COQC_ENV])
    cand.append("C:/Users/tbagt/Coq-8.18/bin/coqc.exe")
    w = shutil.which("coqc")
    if w:
        cand.append(w)
    for c in cand:
        if c and (shutil.which(c) or os.path.exists(c)):
            return c
    return None


# ---------------------------------------------------------------------------
# parsing what Coq prints
# ---------------------------------------------------------------------------


class Con:
    """A constructor applied to arguments: Con("INC", [3]) for `INC 3`.
    Qualification (M.INC, Minimal.EarnedMulti.INC) is dropped."""

    __slots__ = ("name", "args")

    def __init__(self, name, args=()):
        self.name = name
        self.args = list(args)

    def __repr__(self):
        return "Con(%s%s)" % (self.name, "".join(" " + repr(a) for a in self.args))

    def __eq__(self, o):
        return isinstance(o, Con) and o.name == self.name and o.args == self.args


_TOK = re.compile(r"\s*(?:(\d+)|([A-Za-z_][A-Za-z0-9_'.]*)|(.))", re.S)


def _tokens(text: str):
    pos = 0
    out = []
    while pos < len(text):
        m = _TOK.match(text, pos)
        if not m:
            break
        pos = m.end()
        if m.group(1) is not None:
            out.append(("n", int(m.group(1))))
        elif m.group(2) is not None:
            out.append(("id", m.group(2).split(".")[-1]))
        else:
            out.append(("p", m.group(3)))
    return out


def parse_term(text: str):
    """Parse a Coq value as printed by Compute: numerals, true/false,
    None/Some, constructor applications, lists [a; b], pairs (a, b, c).
    Pairs become Python tuples, lists become lists, true/false bools."""
    toks = _tokens(text)
    pos = [0]

    def peek():
        return toks[pos[0]] if pos[0] < len(toks) else ("eof", None)

    def eat(kind=None, val=None):
        t = peek()
        if kind and t[0] != kind or (val is not None and t[1] != val):
            raise ValueError("parse error at %d near %r in %r" % (pos[0], t, text[:200]))
        pos[0] += 1
        return t

    def atom():
        t = peek()
        if t[0] == "n":
            eat()
            return t[1]
        if t[0] == "id":
            eat()
            if t[1] == "true":
                return True
            if t[1] == "false":
                return False
            return Con(t[1])
        if t == ("p", "("):
            eat()
            items = [expr()]
            while peek() == ("p", ","):
                eat()
                items.append(expr())
            eat("p", ")")
            return items[0] if len(items) == 1 else tuple(items)
        if t == ("p", "["):
            eat()
            items = []
            if peek() != ("p", "]"):
                items.append(expr())
                while peek() == ("p", ";"):
                    eat()
                    items.append(expr())
            eat("p", "]")
            return items
        raise ValueError("parse error at %d near %r in %r" % (pos[0], t, text[:200]))

    def expr():
        # application: head atom followed by atoms
        h = atom()
        if isinstance(h, Con) and not h.args:
            args = []
            while peek()[0] in ("n", "id") or peek() in (("p", "("), ("p", "[")):
                args.append(atom())
            h = Con(h.name, args)
        return h

    v = expr()
    if pos[0] != len(toks):
        raise ValueError("trailing input in %r" % (text[:200],))
    return v


def parse_compute_output(out: str) -> List:
    """The values of consecutive `Compute`/`Eval vm_compute in` commands, in
    order. Each result prints as '     = <term>\\n     : <type>'."""
    vals = []
    for m in re.finditer(r"^\s*=\s(.*?)\n\s*:\s", out, re.S | re.M):
        vals.append(parse_term(" ".join(m.group(1).split())))
    return vals


# ---------------------------------------------------------------------------
# running coqc
# ---------------------------------------------------------------------------


def coq_load_flags(root: Path, undec: Optional[Path] = None) -> List[str]:
    """-Q flags for a tree laid out like the repository."""
    flags = ["-Q", str(root / "minimal"), "Minimal"]
    kf = root / "coq" / "kernel" / "foundation"
    if kf.exists():
        flags += ["-R", str(kf), "Kernel"]
    if undec is not None:
        flags += ["-Q", str(undec), "Undecidability"]
    return flags


def run_coqc(coqc: str, flags: Sequence[str], vfile: Path, timeout: int = 3000) -> str:
    proc = subprocess.run([coqc, *flags, str(vfile)], capture_output=True,
                          text=True, timeout=timeout, cwd=str(vfile.parent))
    if proc.returncode != 0:
        raise RuntimeError("coqc failed on %s:\n%s\n%s" % (vfile, proc.stdout[-3000:], proc.stderr[-3000:]))
    return proc.stdout


_MIN_FILES = ["EarnedCore", "EarnedGeneric", "EarnedMulti", "EarnedPriced", "EarnedMultiPriced"]


def build_minimal(coqc: str, dest: Path) -> Path:
    """Compile the standard-library-only files of minimal/ that the
    differential tests need into dest/minimal (copies the .v files; the repo
    is never written)."""
    mdir = dest / "minimal"
    mdir.mkdir(parents=True, exist_ok=True)
    flags = ["-Q", str(mdir), "Minimal"]
    for name in _MIN_FILES:
        src = SRC_ROOT / "minimal" / (name + ".v")
        dst = mdir / (name + ".v")
        shutil.copyfile(src, dst)
        if not (mdir / (name + ".vo")).exists():
            run_coqc(coqc, flags, dst)
    return dest


def prebuilt_flags() -> Tuple[Optional[List[str]], str]:
    """(coqc load-path flags, reason) for a tree in which the realisation and
    the universal files are compiled with the coqc in use.

    THIELE_COQ_BUILD names a directory laid out like the repository
    (minimal/*.vo, coq/kernel/foundation/*.vo, vendor/coq-undecidability/theories)
    and THIELE_UNDEC overrides the compiled coq-undecidability theories directory. Without them the repository itself
    is used when coq/kernel/foundation/Realize.vo exists (the CI build). If
    neither holds, flags is None and reason says why."""
    b = os.environ.get("THIELE_COQ_BUILD")
    root = Path(b) if b else REPO_ROOT
    undec = Path(os.environ.get("THIELE_UNDEC", str(root / "vendor" / "coq-undecidability" / "theories")))
    kf = root / "coq" / "kernel" / "foundation"
    if not (kf / "Realize.vo").exists():
        return None, ("no compiled coq/kernel/foundation/Realize.vo under %s; set THIELE_COQ_BUILD "
                      "(and THIELE_UNDEC) to a built tree" % root)
    if not undec.exists():
        return None, "coq-undecidability theories not found at %s; set THIELE_UNDEC" % undec
    return ["-Q", str(undec), "Undecidability", "-Q", str(root / "minimal"), "Minimal",
            "-R", str(kf), "Kernel"], ""


def coq_values(coqc: str, flags: Sequence[str], text: str, workdir: Path, name: str):
    """Write text as workdir/name.v, run coqc, return the parsed values of
    its Compute commands."""
    workdir.mkdir(parents=True, exist_ok=True)
    v = workdir / (name + ".v")
    v.write_text(text, encoding="utf-8", newline="\n")
    out = run_coqc(coqc, flags, v)
    return parse_compute_output(out)
