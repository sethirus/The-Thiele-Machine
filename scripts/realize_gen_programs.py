#!/usr/bin/env python3
"""Generate coq/kernel/foundation/RealizePrograms.v and
thiele_small/data/programs.json from Coq itself.

The host programs U (UniversalLayout.v) and U_P (UniversalPLayout.v) are
long instruction lists (thousands of instructions) built by Coq definitions
in files that Coq's extraction cannot read (they contain module aliases).
This script asks Coq to evaluate each list (Eval vm_compute), prints every
instruction as a triple of numbers, and writes

  * RealizePrograms.v: the same two lists written out as literal Coq
    terms over the canonical constructor names, each followed by an
    eq_refl proof that it is the original (so Coq's kernel, not this
    script, checks the table);
  * programs.json: the same instructions as [op, a, b] triples for the
    Python realisation, plus the register constants of the layout.

The generated .v is deterministic. tests/test_realize.py regenerates it in
a temporary directory and compares it with the checked-in file, so the
table cannot drift from U and U_P.

Usage (from the repository root, with coqc 8.18 and the project compiled):
    python scripts/realize_gen_programs.py --coqc COQC --flags "-Q ... -R ..." [--out-dir DIR]
"""

from __future__ import annotations

import argparse
import json
import re
import shlex
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# Instructions per chunk of a generated program literal (see lit in run).
CHUNK = 64

PRINT_V = r"""
From Coq Require Import List.
Require Import Kernel.RealizeNames.
Set Printing Width 100000000.
Set Printing Depth 100000000.

Definition ucode (i : @M.instr UC.hprop) : nat * nat * nat :=
  match i with
  | M.INC r => (0, r, 0)
  | M.DEC r j => (1, r, j)
  | M.HALT => (2, 0, 0)
  | M.CHECK _ r => (3, r, 0)
  | M.COMMIT _ r => (4, r, 0)
  | M.CERTIFY => (5, 0, 0)
  end.

Definition pcode (i : @PM.pu_instr UPC.pu_hprop) : nat * nat * nat :=
  match i with
  | PM.INC r => (0, r, 0)
  | PM.DEC r j => (1, r, j)
  | PM.HALT => (2, 0, 0)
  | PM.CHECK _ r => (3, r, 0)
  | PM.COMMIT _ r => (4, r, 0)
  | PM.CERTIFY => (5, 0, 0)
  | PM.PAY => (6, 0, 0)
  end.

Eval vm_compute in (map ucode UL.U).
Eval vm_compute in (map pcode UPL.U_P).
Eval vm_compute in (UL.RA, UL.RB, UL.PROG, UL.GPC).
Eval vm_compute in (UL.NC E.CA, UL.NC E.CB, UL.MP E.CA 0, UL.MP E.CB 0, UL.SLOT E.CA 0, UL.SLOT E.CB 0, UL.DEAD).
"""

CTORS_M = {0: "Minimal.EarnedMulti.INC", 1: "Minimal.EarnedMulti.DEC",
           2: "Minimal.EarnedMulti.HALT", 3: "Minimal.EarnedMulti.CHECK Minimal.UniversalCodes.PSlot",
           4: "Minimal.EarnedMulti.COMMIT Minimal.UniversalCodes.PSlot",
           5: "Minimal.EarnedMulti.CERTIFY"}
CTORS_P = {0: "Minimal.EarnedMultiPriced.INC", 1: "Minimal.EarnedMultiPriced.DEC",
           2: "Minimal.EarnedMultiPriced.HALT",
           3: "Minimal.EarnedMultiPriced.CHECK Kernel.UniversalPCodes.PSlot",
           4: "Minimal.EarnedMultiPriced.COMMIT Kernel.UniversalPCodes.PSlot",
           5: "Minimal.EarnedMultiPriced.CERTIFY", 6: "Minimal.EarnedMultiPriced.PAY"}


def num(n):
    """A numeral. Small numbers are written as nat literals; larger ones
    through N.to_nat of a binary literal, because a nat literal extracts to
    a chain of successor calls as long as the number."""
    return str(n) if n < 10 else "(N.to_nat %d%%N)" % n


def term(trip, ctors):
    op, a, b = trip
    h = ctors[op]
    if op in (0, 3, 4):
        return "%s %s" % (h, num(a))
    if op == 1:
        return "%s %s %s" % (h, num(a), num(b))
    return h


def parse_triples(txt: str):
    return [tuple(int(x) for x in m.groups())
            for m in re.finditer(r"\((\d+), (\d+), (\d+)\)", txt)]


def run(coqc, flags, out_dir: Path):
    with tempfile.TemporaryDirectory() as td:
        v = Path(td) / "RealizePrint.v"
        v.write_text(PRINT_V, encoding="utf-8", newline="\n")
        proc = subprocess.run([coqc, *flags, str(v)], capture_output=True, text=True, cwd=td)
        if proc.returncode != 0:
            sys.exit("coqc failed:\n" + proc.stdout[-3000:] + proc.stderr[-3000:])
        out = proc.stdout
    blocks = re.findall(r"=\s(.*?)\n\s*:\s", out, re.S)
    assert len(blocks) == 4, "expected four results, got %d" % len(blocks)
    U = parse_triples(blocks[0])
    UP = parse_triples(blocks[1])
    ra = [int(x) for x in re.findall(r"\d+", blocks[2])]
    lay = [int(x) for x in re.findall(r"\d+", blocks[3])]
    layout = {"RA": ra[0], "RB": ra[1], "PROG": ra[2], "GPC": ra[3],
              "NC_A": lay[0], "NC_B": lay[1], "MP_A0": lay[2], "MP_B0": lay[3],
              "SLOT_A0": lay[4], "SLOT_B0": lay[5], "DEAD": lay[6]}

    def lit(name, trips, ctors, ty):
        # A list literal of thousands of instructions extracts to straight-line code
        # as long as the list, in the one function that initialises the module, and
        # the OCaml compiler recurses over that length: it runs out of its 8 MB stack
        # on Linux. Written as chunks of CHUNK instructions, each a function of unit
        # (so each is compiled as a function of its own) joined by append, no function
        # is longer than one chunk.
        chunks = [trips[i:i + CHUNK] for i in range(0, len(trips), CHUNK)] or [[]]
        parts = []
        for k, ch in enumerate(chunks):
            body = ";\n  ".join(term(t, ctors) for t in ch)
            parts.append("Definition %s_c%d (_ : unit) : %s :=\n  [%s].\n" % (name, k, ty, body))
        joined = " ++ (".join("%s_c%d tt" % (name, k) for k in range(len(chunks))) + ")" * (len(chunks) - 1)
        parts.append("Definition %s : %s :=\n  %s.\n" % (name, ty, joined))
        return "\n".join(parts)

    v_text = """(** RealizePrograms.v: the host programs U and U_P as literal lists.

    GENERATED by scripts/realize_gen_programs.py from the evaluation of
    U (UniversalLayout.v) and U_P (UniversalPLayout.v) by Coq itself. Do not
    edit by hand. The lists are here, written out, because Coq's monolithic
    extraction cannot read the files that build U and U_P (they contain module
    aliases); each list is followed by an eq_refl proof that it is the
    original, so Coq's kernel checks the table.

    Dependencies: UniversalLayout.v, UniversalPLayout.v. No axioms and no
    unfinished proofs.                                                     *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file is data, checked against its source by the proofs below. *)

From Coq Require Import List NArith.
Import ListNotations.
Require Minimal.EarnedMulti Minimal.EarnedMultiPriced Minimal.UniversalCodes
  Kernel.UniversalLayout Kernel.UniversalPCodes Kernel.UniversalPLayout.

""" + lit("rlz_host_program", U, CTORS_M,
          "list (@Minimal.EarnedMulti.instr Minimal.UniversalCodes.hprop)") + """
Lemma rlz_host_program_is : rlz_host_program = Kernel.UniversalLayout.U.
Proof. vm_compute. reflexivity. Qed.

""" + lit("rlz_phost_program", UP, CTORS_P,
          "list (@Minimal.EarnedMultiPriced.pu_instr Kernel.UniversalPCodes.pu_hprop)") + """
Lemma rlz_phost_program_is : rlz_phost_program = Kernel.UniversalPLayout.U_P.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions rlz_host_program_is.
Print Assumptions rlz_phost_program_is.
"""
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "RealizePrograms.v").write_text(v_text, encoding="utf-8", newline="\n")
    data = {"layout": layout, "U": [list(t) for t in U], "U_P": [list(t) for t in UP]}
    # one instruction triple per line: stable, diffable, small
    def rows(name):
        body = ",\n".join("   " + json.dumps(t, separators=(",", ":")) for t in data[name])
        return '  "%s": [\n%s\n  ]' % (name, body)

    text = '{\n  "layout": %s,\n%s,\n%s\n}\n' % (
        json.dumps(layout, sort_keys=True), rows("U"), rows("U_P"))
    (out_dir / "programs.json").write_text(text, encoding="utf-8", newline="\n")
    return data


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--coqc", required=True)
    ap.add_argument("--flags", help="coqc load-path flags, one string (split like a shell line)")
    ap.add_argument("--flags-json", help="coqc load-path flags as a JSON list (use this on Windows)")
    ap.add_argument("--out-dir", default=str(REPO / "gen_out"))
    a = ap.parse_args()
    flags = json.loads(a.flags_json) if a.flags_json else shlex.split(a.flags or "")
    d = run(a.coqc, flags, Path(a.out_dir))
    print("U: %d instructions, U_P: %d instructions, layout %r"
          % (len(d["U"]), len(d["U_P"]), d["layout"]))


if __name__ == "__main__":
    main()
