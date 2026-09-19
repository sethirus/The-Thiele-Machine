#!/usr/bin/env python3
"""Regenerate the arbitrary typed CPU boundary from actual register declarations.

The generated module contains no invariants or proof assumptions. Completeness
against CoreTyping is checked separately by HWBoundaryCompleteness.v.
"""
import argparse
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'coq/kami_hw/ThieleCPUCore.v'
TARGET = ROOT / 'coq/kami_hw/HWBoundary.v'
HEADER = '''(** HWBoundary.v: a typed record with one field per register of the actual
    CPU [thieleCore], generated from the register declarations of
    ThieleCPUCore.v, and its Kami register map.  Every field is an arbitrary
    value of the declared kind; no invariant is imposed here. *)

Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore.
From Coq Require Import String List.
Import ListNotations.
Open Scope string_scope.

'''


def generate():
    source = re.sub(r'\(\*.*?\*\)', '', SOURCE.read_text(), flags=re.S)
    declarations = re.findall(r'\bRegister\s+"(\w+)"\s*:\s*(.*?)\s*<-', source, re.S)
    fields = [(name, ' '.join(kind.split())) for name, kind in declarations]
    if not fields or len({name for name, _ in fields}) != len(fields):
        raise ValueError('Missing or duplicate CPU register declarations')
    if len(fields) != len(re.findall(r'\bRegister\s+"', source)):
        raise ValueError('Unparsed CPU register declaration')
    text = HEADER + 'Record HWB := {\n'
    text += ';\n'.join(f'  hw_{name} : type ({kind})' for name, kind in fields)
    text += '\n}.\n\nDefinition hwb_reg (k : Kind) (v : type k) : sigT (fullType type) :=\n'
    text += '  existT (fullType type) (SyntaxKind k) v.\n\nDefinition hwb_regs (b : HWB) : RegsT :=\n'
    text += '\n'.join(f'  {"" if i == 0 else "("}M.add "{name}" (hwb_reg ({kind}) b.(hw_{name}))'
                      for i, (name, kind) in enumerate(fields))
    text += '\n  (M.empty _)' + ')' * (len(fields) - 1) + '.\n'
    return text, len(fields)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    generated, count = generate()
    if args.check:
        if TARGET.read_text() != generated:
            raise SystemExit('HWBoundary.v differs from the CPU declarations; regenerate it')
    else:
        TARGET.write_text(generated)
    print(f'HWBoundary: {count} CPU register declarations matched')
