#!/usr/bin/env python3
"""Check configured Coq theorems for unexpected axioms and emit a CI-failing exit code.
"""
import json
import shlex
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
COQ = ROOT / "coq"
CONFIG = COQ / "INQUISITOR_ASSUMPTIONS.json"


def load_flags():
    flags = []
    for line in (COQ / "_CoqProject").read_text().splitlines():
        if line.strip().startswith("-R"):
            flags.extend(shlex.split(line.strip()))
    return flags


def check_target(require, symbol, allowed_tokens):
    cmd = ["coqtop", "-emacs"] + load_flags() + ["-quiet"]
    inp = f"Require Import {require}.\nPrint Assumptions {symbol}.\n"
    p = subprocess.run(cmd, input=inp.encode(), stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out = p.stdout.decode(errors='replace')
    axioms = []
    if "Axioms:" in out:
        idx = out.index("Axioms:")
        tail = out[idx+len("Axioms:"):].strip()
        for line in tail.splitlines():
            line = line.strip()
            if not line:
                break
            axioms.append(line)
    forbidden = []
    for a in axioms:
        ok = False
        for tok in allowed_tokens:
            if not tok or tok.startswith("##"):
                continue
            if tok in a or tok.replace('_','') in a:
                ok = True
                break
        if not ok:
            forbidden.append(a)
    return {'target': f'{require}.{symbol}', 'axioms': axioms, 'forbidden': forbidden, 'output': out}


def main():
    cfg = json.loads(CONFIG.read_text())
    allowed_tokens = cfg.get('allow_axioms', [])
    targets = cfg.get('targets', [])
    results = []
    overall_fail = False
    for t in targets:
        r = check_target(t['require'], t['symbol'], allowed_tokens)
        results.append(r)
        if r['forbidden']:
            overall_fail = True
    outp = Path('artifacts/print_assumptions_ci_report.json')
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(results, indent=2))
    print(json.dumps(results, indent=2))
    if overall_fail:
        print('\nERROR: Forbidden axioms detected. See artifacts/print_assumptions_ci_report.json')
        sys.exit(1)

if __name__ == '__main__':
    main()
