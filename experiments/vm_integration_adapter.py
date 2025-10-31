#!/usr/bin/env python3
# experiments/vm_integration_adapter.py
# Small adapter to emit per-step ledger CSVs from line-based VM logs.
#
# Provides:
#  - emit_ledger_csv(stream_in, out_path): parse line-based VM output (or
#    simulated lines) and write a CSV with columns:
#      run_id,step,vm_mu_bits,instruction_cost,timestamp
#  - CLI with --dry-run that writes a 3-line example CSV for smoke checks.
#
# The parser is permissive: it accepts lines with key=value tokens or simple
# whitespace-separated fields in expected order. This keeps the adapter useful
# for quick integration tests without depending on a particular VM format.

import argparse
import csv
import io
import os
from typing import Iterable, TextIO, Union

CSV_HEADER = ["run_id", "step", "vm_mu_bits", "instruction_cost", "timestamp"]

def _ensure_dir_for_file(path: str):
    d = os.path.dirname(path) or "."
    os.makedirs(d, exist_ok=True)

def _parse_line_flexible(line: str):
    """
    Parse a single line of VM output.

    Supported formats (per-line):
    - key=value ...  (e.g. run_id=run0 step=1 vm_mu_bits=0.5 instruction_cost=2 timestamp=169...)
    - whitespace CSV-like: run_id step vm_mu_bits instruction_cost timestamp

    Returns a dict with keys matching CSV_HEADER or None if the line is empty/unparseable.
    """
    s = line.strip()
    if not s:
        return None
    parts = s.split()
    parsed = {}
    # Try key=value tokens
    if "=" in s:
        for p in parts:
            if "=" in p:
                k, v = p.split("=", 1)
                parsed[k.strip()] = v.strip().strip(",")
    else:
        # Try positional mapping if 5 tokens
        if len(parts) >= 5:
            parsed["run_id"] = parts[0]
            parsed["step"] = parts[1]
            parsed["vm_mu_bits"] = parts[2]
            parsed["instruction_cost"] = parts[3]
            parsed["timestamp"] = parts[4]
        else:
            # Last resort: if comma-separated
            if "," in s:
                toks = [t.strip() for t in s.split(",")]
                if len(toks) >= 5:
                    parsed["run_id"] = toks[0]
                    parsed["step"] = toks[1]
                    parsed["vm_mu_bits"] = toks[2]
                    parsed["instruction_cost"] = toks[3]
                    parsed["timestamp"] = toks[4]
    # Normalize keys and types
    if not parsed:
        return None
    out = {}
    for k in CSV_HEADER:
        if k in parsed:
            out[k] = parsed[k]
        else:
            # Missing field: return None to indicate line not usable
            return None
    return out

def emit_ledger_csv(stream_in: Union[str, TextIO, Iterable[str]], out_path: str) -> str:
    """
    Read line-based VM output from either:
      - a path to a file (str),
      - an open text stream (TextIO),
      - or any iterable of lines (Iterable[str]).
    Write a CSV at out_path with header CSV_HEADER and return the out_path.

    This function is intentionally small and permissive for integration.
    """
    _ensure_dir_for_file(out_path)
    # Open input
    if isinstance(stream_in, str):
        inp = open(stream_in, "r", encoding="utf-8")
        close_inp = True
    elif hasattr(stream_in, "read"):
        inp = stream_in
        close_inp = False
    else:
        # Assume iterable of lines
        inp = stream_in
        close_inp = False

    with open(out_path, "w", newline="", encoding="utf-8") as outf:
        writer = csv.DictWriter(outf, fieldnames=CSV_HEADER)
        writer.writeheader()
        # Iterate lines
        for line in inp:
            parsed = _parse_line_flexible(line)
            if parsed is None:
                continue
            # Try to coerce numeric fields to simple strings
            try:
                parsed["step"] = int(parsed["step"])
            except Exception:
                # leave as-is
                pass
            try:
                parsed["vm_mu_bits"] = float(parsed["vm_mu_bits"])
            except Exception:
                pass
            try:
                parsed["instruction_cost"] = float(parsed["instruction_cost"])
            except Exception:
                pass
            writer.writerow({
                "run_id": parsed["run_id"],
                "step": parsed["step"],
                "vm_mu_bits": parsed["vm_mu_bits"],
                "instruction_cost": parsed["instruction_cost"],
                "timestamp": parsed["timestamp"]
            })
    if isinstance(stream_in, str) and close_inp:
        inp.close()
    return out_path

def _write_example_csv(out_path: str):
    _ensure_dir_for_file(out_path)
    rows = [
        {"run_id":"run0", "step":0, "vm_mu_bits":0.0, "instruction_cost":1.0, "timestamp":"0.0"},
        {"run_id":"run0", "step":1, "vm_mu_bits":0.7, "instruction_cost":2.0, "timestamp":"0.01"},
        {"run_id":"run0", "step":2, "vm_mu_bits":0.2, "instruction_cost":1.0, "timestamp":"0.02"},
    ]
    with open(out_path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=CSV_HEADER)
        w.writeheader()
        for r in rows:
            w.writerow(r)
    return out_path

def main():
    parser = argparse.ArgumentParser(description="VM integration adapter: emit per-step ledger CSVs.")
    parser.add_argument("--in", dest="in_path", help="Path to line-based VM log (optional). If omitted, read stdin.")
    parser.add_argument("--out", dest="out_path", default="logs/vm_ledger.csv", help="CSV output path")
    parser.add_argument("--dry-run", action="store_true", help="Write a small 3-line example CSV and exit")
    args = parser.parse_args()

    if args.dry_run:
        out = _write_example_csv(args.out_path)
        print("Wrote example ledger CSV:", out)
        return

    # Normal operation: read from file or stdin
    if args.in_path:
        out = emit_ledger_csv(args.in_path, args.out_path)
    else:
        import sys
        out = emit_ledger_csv(sys.stdin, args.out_path)
    print("Wrote ledger CSV:", out)

if __name__ == "__main__":
    main()