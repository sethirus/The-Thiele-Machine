#!/usr/bin/env python3
"""
Instrumentation adapter — parse VM runtime logs and emit per-step ledger CSVs.

Purpose:
- Provide a lightweight bridge to integrate the VM's runtime traces with the
  experiment suite. The adapter accepts either a single log file or a directory
  of log files and converts each into a normalized CSV with records:
    step, vm_mu, delta

Usage examples:
- Single file:
    python3 scripts/instrumentation_adapter.py --input path/to/run.log --output path/to/out.csv
- Directory mode (convert all *.log -> *.csv):
    python3 scripts/instrumentation_adapter.py --input logs/ --output csvs/ --dir

Expected input formats (robust):
- Plain CSV-like lines: "step,vm_mu,delta"
- JSON per-line: '{"step": 1, "vm_mu": 0.0, "delta": 2}'
- Other names tolerated: t, trial, mu, vmMu, mu_delta, d

This is a conservative, easily-audited adapter: it does not execute the VM;
instead it normalizes an external runtime trace into the exact CSV layout used
by the experiment verifiers.

Output:
- CSV with header: step,vm_mu,delta
"""

import os
import csv
import json
import argparse
from typing import Optional, Dict, Any

def parse_line(line: str) -> Optional[Dict[str, Any]]:
    line = line.strip()
    if not line:
        return None
    # JSON line
    if line.startswith("{"):
        try:
            obj = json.loads(line)
            return obj
        except Exception:
            return None
    # CSV-like
    parts = [p.strip() for p in line.split(",")]
    if len(parts) >= 3:
        # try to coerce numeric types
        try:
            step = int(parts[0])
        except Exception:
            step = None
        try:
            vm_mu = float(parts[1])
        except Exception:
            vm_mu = None
        try:
            delta = float(parts[2])
        except Exception:
            delta = None
        return {"step": step, "vm_mu": vm_mu, "delta": delta}
    return None

def convert_log_to_csv(input_path: str, output_csv: str) -> str:
    records = []
    with open(input_path, "r") as f:
        for ln in f:
            obj = parse_line(ln)
            if obj is None:
                continue
            # Normalize keys
            step = obj.get("step") if obj.get("step") is not None else obj.get("t") or obj.get("trial")
            vm_mu = obj.get("vm_mu") if obj.get("vm_mu") is not None else obj.get("mu") or obj.get("vmMu")
            delta = obj.get("delta") if obj.get("delta") is not None else obj.get("mu_delta") or obj.get("d")
            records.append({"step": step, "vm_mu": vm_mu, "delta": delta})
    # Ensure directory exists
    out_dir = os.path.dirname(output_csv) or "."
    os.makedirs(out_dir, exist_ok=True)
    # Write CSV
    with open(output_csv, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=["step", "vm_mu", "delta"])
        writer.writeheader()
        for r in records:
            writer.writerow(r)
    return output_csv

def aggregate_from_directory(log_dir: str, out_dir: str) -> str:
    import glob
    os.makedirs(out_dir, exist_ok=True)
    for p in glob.glob(os.path.join(log_dir, "*.log")):
        name = os.path.splitext(os.path.basename(p))[0]
        out = os.path.join(out_dir, f"{name}.csv")
        convert_log_to_csv(p, out)
    return out_dir

def main():
    parser = argparse.ArgumentParser(description="Instrumentation adapter: parse VM logs to CSV.")
    parser.add_argument("--input", required=True, help="Input log file or directory")
    parser.add_argument("--output", required=True, help="Output CSV file or directory")
    parser.add_argument("--dir", action="store_true", help="Treat input/output as directories")
    args = parser.parse_args()
    if args.dir:
        aggregate_from_directory(args.input, args.output)
        print("Wrote CSVs to", args.output)
    else:
        out = convert_log_to_csv(args.input, args.output)
        print("Wrote CSV:", out)

if __name__ == "__main__":
    main()