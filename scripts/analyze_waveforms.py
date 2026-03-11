#!/usr/bin/env python3
"""Basic VCD waveform summary for CI and local verification logs."""

from __future__ import annotations

import os
import sys
from collections import defaultdict


def parse_vcd(vcd_file: str):
    signals = {}
    signal_changes = defaultdict(int)
    time_stamps = set()
    current_time = 0

    with open(vcd_file, "r", encoding="utf-8", errors="replace") as handle:
        for raw_line in handle:
            line = raw_line.strip()
            if line.startswith("$var"):
                parts = line.split()
                if len(parts) >= 5:
                    signals[parts[3]] = {"name": parts[4], "type": parts[1], "width": int(parts[2])}
            elif line.startswith("#"):
                current_time = int(line[1:])
                time_stamps.add(current_time)
            elif line and not line.startswith("$"):
                parts = line.split()
                if len(parts) == 2 and parts[1] in signals:
                    signal_changes[parts[1]] += 1

    return {
        "total_signals": len(signals),
        "signal_changes": dict(signal_changes),
        "time_stamps": sorted(time_stamps),
        "max_time": max(time_stamps) if time_stamps else 0,
        "signals": signals,
    }


def main() -> int:
    vcd_path = sys.argv[1] if len(sys.argv) > 1 else "thiele_cpu_tb.vcd"
    if not os.path.exists(vcd_path):
        print(f"VCD file not found: {vcd_path}")
        return 1

    data = parse_vcd(vcd_path)
    print("=== VCD Waveform Analysis ===")
    print(f"Total signals: {data['total_signals']}")
    print(f"Simulation time range: 0 - {data['max_time']} ns")
    print(f"Time stamps: {len(data['time_stamps'])}")
    print("\nTop 5 signals by changes:")
    sorted_changes = sorted(data["signal_changes"].items(), key=lambda item: item[1], reverse=True)[:5]
    for symbol, changes in sorted_changes:
        name = data["signals"].get(symbol, {}).get("name", "unknown")
        print(f"  {name} ({symbol}): {changes} changes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())