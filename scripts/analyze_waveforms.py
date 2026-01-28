#!/usr/bin/env python3
"""
VCD Waveform Analyzer for Thiele Machine CI
Extracts key information from VCD file for automated verification reports.
"""

import sys
import os
from collections import defaultdict

def parse_vcd(vcd_file):
    """Parse VCD file and extract basic statistics."""
    signals = {}
    signal_changes = defaultdict(int)
    time_stamps = set()
    current_time = 0

    try:
        with open(vcd_file, 'r') as f:
            for line in f:
                line = line.strip()
                if line.startswith('$var'):
                    # $var wire 1 ! pc $end
                    parts = line.split()
                    if len(parts) >= 5:
                        var_type = parts[1]
                        width = int(parts[2])
                        symbol = parts[3]
                        name = parts[4]
                        signals[symbol] = {'name': name, 'type': var_type, 'width': width}
                elif line.startswith('$enddefinitions'):
                    continue  # Continue parsing the timeline
                elif line.startswith('#'):
                    current_time = int(line[1:])
                    time_stamps.add(current_time)
                elif line and not line.startswith('$'):
                    # Signal change: value symbol
                    parts = line.split()
                    if len(parts) == 2:
                        value, symbol = parts
                        if symbol in signals:
                            signal_changes[symbol] += 1

    except FileNotFoundError:
        return None

    return {
        'total_signals': len(signals),
        'signal_changes': dict(signal_changes),
        'time_stamps': sorted(time_stamps),
        'max_time': max(time_stamps) if time_stamps else 0,
        'signals': signals
    }

def main():
    vcd_path = sys.argv[1] if len(sys.argv) > 1 else 'thiele_cpu_tb.vcd'
    if not os.path.exists(vcd_path):
        print(f"VCD file not found: {vcd_path}")
        return

    data = parse_vcd(vcd_path)
    if not data:
        print("Failed to parse VCD")
        return

    print("=== VCD Waveform Analysis ===")
    print(f"Total signals: {data['total_signals']}")
    print(f"Simulation time range: 0 - {data['max_time']} ns")
    print(f"Time stamps: {len(data['time_stamps'])}")

    print("\nKey signals and changes:")
    key_signals = ['!', '@', '#', '$']  # Common symbols for pc, mu_accum, etc.
    for symbol in key_signals:
        if symbol in data['signals']:
            name = data['signals'][symbol]['name']
            changes = data['signal_changes'].get(symbol, 0)
            print(f"  {name} ({symbol}): {changes} changes")

    print("\nTop 5 signals by changes:")
    sorted_changes = sorted(data['signal_changes'].items(), key=lambda x: x[1], reverse=True)[:5]
    for symbol, changes in sorted_changes:
        name = data['signals'].get(symbol, {}).get('name', 'unknown')
        print(f"  {name} ({symbol}): {changes} changes")

    # Check for μ-enforcement activity
    mu_signals = [s for s in data['signals'] if 'mu' in data['signals'][s]['name'].lower()]
    total_mu_changes = sum(data['signal_changes'].get(s, 0) for s in mu_signals)
    print(f"\nμ-related signals: {len(mu_signals)}")
    print(f"Total μ signal changes: {total_mu_changes}")

if __name__ == '__main__':
    main()