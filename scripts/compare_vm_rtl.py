#!/usr/bin/env python3
"""
Compare VM and RTL counters for validation.

Usage: python compare_vm_rtl.py <vm_receipt.json> <rtl_log.json>
"""

import json
import sys
from pathlib import Path

def load_json(file_path):
    """Load JSON from file, or return text if not JSON."""
    with open(file_path, 'r') as f:
        content = f.read()
        try:
            return json.loads(content)
        except json.JSONDecodeError:
            # Return the text content
            return content

def extract_vm_counters(receipt):
    """Extract counters from VM receipt."""
    return receipt.get('counters', {})

def extract_rtl_counters(log_data):
    """Extract counters from RTL log JSON or embedded in log."""
    if isinstance(log_data, dict):
        # Already parsed JSON
        return log_data
    
    # If it's a string (log), extract the JSON part
    if isinstance(log_data, str):
        # Find the JSON block
        start = log_data.find('{')
        end = log_data.rfind('}') + 1
        if start != -1 and end != -1:
            json_str = log_data[start:end]
            try:
                return json.loads(json_str)
            except json.JSONDecodeError:
                pass
    
    # Fallback: assume it's already the dict
    return log_data

def normalize_mdl(mdl_bytes):
    """Normalize mdl_bytes to mdl_ops equivalent."""
    # Assume 1 byte = 1 operation for now
    # TODO: determine proper normalization factor
    return mdl_bytes

def compare_counters(vm_counters, rtl_counters):
    """Compare counters and return results."""
    results = {}
    
    # Partition ops: exact match
    vm_part = vm_counters.get('partition_ops', 0)
    rtl_part = rtl_counters.get('partition_ops', 0)
    results['partition_ops'] = {
        'vm': vm_part,
        'rtl': rtl_part,
        'match': vm_part == rtl_part,
        'diff': abs(vm_part - rtl_part)
    }
    
    # Info gain: within tolerance
    vm_info = vm_counters.get('info_gain', 0.0)
    rtl_info = rtl_counters.get('info_gain', 0.0)
    tolerance = 1e-6
    results['info_gain'] = {
        'vm': vm_info,
        'rtl': rtl_info,
        'match': abs(vm_info - rtl_info) < tolerance,
        'diff': abs(vm_info - rtl_info)
    }
    
    # MDL: normalized comparison
    vm_mdl_bytes = vm_counters.get('mdl_bytes', 0)
    rtl_mdl_ops = rtl_counters.get('mdl_ops', 0)
    vm_mdl_normalized = normalize_mdl(vm_mdl_bytes)
    mdl_tolerance = 1  # Allow some difference
    results['mdl'] = {
        'vm_bytes': vm_mdl_bytes,
        'vm_normalized': vm_mdl_normalized,
        'rtl_ops': rtl_mdl_ops,
        'match': abs(vm_mdl_normalized - rtl_mdl_ops) < mdl_tolerance,
        'diff': abs(vm_mdl_normalized - rtl_mdl_ops)
    }
    
    return results

def print_comparison_table(results):
    """Print comparison table."""
    print("VM ↔ RTL Counter Comparison")
    print("=" * 50)
    print(f"{'Counter':<15} {'VM':<10} {'RTL':<10} {'Match':<6} {'Diff':<10}")
    print("-" * 50)
    
    for counter, data in results.items():
        if counter == 'mdl':
            vm_val = f"{data['vm_bytes']}b"
            rtl_val = f"{data['rtl_ops']}ops"
            match = "✓" if data['match'] else "✗"
            diff = f"{data['diff']:.1f}"
        else:
            vm_val = str(data['vm'])
            rtl_val = str(data['rtl'])
            match = "✓" if data['match'] else "✗"
            diff = f"{data['diff']}"
        
        print(f"{counter:<15} {vm_val:<10} {rtl_val:<10} {match:<6} {diff:<10}")
    
    print("-" * 50)
    all_match = all(data['match'] for data in results.values())
    print(f"Overall: {'PASS' if all_match else 'FAIL'}")

def main():
    if len(sys.argv) != 3:
        print("Usage: python compare_vm_rtl.py <vm_receipt.json> <rtl_log.json>")
        sys.exit(1)
    
    vm_file = Path(sys.argv[1])
    rtl_file = Path(sys.argv[2])
    
    if not vm_file.exists():
        print(f"VM receipt file not found: {vm_file}")
        sys.exit(1)
    
    if not rtl_file.exists():
        print(f"RTL log file not found: {rtl_file}")
        sys.exit(1)
    
    try:
        vm_receipt = load_json(vm_file)
        rtl_log = load_json(rtl_file)
        
        vm_counters = extract_vm_counters(vm_receipt)
        rtl_counters = extract_rtl_counters(rtl_log)
        
        results = compare_counters(vm_counters, rtl_counters)
        print_comparison_table(results)
        
        # Exit code: 0 if all match, 1 if any mismatch
        all_match = all(data['match'] for data in results.values())
        sys.exit(0 if all_match else 1)
        
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)

if __name__ == '__main__':
    main()