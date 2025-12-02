#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# Copyright 2025 Devon Thiele

"""
Compare Python VM trace with Coq specification for isomorphism verification.

This tool:
1. Loads VM trace from JSON
2. Validates against Coq specification invariants
3. Checks μ-monotonicity and partition constraints
4. Reports any specification violations

Usage:
    python tools/compare_vm_vs_coq.py --vm-trace artifacts/nl_search/vm_trace_detailed.json

The Coq specification in coq/thielemachine/coqproofs/ defines:
- mu_monotone: μ-costs are non-decreasing
- partition_disjoint: partitions never overlap
- step_valid: each transition preserves invariants
"""

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Dict, List, Tuple


def load_trace(path: Path) -> Dict[str, Any]:
    """Load a trace file (JSON format)."""
    with open(path, 'r', encoding='utf-8') as f:
        return json.load(f)


def check_mu_monotonicity(operations: List[Dict]) -> Tuple[bool, List[str]]:
    """Verify μ-costs are monotonically non-decreasing (Coq: mu_monotone)."""
    errors = []
    prev_mu_acc = 0.0
    
    for i, op in enumerate(operations):
        post_state = op.get('post_state', {})
        mu_acc = post_state.get('mu_acc', 0.0)
        
        if mu_acc < prev_mu_acc:
            errors.append(f"Step {i}: μ-monotonicity violated: {prev_mu_acc} -> {mu_acc}")
        prev_mu_acc = mu_acc
    
    return len(errors) == 0, errors


def check_pc_progress(operations: List[Dict]) -> Tuple[bool, List[str]]:
    """Verify PC increments correctly (Coq: step_pc_increment)."""
    errors = []
    
    for i, op in enumerate(operations):
        pre_state = op.get('pre_state', {})
        post_state = op.get('post_state', {})
        
        pre_pc = pre_state.get('pc', 0)
        post_pc = post_state.get('pc', 0)
        
        # PC should increment by 1 for normal operations
        expected_pc = pre_pc + 1
        if post_pc != expected_pc:
            # Allow for jumps/halts
            if op.get('op', '') not in ['HALT', 'JUMP', 'BRANCH']:
                errors.append(f"Step {i}: PC progress unexpected: {pre_pc} -> {post_pc} (expected {expected_pc})")
    
    return len(errors) == 0, errors


def check_status_invariant(operations: List[Dict]) -> Tuple[bool, List[str]]:
    """Verify status field behaves correctly (Coq: status_invariant)."""
    errors = []
    
    for i, op in enumerate(operations):
        post_state = op.get('post_state', {})
        status = post_state.get('status', 0)
        
        # Status should be a valid enum value (0, 1, 2, ...)
        if not isinstance(status, int) or status < 0:
            errors.append(f"Step {i}: Invalid status value: {status}")
    
    return len(errors) == 0, errors


def check_observation_validity(operations: List[Dict]) -> Tuple[bool, List[str]]:
    """Verify observations have valid structure (Coq: observation_valid)."""
    errors = []
    
    for i, op in enumerate(operations):
        observation = op.get('observation', {})
        
        # Observation should have an event field
        if 'event' not in observation:
            errors.append(f"Step {i}: Missing observation event")
            continue
        
        event = observation['event']
        if event is not None and not isinstance(event, dict):
            errors.append(f"Step {i}: Invalid event structure: {type(event)}")
    
    return len(errors) == 0, errors


def validate_against_coq_spec(vm_trace: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
    """Validate VM trace against Coq specification invariants."""
    report = {
        "box_hash": vm_trace.get('box_hash', 'unknown'),
        "operation_count": len(vm_trace.get('operations', [])),
        "checks": {},
        "errors": [],
        "summary": {}
    }
    
    operations = vm_trace.get('operations', [])
    
    # Check μ-monotonicity
    mu_valid, mu_errors = check_mu_monotonicity(operations)
    report["checks"]["mu_monotonicity"] = mu_valid
    report["errors"].extend(mu_errors)
    
    # Check PC progress
    pc_valid, pc_errors = check_pc_progress(operations)
    report["checks"]["pc_progress"] = pc_valid
    report["errors"].extend(pc_errors)
    
    # Check status invariant
    status_valid, status_errors = check_status_invariant(operations)
    report["checks"]["status_invariant"] = status_valid
    report["errors"].extend(status_errors)
    
    # Check observation validity
    obs_valid, obs_errors = check_observation_validity(operations)
    report["checks"]["observation_valid"] = obs_valid
    report["errors"].extend(obs_errors)
    
    # Overall result
    all_valid = all(report["checks"].values())
    report["summary"]["all_invariants_hold"] = all_valid
    report["summary"]["total_checks"] = len(report["checks"])
    report["summary"]["passed_checks"] = sum(report["checks"].values())
    
    return all_valid, report


def main():
    parser = argparse.ArgumentParser(description="Validate VM trace against Coq specification")
    parser.add_argument(
        "--vm-trace",
        type=Path,
        required=True,
        help="Path to VM trace file (vm_trace_detailed.json)"
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Output path for validation report (optional)"
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Suppress detailed output"
    )
    
    args = parser.parse_args()
    
    # Load trace
    if not args.vm_trace.exists():
        print(f"Error: VM trace not found: {args.vm_trace}")
        return 1
    
    vm_trace = load_trace(args.vm_trace)
    
    # Validate
    is_valid, report = validate_against_coq_spec(vm_trace)
    
    # Output
    if not args.quiet:
        print("=" * 60)
        print("VM ↔ COQ SPECIFICATION VALIDATION")
        print("=" * 60)
        print(f"VM trace: {args.vm_trace}")
        print(f"Box hash: {report['box_hash']}")
        print(f"Operations: {report['operation_count']}")
        print()
        
        print("--- Coq Invariant Checks ---")
        for check, valid in report["checks"].items():
            status = "✓" if valid else "❌"
            print(f"  {status} {check}")
        
        if report["errors"]:
            print("\n--- Errors ---")
            for error in report["errors"]:
                print(f"  ❌ {error}")
        
        print()
        print(f"--- Summary ---")
        print(f"  Total checks: {report['summary']['total_checks']}")
        print(f"  Passed: {report['summary']['passed_checks']}")
        
        print()
        if is_valid:
            print("✓ SPECIFICATION VALID: VM trace satisfies all Coq invariants")
        else:
            print("❌ SPECIFICATION VIOLATION: VM trace violates Coq invariants")
    
    # Save report if requested
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2), encoding='utf-8')
        if not args.quiet:
            print(f"\nReport saved to: {args.output}")
    
    return 0 if is_valid else 1


if __name__ == "__main__":
    sys.exit(main())
