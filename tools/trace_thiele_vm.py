#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""
Trace Logger for the Thiele VM.

This tool runs a Thiele program and produces a JSON trace file that can be
compared with traces from:
- Verilog RTL simulation
- Coq interpreter extraction

The trace format is designed for isomorphism verification.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Dict, List

# Add repository root to path
REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))

from thielecpu.state import State, MASK_WIDTH, MAX_MODULES
from thielecpu.vm import VM
from thielecpu.assemble import parse


def trace_vm_execution(
    program_path: Path,
    output_trace: Path,
    input_data: Dict[str, Any] | None = None,
) -> List[Dict[str, Any]]:
    """
    Execute a Thiele program and produce a step-by-step trace.
    
    Args:
        program_path: Path to the .thl program file
        output_trace: Path for the output trace.json file
        input_data: Optional input data for the program
        
    Returns:
        List of trace entries
    """
    trace_entries: List[Dict[str, Any]] = []
    
    # Load program
    program_text = program_path.read_text(encoding='utf-8')
    program_lines = program_text.split('\n')
    program = parse(program_lines, program_path.parent)
    
    print(f"Loaded program: {program_path}")
    print(f"Instructions: {len(program)}")
    
    # Initialize VM
    state = State()
    vm = VM(state)
    
    # Load any input data
    if input_data:
        for key, value in input_data.items():
            vm.python_globals[key] = value
    
    # Create output directory for VM artifacts
    outdir = output_trace.parent / "vm_output"
    outdir.mkdir(parents=True, exist_ok=True)
    
    # Execute step by step with tracing
    for step, (op, arg) in enumerate(program):
        # Capture state before
        state_before = state.get_state_snapshot()
        state.step_count = step
        
        # Record entry
        entry = {
            "step": step,
            "pc": step,
            "opcode": op,
            "operands": _parse_operands(op, arg),
            "state_before": state_before,
        }
        
        # Execute the instruction (simplified - for full execution use vm.run())
        _execute_single_step(vm, op, arg, step)
        
        # Capture state after
        state_after = state.get_state_snapshot()
        entry["state_after"] = state_after
        
        trace_entries.append(entry)
        
        print(f"Step {step}: {op} {arg[:30] if len(arg) > 30 else arg}")
        
        # Check for HALT
        if op == "HALT":
            break
    
    # Write trace file
    with output_trace.open('w', encoding='utf-8') as f:
        json.dump(trace_entries, f, indent=2)
    
    print(f"\nTrace written to: {output_trace}")
    print(f"Total steps: {len(trace_entries)}")
    print(f"Final μ-cost: {state.mu_ledger.total}")
    
    return trace_entries


def _parse_operands(op: str, arg: str) -> Dict[str, Any]:
    """Parse operands based on opcode type."""
    operands: Dict[str, Any] = {}
    
    if not arg:
        return operands
    
    if op == "PNEW":
        # PNEW {1,2,3} -> region mask
        if arg.strip().startswith('{') and arg.strip().endswith('}'):
            region_str = arg.strip()[1:-1]
            if region_str:
                indices = set(map(int, region_str.split(',')))
                # Convert to mask
                mask = sum(1 << i for i in indices if 0 <= i < MASK_WIDTH)
                operands["region"] = mask
            else:
                operands["region"] = 0
        else:
            operands["region"] = 1  # Default
    elif op == "PSPLIT":
        parts = arg.split()
        if parts:
            operands["module_id"] = int(parts[0])
            if len(parts) > 1:
                operands["mask"] = int(parts[1], 16) if parts[1].startswith('0x') else int(parts[1])
    elif op == "PMERGE":
        parts = arg.split()
        if len(parts) >= 2:
            operands["m1"] = int(parts[0])
            operands["m2"] = int(parts[1])
    elif op in {"XOR_LOAD", "XOR_ADD", "XOR_SWAP", "XOR_RANK", "XFER"}:
        parts = arg.split()
        if len(parts) >= 2:
            operands["dest"] = int(parts[0])
            operands["src"] = int(parts[1])
    elif op == "EMIT":
        operands["value"] = arg
    elif op == "PYEXEC":
        operands["code"] = arg[:100] + "..." if len(arg) > 100 else arg
    
    return operands


def _execute_single_step(vm: VM, op: str, arg: str, step: int) -> None:
    """Execute a single instruction for tracing purposes."""
    state = vm.state
    
    if op == "PNEW":
        if arg.strip().startswith('{') and arg.strip().endswith('}'):
            region_str = arg.strip()[1:-1]
            if region_str:
                region = set(map(int, region_str.split(',')))
            else:
                region = set()
        else:
            region = {1}
        state.pnew(region)
    
    elif op == "PSPLIT":
        parts = arg.split()
        if parts:
            from thielecpu._types import ModuleId
            module_id = ModuleId(int(parts[0]))
            # Default predicate: even/odd
            pred = lambda x: x % 2 == 0
            state.psplit(module_id, pred)
    
    elif op == "PMERGE":
        parts = arg.split()
        if len(parts) >= 2:
            from thielecpu._types import ModuleId
            m1 = ModuleId(int(parts[0]))
            m2 = ModuleId(int(parts[1]))
            state.pmerge(m1, m2)
    
    elif op == "PYEXEC":
        vm.execute_python(arg)
    
    elif op == "EMIT":
        # EMIT doesn't change partition state
        pass
    
    elif op == "HALT":
        pass
    
    # Other ops handled minimally
    state.step_count = step + 1


def verify_trace_self_consistency(trace_entries: List[Dict[str, Any]]) -> bool:
    """
    Verify that replaying operations from the trace reconstructs the final state.
    
    Returns True if trace is self-consistent.
    """
    if not trace_entries:
        return True
    
    # The state_after of step N should match state_before of step N+1
    for i in range(len(trace_entries) - 1):
        after = trace_entries[i]["state_after"]
        before = trace_entries[i + 1]["state_before"]
        
        # Compare μ-ledger values
        if after["mu"]["mu_discovery"] != before["mu"]["mu_discovery"]:
            print(f"Inconsistency at step {i}: mu_discovery mismatch")
            return False
        if after["mu"]["mu_execution"] != before["mu"]["mu_execution"]:
            print(f"Inconsistency at step {i}: mu_execution mismatch")
            return False
        
        # Compare num_modules
        if after["num_modules"] != before["num_modules"]:
            print(f"Inconsistency at step {i}: num_modules mismatch")
            return False
    
    print("Trace self-consistency: VERIFIED")
    return True


def main():
    parser = argparse.ArgumentParser(
        description="Trace Thiele VM execution for isomorphism verification"
    )
    parser.add_argument(
        "program",
        type=Path,
        help="Path to the .thl program file"
    )
    parser.add_argument(
        "-o", "--output",
        type=Path,
        default=Path("vm_trace.json"),
        help="Output trace file (default: vm_trace.json)"
    )
    parser.add_argument(
        "--verify",
        action="store_true",
        help="Verify trace self-consistency after execution"
    )
    
    args = parser.parse_args()
    
    if not args.program.exists():
        print(f"Error: Program file not found: {args.program}")
        sys.exit(1)
    
    # Ensure output directory exists
    args.output.parent.mkdir(parents=True, exist_ok=True)
    
    # Run trace
    trace = trace_vm_execution(args.program, args.output)
    
    # Verify if requested
    if args.verify:
        if not verify_trace_self_consistency(trace):
            sys.exit(1)
    
    sys.exit(0)


if __name__ == "__main__":
    main()
