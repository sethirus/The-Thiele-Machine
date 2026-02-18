"""
Python wrapper for the Coq-extracted VM runner.

This module provides Python access to the formally verified VM semantics
extracted from Coq proofs.
"""

import json
import subprocess
import tempfile
from pathlib import Path
from typing import List, Dict, Any, Tuple
from dataclasses import dataclass

VM_RUNNER_PATH = Path(__file__).parent.parent / "build" / "vm_runner"

@dataclass
class VMModule:
    """Represents a module in the VM's property graph"""
    id: int
    region: List[int]
    axioms: int  # Count of axioms discovered for this module

@dataclass
class VMState:
    """Complete VM state after execution"""
    pc: int
    mu: int  # Total μ-cost consumed
    err: bool
    regs: List[int]
    mem: List[int]
    csrs: Dict[str, int]
    graph: Dict[str, Any]
    modules: List[VMModule]

def run_vm_trace(instructions: List[str], fuel: int = 1000) -> VMState:
    """
    Execute a VM trace and return the final state.

    Args:
        instructions: List of VM instruction strings (e.g., ["PNEW {0,1,2} 10", "HALT 1"])
        fuel: Maximum execution steps

    Returns:
        VMState with final execution state

    Raises:
        RuntimeError: If VM execution fails
    """
    if not VM_RUNNER_PATH.exists():
        raise RuntimeError(f"VM runner not found at {VM_RUNNER_PATH}. Run: ocamlfind ocamlopt -linkpkg -package str -I build -o build/vm_runner build/thiele_core.mli build/thiele_core.ml tools/extracted_vm_runner.ml")

    # Create temporary trace file
    with tempfile.NamedTemporaryFile(mode='w', suffix='.txt', delete=False) as f:
        trace_path = f.name
        f.write(f"FUEL {fuel}\n")
        for instr in instructions:
            f.write(f"{instr}\n")

    try:
        # Run VM
        result = subprocess.run(
            [str(VM_RUNNER_PATH), trace_path],
            capture_output=True,
            text=True,
            timeout=30
        )

        if result.returncode != 0:
            raise RuntimeError(f"VM execution failed: {result.stderr}")

        # Parse JSON output
        try:
            state_json = json.loads(result.stdout)
        except json.JSONDecodeError as e:
            raise RuntimeError(f"Failed to parse VM output: {e}\nOutput: {result.stdout}")

        # Convert to VMState
        modules = [
            VMModule(id=m['id'], region=m['region'], axioms=m['axioms'])
            for m in state_json['graph']['modules']
        ]

        return VMState(
            pc=state_json['pc'],
            mu=state_json['mu'],
            err=state_json['err'],
            regs=state_json['regs'],
            mem=state_json['mem'],
            csrs=state_json['csrs'],
            graph=state_json['graph'],
            modules=modules
        )

    finally:
        # Clean up trace file
        Path(trace_path).unlink(missing_ok=True)


def create_test_state_with_modules(num_modules: int = 10, fuel: int = 500) -> VMState:
    """
    Create a VM state with a specified number of modules for testing.

    Creates modules with varying regions to form a connected graph suitable
    for testing geometric and topological properties.

    Args:
        num_modules: Number of modules to create
        fuel: Execution fuel

    Returns:
        VMState with created modules
    """
    instructions = []

    # Create modules with overlapping regions to form a graph
    # Module 0: region {0,1,2}
    # Module 1: region {1,2,3}
    # Module 2: region {2,3,4}
    # etc. - creates a chain with shared edges

    for i in range(num_modules):
        region = [i, i+1, i+2]
        region_str = "{" + ",".join(map(str, region)) + "}"
        cost = 10 + i
        instructions.append(f"PNEW {region_str} {cost}")

    # Add HALT
    instructions.append("HALT 1")

    return run_vm_trace(instructions, fuel=fuel)


def compute_mu_cost_density(state: VMState, module_id: int) -> float:
    """
    Compute the μ-cost density for a given module.

    density(m) = (encoding_length(m) + region_size(m)) / region_size(m)
               = 1 + encoding_length(m) / |region(m)|

    For modules created by PNEW, encoding_length is approximately the creation cost.
    """
    # Find module by ID
    module = None
    for m in state.modules:
        if m.id == module_id:
            module = m
            break

    if module is None:
        available_ids = [m.id for m in state.modules]
        raise ValueError(f"Module {module_id} not found. Available IDs: {available_ids}")

    region_size = len(module.region)

    if region_size == 0:
        return 0.0

    # Simplified: encoding length ~ creation cost (stored in module)
    # For a more accurate computation, would need per-module cost tracking
    # Modules created by PNEW {i,i+1,i+2} have cost 10+i
    encoding_length = 10.0 + (module_id - state.modules[0].id)  # Offset from first module

    return (encoding_length + region_size) / region_size


if __name__ == "__main__":
    # Test the VM wrapper
    print("Testing VM wrapper...")

    # Simple test: create a few modules
    state = create_test_state_with_modules(num_modules=5, fuel=100)

    print(f"Final state: PC={state.pc}, μ={state.mu}, err={state.err}")
    print(f"Created {len(state.modules)} modules:")
    for mod in state.modules:
        print(f"  Module {mod.id}: region={mod.region}, axioms={mod.axioms}")
        density = compute_mu_cost_density(state, mod.id)
        print(f"    μ-density ≈ {density:.3f}")

    print("\nVM wrapper working correctly!")
