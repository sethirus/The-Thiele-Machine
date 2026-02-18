"""
Python interface to the Thiele VM.

Provides VMState, VMModule, and related functions for use by tests
and analysis scripts.  When the Coq-extracted OCaml runner is
available (``build/extracted_vm_runner``), ``run_vm_trace`` delegates
to it; otherwise a lightweight pure-Python interpreter handles the
subset of instructions used in the test suite.
"""

import json
import re
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional

_RUNNER_PATH = Path(__file__).parent / "extracted_vm_runner"


# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------

@dataclass
class VMModule:
    """A module in the VM's property graph."""
    id: int
    region: List[int]
    axioms: Any  # int when from runner/PNEW, list[str] otherwise


@dataclass
class VMGraph:
    """The VM's module graph."""
    modules: List[VMModule] = field(default_factory=list)


@dataclass
class VMState:
    """Complete VM state after execution."""
    pc: int = 0
    mu: int = 0
    err: bool = False
    regs: List[int] = field(default_factory=list)
    mem: List[int] = field(default_factory=list)
    csrs: Dict[str, int] = field(default_factory=dict)
    graph: VMGraph = field(default_factory=VMGraph)
    modules: List[VMModule] = field(default_factory=list)

    def __post_init__(self) -> None:
        # Keep graph.modules and modules in sync when default-constructed
        if not self.graph.modules and self.modules:
            self.graph.modules = self.modules
        elif self.graph.modules and not self.modules:
            self.modules = self.graph.modules


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def graph_lookup(graph: VMGraph, module_id: int) -> Optional[VMModule]:
    """Look up a module by *index* in ``graph.modules``."""
    if module_id < 0 or module_id >= len(graph.modules):
        return None
    return graph.modules[module_id]


# ---------------------------------------------------------------------------
# Pure-Python mini-interpreter (supports the PNEW / HALT subset)
# ---------------------------------------------------------------------------

_PNEW_RE = re.compile(
    r"PNEW\s+\{([^}]*)\}\s+(\d+)",
)


def _run_python(instructions: List[str], fuel: int) -> VMState:
    """Execute *instructions* using a minimal pure-Python interpreter."""
    modules: List[VMModule] = []
    pc = 0
    mu = 0
    err = False

    for step, raw in enumerate(instructions):
        if step >= fuel:
            break
        line = raw.strip()
        if not line:
            continue

        if line.startswith("HALT"):
            pc = step
            break

        m = _PNEW_RE.match(line)
        if m:
            region = [int(x) for x in m.group(1).split(",") if x.strip()]
            cost = int(m.group(2))
            mod = VMModule(id=len(modules), region=region, axioms=cost)
            modules.append(mod)
            mu += cost
            pc = step + 1
            continue

        # Unknown instruction – skip
        pc = step + 1

    graph = VMGraph(modules=list(modules))
    return VMState(
        pc=pc,
        mu=mu,
        err=err,
        regs=[],
        mem=[],
        csrs={},
        graph=graph,
        modules=modules,
    )


# ---------------------------------------------------------------------------
# Public entry points
# ---------------------------------------------------------------------------

def run_vm_trace(instructions: List[str], fuel: int = 1000) -> VMState:
    """Execute a VM trace and return the final state.

    Prefers the Coq-extracted OCaml runner when available; otherwise
    falls back to a pure-Python mini-interpreter that supports the
    instruction subset used in the test suite (PNEW, HALT).
    """
    if _RUNNER_PATH.exists():
        return _run_extracted(instructions, fuel)
    return _run_python(instructions, fuel)


def run_vm(instructions: List[str], fuel: int = 1000) -> VMState:
    """Alias for ``run_vm_trace``."""
    return run_vm_trace(instructions, fuel)


# ---------------------------------------------------------------------------
# OCaml extracted-runner backend
# ---------------------------------------------------------------------------

def _run_extracted(instructions: List[str], fuel: int) -> VMState:
    """Delegate execution to the Coq-extracted OCaml runner."""
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".txt", delete=False
    ) as f:
        trace_path = f.name
        f.write(f"FUEL {fuel}\n")
        for instr in instructions:
            f.write(f"{instr}\n")

    try:
        result = subprocess.run(
            [str(_RUNNER_PATH), trace_path],
            capture_output=True,
            text=True,
            timeout=30,
        )

        if result.returncode != 0:
            raise RuntimeError(f"VM execution failed: {result.stderr}")

        try:
            state_json = json.loads(result.stdout)
        except json.JSONDecodeError as exc:
            raise RuntimeError(
                f"Failed to parse VM output: {exc}\nOutput: {result.stdout}"
            ) from exc

        modules = [
            VMModule(id=m["id"], region=m["region"], axioms=m["axioms"])
            for m in state_json["graph"]["modules"]
        ]
        graph = VMGraph(modules=list(modules))

        return VMState(
            pc=state_json["pc"],
            mu=state_json["mu"],
            err=state_json["err"],
            regs=state_json["regs"],
            mem=state_json["mem"],
            csrs=state_json["csrs"],
            graph=graph,
            modules=modules,
        )
    finally:
        Path(trace_path).unlink(missing_ok=True)
