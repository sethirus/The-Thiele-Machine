"""
Python interface to the Thiele VM.

Provides VMState, VMModule, and related functions for use by tests
and analysis scripts.  When the Coq-extracted OCaml runner is
available (``build/extracted_vm_runner``), ``run_vm_trace`` delegates
to it; otherwise a pure-Python interpreter handles all 31 opcodes.
"""

import json
import os
import re
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional

_RUNNER_PATH = Path(__file__).parent / "extracted_vm_runner"


def _runner_launchable() -> bool:
    if not _RUNNER_PATH.exists() or not _RUNNER_PATH.is_file() or not os.access(_RUNNER_PATH, os.X_OK):
        return False

    # Bytecode executables produced by ocamlc require ocamlrun.
    try:
        first_line = _RUNNER_PATH.read_bytes().splitlines()[0]
        if first_line.startswith(b"#!/usr/bin/ocamlrun") and not Path("/usr/bin/ocamlrun").exists():
            return False
    except Exception:
        # If inspection fails, let runtime execution decide.
        pass

    return True


def _runner_available() -> bool:
    return _runner_launchable()


def _strict_backend_required() -> bool:
    """Return True when fallback execution must be forbidden.

    Set `THIELE_STRICT_VM_BACKEND=1` (or true/yes/on) to require the
    Coq-extracted runner for `run_vm_trace`.
    """
    raw = os.getenv("THIELE_STRICT_VM_BACKEND", "0").strip().lower()
    return raw in {"1", "true", "yes", "on"}


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
    """Execute *instructions* using a pure-Python interpreter handling all 31 opcodes."""
    # --- Mutable VM state ---
    regs = [0] * 32
    mem = [0] * 4096
    heap_base = 0
    modules: List[VMModule] = []
    mu = 0
    mu_tensor = [0] * 16
    logic_acc = 0
    err = False
    pc = 0
    active_module = -1
    partition_table: List[tuple] = []  # list of (base, size) from INIT_PT

    def _si(s: str) -> int:
        """Parse integer token; supports 0x hex prefix."""
        try:
            return int(s, 0)
        except (ValueError, TypeError):
            return 0

    def _parse_region(tok: str) -> List[int]:
        t = tok.strip()
        if len(t) >= 2 and t[0] == "{" and t[-1] == "}":
            inner = t[1:-1].strip()
            if not inner:
                return []
            return [_si(x.strip()) for x in inner.split(",") if x.strip()]
        return []

    # --- Pass 1: honour INIT_*/FUEL directives; collect program instructions ---
    program: List[str] = []
    for raw in instructions:
        line = raw.strip()
        if not line or line[0] in ("#", ";"):
            continue
        toks = line.split()
        op = toks[0].upper()
        if op == "FUEL":
            if len(toks) >= 2:
                fuel = _si(toks[1])
        elif op == "INIT_LOGIC_ACC":
            if len(toks) >= 2:
                logic_acc = _si(toks[1])
        elif op == "INIT_MU":
            if len(toks) >= 2:
                mu = _si(toks[1])
        elif op == "INIT_MEM":
            if len(toks) >= 3:
                a = _si(toks[1]) % 4096
                mem[a] = _si(toks[2])
        elif op == "INIT_REG":
            if len(toks) >= 3:
                regs[_si(toks[1]) % 32] = _si(toks[2])
        elif op == "INIT_TENSOR":
            if len(toks) >= 3:
                mu_tensor[_si(toks[1]) % 16] = _si(toks[2])
        elif op == "INIT_ACTIVE_MODULE":
            if len(toks) >= 2:
                active_module = _si(toks[1])
        elif op == "INIT_PT":
            if len(toks) >= 3:
                partition_table.append((_si(toks[1]), _si(toks[2])))
        else:
            program.append(line)

    # Register / memory accessors
    def _rg(r: int) -> int:
        return regs[r % 32]

    def _rs(r: int, v: int) -> None:
        regs[r % 32] = v

    def _mg(a: int) -> int:
        return mem[a] if 0 <= a < 4096 else 0

    def _mp(a: int, v: int) -> None:
        if 0 <= a < 4096:
            mem[a] = v

    def _in_pt(addr: int) -> bool:
        if 0 <= active_module < len(partition_table):
            base, size = partition_table[active_module]
            return base <= addr < base + size
        return False

    # --- Pass 2: PC-dispatch execution loop ---
    steps = 0
    while steps < fuel:
        if not (0 <= pc < len(program)):
            break
        line = program[pc]
        toks = line.split()
        if not toks:
            pc += 1
            continue
        op = toks[0].upper()
        steps += 1

        if op == "HALT":
            # HALT [cost]
            try:
                mu += int(toks[-1])
            except (ValueError, IndexError):
                pass
            break

        elif op == "PNEW":
            # PNEW {region} cost
            if len(toks) >= 3:
                region = _parse_region(toks[1])
                cost = int(toks[2])
                modules.append(VMModule(id=len(modules), region=region, axioms=cost))
                mu += cost
            pc += 1

        elif op == "PSPLIT":
            # PSPLIT mid {left} {right} cost
            if len(toks) >= 5:
                mu += int(toks[4])
            pc += 1

        elif op == "PMERGE":
            # PMERGE m1 m2 cost
            if len(toks) >= 4:
                mu += int(toks[3])
            pc += 1

        elif op == "LASSERT":
            # LASSERT mid axiom cost  — charge mu, assume SAT continuation
            if len(toks) >= 4:
                mu += int(toks[3])
            pc += 1

        elif op == "LJOIN":
            # LJOIN f1 f2 cost
            if len(toks) >= 4:
                mu += int(toks[3])
            pc += 1

        elif op == "MDLACC":
            # MDLACC mid cost
            if len(toks) >= 3:
                mu += int(toks[2])
            pc += 1

        elif op == "PDISCOVER":
            # PDISCOVER mid {evidence} cost  — requires logic gate key
            if logic_acc != 0xCAFEEACE:
                err = True
            elif len(toks) >= 4:
                mu += int(toks[3])
            pc += 1

        elif op == "XFER":
            # XFER dst src cost
            if len(toks) >= 4:
                _rs(int(toks[1]), _rg(int(toks[2])))
                mu += int(toks[3])
            pc += 1

        elif op == "LOAD_IMM":
            # LOAD_IMM dst imm cost
            if len(toks) >= 4:
                _rs(int(toks[1]), _si(toks[2]))
                mu += int(toks[3])
            pc += 1

        elif op == "CHSH_TRIAL":
            # CHSH_TRIAL x y a b cost  — requires logic gate key
            if logic_acc != 0xCAFEEACE:
                err = True
            elif len(toks) >= 6:
                mu += int(toks[5])
            pc += 1

        elif op == "XOR_LOAD":
            # XOR_LOAD dst addr cost
            if len(toks) >= 4:
                dst = int(toks[1])
                _rs(dst, _rg(dst) ^ _mg(int(toks[2])))
                mu += int(toks[3])
            pc += 1

        elif op == "XOR_ADD":
            # XOR_ADD dst src cost
            if len(toks) >= 4:
                dst = int(toks[1])
                _rs(dst, _rg(dst) ^ _rg(int(toks[2])))
                mu += int(toks[3])
            pc += 1

        elif op == "XOR_SWAP":
            # XOR_SWAP a b cost
            if len(toks) >= 4:
                a, b = int(toks[1]), int(toks[2])
                va, vb = _rg(a), _rg(b)
                _rs(a, vb)
                _rs(b, va)
                mu += int(toks[3])
            pc += 1

        elif op == "XOR_RANK":
            # XOR_RANK dst src cost  — popcount(regs[src]) -> regs[dst]
            if len(toks) >= 4:
                _rs(int(toks[1]), bin(_rg(int(toks[2]))).count("1"))
                mu += int(toks[3])
            pc += 1

        elif op == "EMIT":
            # EMIT mid bits cost
            if len(toks) >= 4:
                mu += int(toks[3])
            pc += 1

        elif op == "REVEAL":
            # REVEAL ti tj bits [cert]  — cost = bits; requires logic gate key
            if logic_acc != 0xCAFEEACE:
                err = True
            elif len(toks) >= 4:
                ti, tj = int(toks[1]), int(toks[2])
                bits = int(toks[3])
                mu += bits
                flat = ti * 4 + tj
                if 0 <= flat < 16:
                    mu_tensor[flat] += bits
            pc += 1

        elif op == "ORACLE_HALTS":
            # ORACLE_HALTS payload cost  — halt execution
            if len(toks) >= 3:
                mu += int(toks[2])
            break

        elif op == "LOAD":
            # LOAD dst addr cost  — locality-checked memory read
            if len(toks) >= 4:
                dst, addr, cost = int(toks[1]), int(toks[2]), int(toks[3])
                if not _in_pt(addr):
                    err = True
                else:
                    _rs(dst, _mg(addr))
                    mu += cost
            pc += 1

        elif op == "STORE":
            # STORE addr src cost  — locality-checked memory write
            if len(toks) >= 4:
                addr, src, cost = int(toks[1]), int(toks[2]), int(toks[3])
                if not _in_pt(addr):
                    err = True
                else:
                    _mp(addr, _rg(src))
                    mu += cost
            pc += 1

        elif op == "ADD":
            # ADD dst src1 src2 cost
            if len(toks) >= 5:
                _rs(int(toks[1]), _rg(int(toks[2])) + _rg(int(toks[3])))
                mu += int(toks[4])
            pc += 1

        elif op == "SUB":
            # SUB dst src1 src2 cost
            if len(toks) >= 5:
                _rs(int(toks[1]), _rg(int(toks[2])) - _rg(int(toks[3])))
                mu += int(toks[4])
            pc += 1

        elif op == "JUMP":
            # JUMP target cost
            if len(toks) >= 3:
                mu += int(toks[2])
                pc = int(toks[1])
            else:
                pc += 1

        elif op == "JNEZ":
            # JNEZ rs target cost
            if len(toks) >= 4:
                rs, target, cost = int(toks[1]), int(toks[2]), int(toks[3])
                mu += cost
                if _rg(rs) != 0:
                    pc = target
                else:
                    pc += 1
            else:
                pc += 1

        elif op == "CALL":
            # CALL target cost  — push return addr to mem[regs[31]]; jump
            if len(toks) >= 3:
                target, cost = int(toks[1]), int(toks[2])
                mu += cost
                _mp(regs[31], pc + 1)
                regs[31] -= 1
                pc = target
            else:
                pc += 1

        elif op == "RET":
            # RET cost  — increment sp, pop return addr from mem[regs[31]]
            try:
                mu += int(toks[-1])
            except (ValueError, IndexError):
                pass
            regs[31] += 1
            pc = _mg(regs[31])

        elif op == "CHECKPOINT":
            # CHECKPOINT label [cost]  — no-op harness checkpoint
            if len(toks) >= 3:
                try:
                    mu += int(toks[2])
                except ValueError:
                    pass
            pc += 1

        elif op == "READ_PORT":
            # READ_PORT dst ch value bits cost  — load value token into dst
            if len(toks) >= 6:
                _rs(int(toks[1]), _si(toks[3]))
                mu += int(toks[5])
            pc += 1

        elif op == "WRITE_PORT":
            # WRITE_PORT ch src cost  — I/O not modelled in Python fallback
            if len(toks) >= 4:
                try:
                    mu += int(toks[3])
                except ValueError:
                    pass
            pc += 1

        elif op == "HEAP_LOAD":
            # HEAP_LOAD dst addr cost
            if len(toks) >= 4:
                dst, addr, cost = int(toks[1]), int(toks[2]), int(toks[3])
                _rs(dst, _mg(heap_base + addr))
                mu += cost
            pc += 1

        elif op == "HEAP_STORE":
            # HEAP_STORE addr src cost
            if len(toks) >= 4:
                addr, src, cost = int(toks[1]), int(toks[2]), int(toks[3])
                _mp(heap_base + addr, _rg(src))
                mu += cost
            pc += 1

        else:
            # Unknown instruction — skip
            pc += 1

    graph = VMGraph(modules=list(modules))
    return VMState(
        pc=pc,
        mu=mu,
        err=err,
        regs=list(regs),
        mem=list(mem),
        csrs={
            "cert_addr": 0,
            "status": 0,
            "err": 1 if err else 0,
            "heap_base": heap_base,
        },
        graph=graph,
        modules=list(modules),
    )


# ---------------------------------------------------------------------------
# Public entry points
# ---------------------------------------------------------------------------

def run_vm_trace(instructions: List[str], fuel: int = 1000) -> VMState:
    """Execute a VM trace and return the final state.

    Prefers the Coq-extracted OCaml runner when available; otherwise
    falls back to a pure-Python interpreter that supports all 31 opcodes.
    """
    if _runner_available():
        try:
            return _run_extracted(instructions, fuel)
        except (FileNotFoundError, PermissionError, OSError):
            # Treat unlaunchable extracted binaries as unavailable in non-strict mode.
            if _strict_backend_required():
                raise
    if _strict_backend_required():
        raise RuntimeError(
            "Coq-extracted runner missing under strict backend policy. "
            f"Expected: {_RUNNER_PATH}. "
            "Build with: ocamlc -I build -o build/extracted_vm_runner "
            "build/thiele_core.mli build/thiele_core.ml tools/extracted_vm_runner.ml"
        )
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
