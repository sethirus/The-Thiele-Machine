"""
Python interface to the Thiele VM.

This is a thin wrapper around thielecpu/vm.py (the Coq-extracted Python VM).
All 38 opcodes are handled by the formally-derived VM from coq/Extraction.v.

Backend priority:
  1. Coq-extracted OCaml binary (extracted_vm_runner) - when available
  2. Coq-extracted Python VM (thielecpu/vm.py) - THE definitive Python VM
"""

import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional

# Import THE definitive Coq-extracted Python VM
sys.path.insert(0, str(Path(__file__).parent.parent))
from thielecpu import vm as extracted_vm

_RUNNER_PATH = Path(__file__).parent / "extracted_vm_runner"


def _runner_available() -> bool:
    """Check if the OCaml extracted runner is available."""
    if not _RUNNER_PATH.exists() or not _RUNNER_PATH.is_file():
        return False
    if not os.access(_RUNNER_PATH, os.X_OK):
        return False
    # Check if ocamlrun is available for bytecode executables
    try:
        first_line = _RUNNER_PATH.read_bytes().splitlines()[0]
        if first_line.startswith(b"#!/usr/bin/ocamlrun"):
            return Path("/usr/bin/ocamlrun").exists()
    except Exception:
        pass
    return True


def _strict_backend_required() -> bool:
    """Return True when THIELE_STRICT_VM_BACKEND=1 is set."""
    raw = os.getenv("THIELE_STRICT_VM_BACKEND", "0").strip().lower()
    return raw in {"1", "true", "yes", "on"}


# ---------------------------------------------------------------------------
# Data classes (external API)
# ---------------------------------------------------------------------------

@dataclass
class VMModule:
    """A module in the VM's property graph."""
    id: int
    region: List[int]
    axioms: Any

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
    mu_tensor: List[int] = field(default_factory=list)
    logic_acc: int = 0
    mstatus: int = 0
    certified: bool = False
    witness: List[int] = field(default_factory=lambda: [0] * 8)

    def __post_init__(self) -> None:
        if not self.graph.modules and self.modules:
            self.graph.modules = self.modules
        elif self.graph.modules and not self.modules:
            self.modules = self.graph.modules

    @property
    def supra_cert(self) -> bool:
        """True iff csr_cert_addr != 0.

        This matches Coq's has_supra_cert predicate:
            Definition has_supra_cert (s : VMState) : Prop :=
              s.(vm_csrs).(csr_cert_addr) <> 0.

        Distinct from `certified` (which reflects vm_certified, set only
        by the CERTIFY opcode). MORPH_ASSERT sets csr_cert_addr (and thus
        supra_cert) but does NOT set vm_certified.

        The NoFI theorems in AbstractNoFI.v and NoFreeInsight.v operate
        on has_supra_cert, so supra_cert is the correct field to observe
        when checking whether a formal structural claim has been recorded.
        """
        return self.csrs.get("cert_addr", 0) != 0


def graph_lookup(graph: VMGraph, module_id: int) -> Optional[VMModule]:
    """Look up a module by index in graph.modules."""
    if module_id < 0 or module_id >= len(graph.modules):
        return None
    return graph.modules[module_id]


# ---------------------------------------------------------------------------
# Instruction parser: textual format → dict format for extracted VM
# ---------------------------------------------------------------------------

def _parse_int(s: str) -> int:
    """Parse integer, supports 0x hex prefix and rN register aliases."""
    try:
        return int(s, 0)
    except (ValueError, TypeError):
        # Handle register aliases r0-r31
        if isinstance(s, str) and len(s) >= 2 and s[0].lower() == 'r':
            try:
                return int(s[1:]) & 0x1F
            except (ValueError, TypeError):
                pass
        return 0


def _parse_region(tok: str) -> List[int]:
    """Parse region token: {1,2,3} → [1,2,3]"""
    t = tok.strip()
    if len(t) >= 2 and t[0] == "{" and t[-1] == "}":
        inner = t[1:-1].strip()
        if not inner:
            return []
        return [_parse_int(x.strip()) for x in inner.split(",") if x.strip()]
    return []


def _parse_instruction_dict(toks: List[str]) -> Optional[Dict[str, Any]]:
    """Parse textual instruction tokens into dict format for thiele_vm_extracted."""
    if not toks:
        return None

    op = toks[0].upper()

    # Map textual format to dict format
    if op == "PNEW" and len(toks) >= 3:
        return {"op": "pnew", "region": _parse_region(toks[1]), "cost": _parse_int(toks[2])}
    elif op == "PSPLIT" and len(toks) >= 5:
        return {"op": "psplit", "module": _parse_int(toks[1]), "left": _parse_region(toks[2]),
                "right": _parse_region(toks[3]), "cost": _parse_int(toks[4])}
    elif op == "PMERGE" and len(toks) >= 4:
        return {"op": "pmerge", "m1": _parse_int(toks[1]), "m2": _parse_int(toks[2]), "cost": _parse_int(toks[3])}
    elif op == "LASSERT" and len(toks) >= 4:
        return {"op": "lassert", "module": _parse_int(toks[1]), "formula": toks[2],
                "cert": {"type": "sat", "proof": ""}, "cost": _parse_int(toks[3])}
    elif op == "LJOIN" and len(toks) >= 4:
        return {"op": "ljoin", "cert1": toks[1], "cert2": toks[2], "cost": _parse_int(toks[3])}
    elif op == "MDLACC" and len(toks) >= 3:
        return {"op": "mdlacc", "cost": _parse_int(toks[2])}
    elif op == "PDISCOVER" and len(toks) >= 4:
        return {"op": "pdiscover", "module": _parse_int(toks[1]), "evidence": [], "cost": _parse_int(toks[3])}
    elif op == "XFER" and len(toks) >= 4:
        return {"op": "xfer", "dst": _parse_int(toks[1]), "src": _parse_int(toks[2]), "cost": _parse_int(toks[3])}
    elif op == "LOAD_IMM" and len(toks) >= 4:
        return {"op": "load_imm", "dst": _parse_int(toks[1]), "imm": _parse_int(toks[2]), "cost": _parse_int(toks[3])}
    elif op == "LOAD" and len(toks) >= 4:
        return {"op": "load", "dst": _parse_int(toks[1]), "addr": _parse_int(toks[2]), "cost": _parse_int(toks[3])}
    elif op == "STORE" and len(toks) >= 4:
        return {"op": "store", "addr": _parse_int(toks[1]), "src": _parse_int(toks[2]), "cost": _parse_int(toks[3])}
    elif op == "ADD" and len(toks) >= 5:
        return {"op": "add", "dst": _parse_int(toks[1]), "rs1": _parse_int(toks[2]),
                "rs2": _parse_int(toks[3]), "cost": _parse_int(toks[4])}
    elif op == "SUB" and len(toks) >= 5:
        return {"op": "sub", "dst": _parse_int(toks[1]), "rs1": _parse_int(toks[2]),
                "rs2": _parse_int(toks[3]), "cost": _parse_int(toks[4])}
    elif op == "JUMP" and len(toks) >= 3:
        return {"op": "jump", "target": _parse_int(toks[1]), "cost": _parse_int(toks[2])}
    elif op == "JNEZ" and len(toks) >= 4:
        return {"op": "jnez", "rs": _parse_int(toks[1]), "target": _parse_int(toks[2]), "cost": _parse_int(toks[3])}
    elif op == "CALL" and len(toks) >= 3:
        return {"op": "call", "target": _parse_int(toks[1]), "cost": _parse_int(toks[2])}
    elif op == "RET" and len(toks) >= 2:
        return {"op": "ret", "cost": _parse_int(toks[1])}
    elif op == "CHSH_TRIAL" and len(toks) >= 6:
        return {"op": "chsh_trial", "x": _parse_int(toks[1]), "y": _parse_int(toks[2]),
                "a": _parse_int(toks[3]), "b": _parse_int(toks[4]), "cost": _parse_int(toks[5])}
    elif op == "XOR_LOAD" and len(toks) >= 4:
        return {"op": "xor_load", "dst": _parse_int(toks[1]), "addr": _parse_int(toks[2]), "cost": _parse_int(toks[3])}
    elif op == "XOR_ADD" and len(toks) >= 4:
        return {"op": "xor_add", "dst": _parse_int(toks[1]), "src": _parse_int(toks[2]), "cost": _parse_int(toks[3])}
    elif op == "XOR_SWAP" and len(toks) >= 4:
        return {"op": "xor_swap", "a": _parse_int(toks[1]), "b": _parse_int(toks[2]), "cost": _parse_int(toks[3])}
    elif op == "XOR_RANK" and len(toks) >= 4:
        return {"op": "xor_rank", "dst": _parse_int(toks[1]), "src": _parse_int(toks[2]), "cost": _parse_int(toks[3])}
    elif op == "EMIT" and len(toks) >= 4:
        return {"op": "emit", "module": _parse_int(toks[1]), "payload": toks[2], "cost": _parse_int(toks[3])}
    elif op == "REVEAL" and len(toks) >= 4:
        return {"op": "reveal", "module": _parse_int(toks[1]), "bits": _parse_int(toks[2]),
                "cert": toks[3] if len(toks) > 4 else "", "cost": _parse_int(toks[min(4, len(toks)-1)])}
    elif op == "ORACLE_HALTS" and len(toks) >= 3:
        return {"op": "oracle_halts", "cost": _parse_int(toks[2])}
    elif op == "HALT":
        return {"op": "halt", "cost": _parse_int(toks[1]) if len(toks) >= 2 else 0}
    elif op == "CHECKPOINT" and len(toks) >= 2:
        return {"op": "checkpoint", "cost": _parse_int(toks[2]) if len(toks) >= 3 else 0}
    elif op == "READ_PORT" and len(toks) >= 6:
        return {"op": "read_port", "dst": _parse_int(toks[1]), "channel": _parse_int(toks[2]),
                "value": _parse_int(toks[3]), "bits": _parse_int(toks[4]), "cost": _parse_int(toks[5])}
    elif op == "WRITE_PORT" and len(toks) >= 4:
        return {"op": "write_port", "channel": _parse_int(toks[1]), "src": _parse_int(toks[2]), "cost": _parse_int(toks[3])}
    elif op == "HEAP_LOAD" and len(toks) >= 4:
        return {"op": "heap_load", "dst": _parse_int(toks[1]), "addr": _parse_int(toks[2]), "cost": _parse_int(toks[3])}
    elif op == "HEAP_STORE" and len(toks) >= 4:
        return {"op": "heap_store", "addr": _parse_int(toks[1]), "src": _parse_int(toks[2]), "cost": _parse_int(toks[3])}
    elif op == "CERTIFY" and len(toks) >= 2:
        return {"op": "certify", "cost": _parse_int(toks[1])}
    elif op == "AND" and len(toks) >= 5:
        return {"op": "and_", "dst": _parse_int(toks[1]), "rs1": _parse_int(toks[2]),
                "rs2": _parse_int(toks[3]), "cost": _parse_int(toks[4])}
    elif op == "OR" and len(toks) >= 5:
        return {"op": "or_", "dst": _parse_int(toks[1]), "rs1": _parse_int(toks[2]),
                "rs2": _parse_int(toks[3]), "cost": _parse_int(toks[4])}
    elif op == "SHL" and len(toks) >= 5:
        return {"op": "shl", "dst": _parse_int(toks[1]), "rs1": _parse_int(toks[2]),
                "rs2": _parse_int(toks[3]), "cost": _parse_int(toks[4])}
    elif op == "SHR" and len(toks) >= 5:
        return {"op": "shr", "dst": _parse_int(toks[1]), "rs1": _parse_int(toks[2]),
                "rs2": _parse_int(toks[3]), "cost": _parse_int(toks[4])}
    elif op == "MUL" and len(toks) >= 5:
        return {"op": "mul", "dst": _parse_int(toks[1]), "rs1": _parse_int(toks[2]),
                "rs2": _parse_int(toks[3]), "cost": _parse_int(toks[4])}
    elif op == "LUI" and len(toks) >= 4:
        return {"op": "lui", "dst": _parse_int(toks[1]), "imm": _parse_int(toks[2]), "cost": _parse_int(toks[3])}
    elif op == "TENSOR_SET" and len(toks) >= 6:
        return {"op": "tensor_set", "module": _parse_int(toks[1]), "i": _parse_int(toks[2]),
                "j": _parse_int(toks[3]), "value": _parse_int(toks[4]), "mu_delta": _parse_int(toks[5])}
    elif op == "TENSOR_GET" and len(toks) >= 6:
        return {"op": "tensor_get", "dst": _parse_int(toks[1]), "module": _parse_int(toks[2]),
                "i": _parse_int(toks[3]), "j": _parse_int(toks[4]), "mu_delta": _parse_int(toks[5])}
    # Phase 5: categorical morphism opcodes (0x27–0x2D) — mirrors extracted_vm_runner.ml lines 391-404
    elif op == "MORPH" and len(toks) >= 6:
        return {"op": "morph", "dst": _parse_int(toks[1]), "src_mod": _parse_int(toks[2]),
                "dst_mod": _parse_int(toks[3]), "coupling_idx": _parse_int(toks[4]), "cost": _parse_int(toks[5])}
    elif op == "COMPOSE" and len(toks) >= 5:
        return {"op": "compose", "dst": _parse_int(toks[1]), "m1_id": _parse_int(toks[2]),
                "m2_id": _parse_int(toks[3]), "cost": _parse_int(toks[4])}
    elif op == "MORPH_ID" and len(toks) >= 4:
        return {"op": "morph_id", "dst": _parse_int(toks[1]), "module": _parse_int(toks[2]),
                "cost": _parse_int(toks[3])}
    elif op == "MORPH_DELETE" and len(toks) >= 3:
        return {"op": "morph_delete", "morph_id": _parse_int(toks[1]), "cost": _parse_int(toks[2])}
    elif op == "MORPH_ASSERT" and len(toks) >= 5:
        return {"op": "morph_assert", "morph_id": _parse_int(toks[1]), "property": toks[2],
                "cert": toks[3], "cost": _parse_int(toks[4])}
    elif op == "MORPH_TENSOR" and len(toks) >= 5:
        return {"op": "morph_tensor", "dst": _parse_int(toks[1]), "f_id": _parse_int(toks[2]),
                "g_id": _parse_int(toks[3]), "cost": _parse_int(toks[4])}
    elif op == "MORPH_GET" and len(toks) >= 5:
        return {"op": "morph_get", "dst": _parse_int(toks[1]), "morph_id": _parse_int(toks[2]),
                "selector": _parse_int(toks[3]), "cost": _parse_int(toks[4])}

    return None


# ---------------------------------------------------------------------------
# Main execution: uses Coq-extracted Python VM
# ---------------------------------------------------------------------------

def _run_extracted_py(instructions: List[str], fuel: int) -> VMState:
    """
    Execute using THE definitive Coq-extracted Python VM.
    Translates textual instruction format to dict format, runs extraction, returns result.
    """
    # Initialize state from INIT directives
    init_state = extracted_vm.VMState.default()
    program = []

    for raw in instructions:
        line = raw.strip()
        if not line or line[0] in ("#", ";"):
            continue
        toks = line.split()
        op = toks[0].upper()

        # Handle INIT directives
        if op == "FUEL":
            if len(toks) >= 2:
                fuel = _parse_int(toks[1])
        elif op == "INIT_REG":
            if len(toks) >= 3:
                init_state.vm_regs[_parse_int(toks[1]) % 32] = _parse_int(toks[2])
        elif op == "INIT_MEM":
            if len(toks) >= 3:
                init_state.vm_mem[_parse_int(toks[1]) % 65536] = _parse_int(toks[2])
        elif op == "INIT_MU":
            if len(toks) >= 2:
                init_state.vm_mu = _parse_int(toks[1])
        elif op == "INIT_TENSOR":
            if len(toks) >= 3:
                init_state.vm_mu_tensor[_parse_int(toks[1]) % 16] = _parse_int(toks[2])
        elif op == "INIT_LOGIC_ACC":
            if len(toks) >= 2:
                init_state.vm_logic_acc = _parse_int(toks[1])
        elif op == "INIT_ACTIVE_MODULE":
            if len(toks) >= 2:
                # Set active module in CSR status (matches Kami active_module register)
                pass  # Active module is hardware-only state, skip in Python fallback
        elif op == "INIT_PT":
            # Partition table init is handled via graph operations
            pass
        elif op.startswith("INIT_"):
            pass
        else:
            # Parse instruction
            instr = _parse_instruction_dict(toks)
            if instr:
                program.append(instr)

    # Execute through Coq-extracted VM
    final_state = extracted_vm.vm_run(init_state, program, max_steps=fuel)

    # Convert to external VMState format — use actual graph modules (id, region, axioms)
    modules = [
        VMModule(id=mid, region=list(ms.module_region), axioms=len(ms.module_axioms))
        for mid, ms in final_state.vm_graph.pg_modules
    ]
    graph = VMGraph(modules=modules)

    return VMState(
        pc=final_state.vm_pc,
        mu=final_state.vm_mu,
        err=final_state.vm_err,
        regs=list(final_state.vm_regs),
        mem=list(final_state.vm_mem),
        csrs={
            "cert_addr": final_state.vm_csrs.csr_cert_addr,
            "status": final_state.vm_csrs.csr_status,
            "err": final_state.vm_csrs.csr_err,
            "heap_base": final_state.vm_csrs.csr_heap_base,
        },
        graph=graph,
        modules=modules,
        mu_tensor=list(final_state.vm_mu_tensor),
        logic_acc=final_state.vm_logic_acc,
        mstatus=final_state.vm_mstatus,
        certified=final_state.vm_certified,
        witness=list(final_state.vm_witness),
    )


# ---------------------------------------------------------------------------
# OCaml extracted-runner backend (when available)
# ---------------------------------------------------------------------------

_OCAML_ONLY_INIT = {"INIT_REG", "INIT_MEM", "MEM_SIZE", "INIT_LOGIC_ACC", "INIT_ACTIVE_MODULE", "INIT_PT", "INIT_TENSOR"}

_REG_ALIAS_RE = re.compile(r'\br(\d+)\b')


def _translate_reg_names(line: str) -> str:
    """Translate register aliases rN → N for the OCaml runner."""
    return _REG_ALIAS_RE.sub(lambda m: str(int(m.group(1)) & 0x1F), line)


def _run_ocaml(instructions: List[str], fuel: int) -> VMState:
    """Delegate execution to the Coq-extracted OCaml runner."""
    with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:
        trace_path = f.name
        f.write(f"FUEL {fuel}\n")
        for instr in instructions:
            line = instr.strip()
            if not line or line[0] in ("#", ";"):
                continue
            toks = line.split()
            op = toks[0].upper()
            # Skip RTL-only directives unknown to the OCaml runner
            if op.startswith("INIT_") and op not in _OCAML_ONLY_INIT:
                continue
            # Translate register aliases (r1 → 1) for OCaml runner
            line = _translate_reg_names(line)
            # OCaml runner requires HALT to have a cost argument
            if op == "HALT" and len(toks) == 1:
                f.write("HALT 1\n")
            else:
                f.write(f"{line}\n")

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
            mem=(lambda m: m + [0] * (65536 - len(m)))(state_json["mem"]),
            csrs=state_json["csrs"],
            graph=graph,
            modules=modules,
            mu_tensor=state_json.get("mu_tensor", []),
            logic_acc=state_json.get("logic_acc", 0),
            mstatus=state_json.get("mstatus", 0),
            certified=state_json.get("certified", False),
            witness=state_json.get("witness", [0] * 8),
        )
    finally:
        Path(trace_path).unlink(missing_ok=True)


# ---------------------------------------------------------------------------
# Backend aliases (used by tests for monkeypatching)
# ---------------------------------------------------------------------------

#: Alias: OCaml extracted binary runner backend
_run_extracted = _run_ocaml

#: Alias: Coq-extracted Python VM backend
_run_python = _run_extracted_py


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def run_vm_trace(instructions: List[str], fuel: int = 1000) -> VMState:
    """Execute a VM trace and return the final state.

    Backend priority:
      1. Coq-extracted OCaml binary (extracted_vm_runner) - when available
      2. Coq-extracted Python VM (thielecpu/vm.py) - THE definitive Python VM

    All 47 opcodes are handled by formally-derived code from coq/Extraction.v.
    """
    strict = _strict_backend_required()

    # Try OCaml extracted runner first (fastest)
    if _runner_available():
        try:
            return _run_extracted(instructions, fuel)
        except (FileNotFoundError, PermissionError, OSError):
            if strict:
                raise RuntimeError(
                    "strict backend policy: OCaml extracted runner failed"
                )

    if strict and not _runner_available():
        raise RuntimeError(
            "strict backend policy: OCaml extracted runner not available at "
            f"{_RUNNER_PATH}"
        )

    # Use THE definitive Coq-extracted Python VM
    try:
        return _run_python(instructions, fuel)
    except Exception as e:
        raise RuntimeError(
            f"Coq-extracted Python VM failed: {e}\n"
            "This is THE definitive VM; no legacy fallback exists."
        ) from e


def run_vm(instructions: List[str], fuel: int = 1000) -> VMState:
    """Alias for run_vm_trace."""
    return run_vm_trace(instructions, fuel)
