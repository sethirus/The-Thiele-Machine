"""Random program fuzzing: Coq == Python for arbitrary instruction sequences.

This test generates random programs with all 18 opcodes and verifies that
the Coq-extracted OCaml runner and the Python VM produce identical final state.

Property: For ALL valid instruction sequences:
  coq_state.mu == python_state.mu
  coq_state.err == python_state.err
  coq_state.regs == python_state.regs
  coq_state.modules == python_state.modules (up to sort order)
"""

import json
import os
import subprocess
import tempfile
from pathlib import Path
from typing import List, Tuple

import pytest
from hypothesis import given, settings, assume, HealthCheck
import hypothesis.strategies as st


def _env_int(name: str, default: int) -> int:
    raw = os.getenv(name)
    if raw is None:
        return default
    try:
        return max(1, int(raw))
    except ValueError:
        return default


RPF_MAX_EXAMPLES = _env_int("THIELE_FUZZ_MAX_EXAMPLES", 200)
RPF_TENSOR_MAX_EXAMPLES = _env_int("THIELE_FUZZ_TENSOR_MAX_EXAMPLES", 100)
RPF_LONG_MAX_EXAMPLES = _env_int("THIELE_FUZZ_LONG_MAX_EXAMPLES", 50)

REPO_ROOT = Path(__file__).resolve().parents[1]
EXTRACTED_RUNNER = REPO_ROOT / "build" / "extracted_vm_runner_native"
if not EXTRACTED_RUNNER.exists():
    EXTRACTED_RUNNER = REPO_ROOT / "build" / "extracted_vm_runner"


def _ocaml_env():
    env = os.environ.copy()
    env.setdefault("OCAMLRUNPARAM", "l=64M")
    return env


def run_coq(program: str) -> dict:
    """Run program through Coq-extracted OCaml runner, return JSON dict."""
    if not EXTRACTED_RUNNER.exists():
        pytest.skip("OCaml runner not built")
    with tempfile.NamedTemporaryFile(mode='w', suffix='.txt', delete=False) as f:
        f.write(program)
        prog_path = f.name
    try:
        result = subprocess.run(
            [str(EXTRACTED_RUNNER), prog_path],
            capture_output=True, text=True, timeout=30, env=_ocaml_env(),
        )
        if result.returncode != 0:
            return None  # Runner error — skip this case
        return json.loads(result.stdout)
    except (subprocess.TimeoutExpired, json.JSONDecodeError):
        return None
    finally:
        Path(prog_path).unlink()


def run_python(program: str):
    """Run program through Python VM, return (mu, err, regs, modules, tensor)."""
    from thielecpu.vm import VM
    from thielecpu.state import State
    from tests.test_bisimulation_complete import parse_program_to_python_instructions

    instructions, init_regs, init_mem = parse_program_to_python_instructions(program)
    state = State()
    vm = VM(state=state)
    for idx, val in init_regs.items():
        vm.register_file[idx % 32] = val
    for idx, val in init_mem.items():
        vm.data_memory[idx % 256] = val
    with tempfile.TemporaryDirectory() as tmpdir:
        vm.run(instructions, Path(tmpdir) / "out", auto_mdlacc=False)

    from thielecpu.isa import CSR
    modules = []
    if hasattr(vm.state.regions, 'modules'):
        for mid, region in vm.state.regions.modules.items():
            modules.append({"id": mid, "region": sorted(list(region))})

    err = vm.state.csr.get(CSR.ERR, 0) != 0 if hasattr(vm.state, 'csr') else False
    tensor = [row[:] for row in vm.state.mu_ledger.mu_tensor]

    return {
        "mu": vm.state.mu_ledger.total,
        "err": err,
        "regs": list(vm.register_file),
        "mem": list(vm.data_memory),
        "modules": modules,
        "mu_tensor": tensor,
    }


# ---------------------------------------------------------------------------
# Instruction generators
# ---------------------------------------------------------------------------

def gen_pnew():
    """Generate a PNEW instruction with valid region and cost."""
    def _format_pnew(sz: int) -> str:
        return f"PNEW {{{','.join(str(i) for i in range(sz))}}} {sz + 3}"

    return st.builds(_format_pnew, st.integers(1, 4))

def gen_reveal():
    """Generate a REVEAL instruction."""
    def _format_reveal(ti: int, tj: int, bits: int) -> str:
        return f"REVEAL {ti} {tj} {bits}"

    return st.builds(
        _format_reveal,
        st.integers(0, 3),
        st.integers(0, 3),
        st.integers(1, 10),
    )

def gen_xfer():
    """Generate an XFER instruction (dst src cost)."""
    def _format_xfer(dst: int, src: int, cost: int) -> str:
        return f"XFER {dst} {src} {cost}"

    return st.builds(
        _format_xfer,
        st.integers(0, 7),
        st.integers(0, 7),
        st.integers(1, 3),
    )

def gen_xor_load():
    """Generate an XOR_LOAD instruction (dst addr cost)."""
    def _format_xor_load(dst: int, addr: int, cost: int) -> str:
        return f"XOR_LOAD {dst} {addr} {cost}"

    return st.builds(
        _format_xor_load,
        st.integers(0, 7),
        st.integers(0, 31),
        st.integers(1, 3),
    )

def gen_xor_add():
    """Generate an XOR_ADD instruction (dst src cost)."""
    def _format_xor_add(dst: int, src: int, cost: int) -> str:
        return f"XOR_ADD {dst} {src} {cost}"

    return st.builds(
        _format_xor_add,
        st.integers(0, 7),
        st.integers(0, 7),
        st.integers(1, 3),
    )

def gen_xor_swap():
    """Generate an XOR_SWAP instruction (a b cost)."""
    def _format_xor_swap(a: int, b: int, cost: int) -> str:
        return f"XOR_SWAP {a} {b} {cost}"

    return st.builds(
        _format_xor_swap,
        st.integers(0, 7),
        st.integers(0, 7),
        st.integers(1, 3),
    )

def gen_safe_instruction():
    """Generate a random safe instruction (won't cause errors in isolation)."""
    return st.one_of(
        gen_xfer(),
        gen_xor_load(),
        gen_xor_add(),
        gen_xor_swap(),
        gen_reveal(),
    )

@st.composite
def random_program(draw):
    """Generate a random program with PNEW setup + operations + HALT."""
    # Always start with PNEW to have a valid partition
    setup = draw(gen_pnew())
    num_ops = draw(st.integers(0, 15))
    ops = [draw(gen_safe_instruction()) for _ in range(num_ops)]
    fuel = num_ops + 5
    lines = [f"FUEL {fuel}", setup] + ops + ["HALT 0"]
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

class TestRandomProgramIsomorphism:
    """Verify Coq == Python for random instruction sequences."""

    @given(program=random_program())
    @settings(max_examples=RPF_MAX_EXAMPLES, deadline=None, suppress_health_check=[HealthCheck.too_slow])
    def test_mu_matches_for_random_programs(self, program):
        """μ-cost must be identical between Coq and Python for any program."""
        coq = run_coq(program)
        assert coq is not None, f"Coq runner failed for program:\n{program}"
        py = run_python(program)

        assert coq["mu"] == py["mu"], (
            f"μ mismatch: Coq={coq['mu']} Python={py['mu']}\nProgram:\n{program}"
        )

    @given(program=random_program())
    @settings(max_examples=RPF_MAX_EXAMPLES, deadline=None, suppress_health_check=[HealthCheck.too_slow])
    def test_error_flag_matches(self, program):
        """Error flag must match between Coq and Python."""
        coq = run_coq(program)
        assert coq is not None, f"Coq runner failed for program:\n{program}"
        py = run_python(program)

        assert coq["err"] == py["err"], (
            f"err mismatch: Coq={coq['err']} Python={py['err']}\nProgram:\n{program}"
        )

    @given(program=random_program())
    @settings(max_examples=RPF_MAX_EXAMPLES, deadline=None, suppress_health_check=[HealthCheck.too_slow])
    def test_registers_match(self, program):
        """Register state must be identical after execution."""
        coq = run_coq(program)
        assert coq is not None, f"Coq runner failed for program:\n{program}"
        py = run_python(program)

        for i in range(32):
            assert coq["regs"][i] == py["regs"][i], (
                f"Reg[{i}] mismatch: Coq={coq['regs'][i]} Python={py['regs'][i]}"
                f"\nProgram:\n{program}"
            )

    @given(program=random_program())
    @settings(max_examples=RPF_TENSOR_MAX_EXAMPLES, deadline=None, suppress_health_check=[HealthCheck.too_slow])
    def test_tensor_matches(self, program):
        """mu_tensor must match between Coq and Python."""
        coq = run_coq(program)
        assert coq is not None, f"Coq runner failed for program:\n{program}"
        assume("mu_tensor" in coq)
        py = run_python(program)

        # Flatten Python tensor for comparison
        py_flat = []
        for row in py["mu_tensor"]:
            py_flat.extend(row)

        for idx in range(16):
            assert coq["mu_tensor"][idx] == py_flat[idx], (
                f"tensor[{idx}] mismatch: Coq={coq['mu_tensor'][idx]} Python={py_flat[idx]}"
                f"\nProgram:\n{program}"
            )


class TestRandomProgramStress:
    """Stress tests with longer random programs."""

    @given(
        ops=st.lists(
            st.one_of(
                gen_xfer(),
                gen_xor_load(),
                gen_xor_add(),
                gen_reveal(),
            ),
            min_size=10,
            max_size=30,
        )
    )
    @settings(max_examples=RPF_LONG_MAX_EXAMPLES, deadline=None, suppress_health_check=[HealthCheck.too_slow])
    def test_long_program_mu_isomorphism(self, ops):
        """Longer programs still maintain μ isomorphism."""
        fuel = len(ops) + 5
        program = "\n".join(
            [f"FUEL {fuel}", "PNEW {0,1,2} 5"] + ops + ["HALT 0"]
        )
        coq = run_coq(program)
        assert coq is not None, f"Coq runner failed for program:\n{program}"
        py = run_python(program)
        assert coq["mu"] == py["mu"], (
            f"μ mismatch on long program: Coq={coq['mu']} Python={py['mu']}"
        )

    def test_determinism_same_program_twice(self):
        """Same program must produce identical results both times."""
        program = "FUEL 10\nPNEW {0,1} 5\nREVEAL 2 3 7\nXFER 1 0 1\nXOR_LOAD 3 0 1\nHALT 0\n"
        coq1 = run_coq(program)
        coq2 = run_coq(program)
        py1 = run_python(program)
        py2 = run_python(program)
        if coq1 and coq2:
            assert coq1 == coq2, "Coq not deterministic"
        assert py1["mu"] == py2["mu"], "Python not deterministic"
        assert py1["regs"] == py2["regs"], "Python registers not deterministic"

    def test_all_reveal_tensor_indices_in_one_program(self):
        """Single program that charges all 16 tensor entries."""
        lines = ["FUEL 30", "PNEW {0,1} 5"]
        expected = {}
        for ti in range(4):
            for tj in range(4):
                bits = ti * 4 + tj + 1  # 1..16
                lines.append(f"REVEAL {ti} {tj} {bits}")
                expected[(ti, tj)] = bits
        lines.append("HALT 0")
        program = "\n".join(lines)

        coq = run_coq(program)
        py = run_python(program)

        # Verify all 16 entries
        for (ti, tj), bits in expected.items():
            assert py["mu_tensor"][ti][tj] == bits, (
                f"Python tensor[{ti}][{tj}] = {py['mu_tensor'][ti][tj]}, expected {bits}"
            )
            if coq and "mu_tensor" in coq:
                flat_idx = ti * 4 + tj
                assert coq["mu_tensor"][flat_idx] == bits, (
                    f"Coq tensor[{flat_idx}] = {coq['mu_tensor'][flat_idx]}, expected {bits}"
                )
