"""Paradox suite + positive co-sim parity checks on Kami RTL (Verilator)."""

from __future__ import annotations

from pathlib import Path
import tempfile

import pytest

from thielecpu.hardware.cosim import run_verilog
from thielecpu.state import State
from thielecpu.vm import VM

ERR_LOCALITY = 0x0BADC0DE
ERR_LOGIC = 0xC43471A1
ERR_BIANCHI = 0x0B1A4C81
ERR_CHSH = 0x0BADC45C


def _run_vm(program: list[tuple[str, str]], init_mem: dict[int, int]) -> dict:
    state = State()
    vm = VM(state)
    for addr, value in init_mem.items():
        vm.data_memory[addr] = value & 0xFFFFFFFF

    with tempfile.TemporaryDirectory() as td:
        vm.run(program, Path(td), write_artifacts=False, auto_mdlacc=False)

    return {
        "regs": [int(v) & 0xFFFFFFFF for v in vm.register_file],
        "mem": [int(v) & 0xFFFFFFFF for v in vm.data_memory],
        "mu": int(vm.state.mu_ledger.total) & 0xFFFFFFFF,
    }


@pytest.mark.hardware
def test_positive_parity_vm_equals_rtl_for_compute_subset() -> None:
    # Baseline positive parity: both models execute HALT and preserve reset state.
    rtl_program = "HALT 0\n"

    rtl = run_verilog(rtl_program, backend="verilator")
    if rtl is None:
        pytest.skip("verilator unavailable")

    vm = _run_vm([("HALT", "")], {})

    assert rtl["regs"] == vm["regs"]
    assert rtl["mem"] == vm["mem"]
    assert int(rtl["mu"]) == vm["mu"]


@pytest.mark.hardware
def test_paradox_thief_locality_store_out_of_partition_rejected() -> None:
    result = run_verilog(
        "\n".join(
            [
                "INIT_ACTIVE_MODULE 0",
                "INIT_PT 0 10",
                "LOAD_IMM 0 77 1",
                "STORE 250 0 1",
                "HALT 0",
                "",
            ]
        ),
        backend="verilator",
    )
    if result is None:
        pytest.skip("verilator unavailable")

    assert result.get("error_code", 0) == ERR_LOCALITY
    assert result.get("err", 0) == 1
    assert result.get("status", 0) in (2, 3)
    assert result.get("mem", [0] * 256)[250] == 0


@pytest.mark.hardware
def test_paradox_liar_lassert_bridge_completes_without_hang() -> None:
    result = run_verilog(
        "\n".join(
            [
                "LASSERT 0 1 0",
                "HALT 0",
                "",
            ]
        ),
        backend="verilator",
        logic_z3_bridge=True,
    )
    if result is None:
        pytest.skip("verilator unavailable")

    assert result.get("status", 0) == 2
    assert result.get("cycles", 10000) < 10000


@pytest.mark.hardware
def test_paradox_perpetual_motion_bianchi_alarm() -> None:
    result = run_verilog(
        "\n".join(
            [
                "INIT_MU 0",
                "INIT_TENSOR 0 100",
                "REVEAL 0 0 1",
                "HALT 0",
                "",
            ]
        ),
        backend="verilator",
    )
    if result is None:
        pytest.skip("verilator unavailable")

    assert result.get("error_code", 0) == ERR_BIANCHI
    assert result.get("bianchi_alarm", 0) == 1


@pytest.mark.hardware
def test_paradox_cheater_chsh_x1_without_certificate_rejected() -> None:
    result = run_verilog(
        "\n".join(
            [
                "CHSH_TRIAL 1 0 0 0 7",
                "HALT 0",
                "",
            ]
        ),
        backend="verilator",
    )
    if result is None:
        pytest.skip("verilator unavailable")

    assert result.get("error_code", 0) == ERR_CHSH
    assert result.get("status", 0) == 3
