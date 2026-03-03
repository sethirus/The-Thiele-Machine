"""Hardware CHSH bridge checks using Verilator backend.

These checks pin down the new quantum-verification path in RTL:
- CHSH_TRIAL is a high-value op requiring logic_acc == 0xCAFEEACE.
- x=1 CHSH settings are rejected unless a REVEAL certificate exists (tensor_total > 0).
- x=1 CHSH settings incur an additional mu surcharge when allowed.
"""

from __future__ import annotations

import pytest

from thielecpu.hardware.cosim import run_verilog


@pytest.mark.hardware
def test_chsh_without_logic_gate_key_is_rejected() -> None:
    """CHSH_TRIAL without logic_acc gate key triggers ERR_LOGIC_VAL."""
    result = run_verilog(
        "\n".join(
            [
                "CHSH_TRIAL 0 0 0 0 7",
                "HALT 0",
                "",
            ]
        ),
        backend="verilator",
    )
    if result is None:
        pytest.skip("verilator unavailable")

    assert result.get("error_code", 0) == 0xC43471A1
    assert result.get("err", 0) == 1


@pytest.mark.hardware
def test_chsh_x1_without_reveal_certificate_is_rejected() -> None:
    """x=1 CHSH trial with logic gate key but no tensor evidence is rejected."""
    result = run_verilog(
        "\n".join(
            [
                "INIT_LOGIC_ACC 0xCAFEEACE",
                "CHSH_TRIAL 1 0 0 0 7",
                "HALT 0",
                "",
            ]
        ),
        backend="verilator",
    )
    if result is None:
        pytest.skip("verilator unavailable")

    assert result.get("error_code", 0) == 0x0BADC45C
    assert result.get("err", 0) == 1


@pytest.mark.hardware
def test_chsh_x0_with_logic_gate_key_succeeds() -> None:
    """x=0 CHSH trial with logic gate key succeeds."""
    result = run_verilog(
        "\n".join(
            [
                "INIT_LOGIC_ACC 0xCAFEEACE",
                "CHSH_TRIAL 0 0 0 0 7",
                "HALT 0",
                "",
            ]
        ),
        backend="verilator",
    )
    if result is None:
        pytest.skip("verilator unavailable")

    assert result.get("error_code", 0) == 0
    assert result.get("err", 0) == 0
    assert result.get("mu", -1) == 7


@pytest.mark.hardware
def test_chsh_x1_with_reveal_certificate_is_allowed_and_surcharged() -> None:
    result = run_verilog(
        "\n".join(
            [
                # Logic gate key and certificate via REVEAL.
                # Note: INIT_MU is intentionally absent — it corrupts the CPU's
                # init pipeline (executing instructions during the force cycle),
                # causing REVEAL's mu charge to be applied before Phase 4 starts.
                # Starting from mu=0 gives a clean, deterministic total.
                "INIT_LOGIC_ACC 0xCAFEEACE",
                "REVEAL 0 0 1",
                "CHSH_TRIAL 1 0 0 0 7",
                "HALT 0",
                "",
            ]
        ),
        backend="verilator",
    )
    if result is None:
        pytest.skip("verilator unavailable")

    assert result.get("error_code", 0) == 0
    assert result.get("status", 0) == 2
    # mu = REVEAL cost (1) + CHSH base cost (7) + x=1 surcharge (256) = 264.
    assert result.get("mu", -1) == 264
