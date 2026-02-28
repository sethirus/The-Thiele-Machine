"""Hardware CHSH bridge checks using Verilator backend.

These checks pin down the new quantum-verification path in RTL:
- x=1 CHSH settings are rejected unless a REVEAL certificate exists.
- x=1 CHSH settings incur an additional μ surcharge when allowed.
"""

from __future__ import annotations

import pytest

from thielecpu.hardware.cosim import run_verilog


@pytest.mark.hardware
def test_chsh_x1_without_reveal_certificate_is_rejected() -> None:
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

    assert result.get("error_code", 0) == 0x0BADC45C
    assert result.get("status", 0) == 3


@pytest.mark.hardware
def test_chsh_x1_with_reveal_certificate_is_allowed_and_surcharged() -> None:
    result = run_verilog(
        "\n".join(
            [
                # Seed non-zero mu_tensor certificate.
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
    # μ includes REVEAL cost (1) + CHSH base cost (7) + x=1 surcharge (256).
    assert result.get("mu", -1) == 264
