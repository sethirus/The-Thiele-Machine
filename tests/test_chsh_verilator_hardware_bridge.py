"""Hardware CHSH bridge checks using Verilator backend.

These checks pin down the quantum-verification path in RTL:
- CHSH_TRIAL charges its declared cost and does NOT require a logic key.
- The x=1 surcharge and the zero-tensor gate were removed.

The logic-gate lock (logic_acc == 0xCAFEEACE), the x=1 +256 surcharge and the
zero-tensor fault were deliberately removed from the CPU so it matches
`kami_step` (Devon, 2026-09-14; see artifacts/review_revision/
C2_DIVERGENCE_LEDGER.md "Logic-gate lock -> Removed from the CPU" and
"CHSH_TRIAL x=1 -> Surcharge and gate removed"). The old expectations asserted
the removed behaviour; these tests now assert the aligned contract.
"""

from __future__ import annotations

import pytest

pytestmark = pytest.mark.strict_rtl

from thielecpu.hardware.cosim import run_verilog


@pytest.mark.hardware
def test_chsh_without_logic_gate_key_is_accepted() -> None:
    """CHSH_TRIAL no longer requires a logic-gate key."""
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

    assert result.get("error_code", 0) == 0
    assert result.get("err", 0) == 0
    assert result.get("mu", -1) == 7


@pytest.mark.hardware
def test_chsh_x1_without_reveal_certificate_is_accepted() -> None:
    """x=1 CHSH trial no longer needs tensor evidence, and takes no surcharge."""
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

    assert result.get("error_code", 0) == 0
    assert result.get("err", 0) == 0
    assert result.get("mu", -1) == 7


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
def test_chsh_x1_with_reveal_certificate_charges_declared_cost() -> None:
    """A preceding REVEAL and an x=1 CHSH trial charge only their declared costs.

    REVEAL 0 1 0 charges bits + cost + 1 = 2 (VMStep.v:290); CHSH_TRIAL 1 ... 7
    charges its declared 7 with no x=1 surcharge.
    """
    result = run_verilog(
        "\n".join(
            [
                "REVEAL 0 1 0",
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
    # mu = REVEAL (1 bit + S(0) = 2) + CHSH declared cost (7) = 9. No surcharge.
    assert result.get("mu", -1) == 9
