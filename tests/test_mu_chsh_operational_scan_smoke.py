from __future__ import annotations

from fractions import Fraction
from pathlib import Path

import pytest

from tools.mu_chsh_operational_scan import run_one


@pytest.mark.parametrize(
    "strategy,expected",
    [
        ("lhv", Fraction(2, 1)),
        ("tsirelson", None),
        ("supra_16_5", Fraction(16, 5)),
        ("pr", Fraction(4, 1)),
    ],
)
def test_operational_scan_strategies(tmp_path: Path, strategy: str, expected: Fraction | None) -> None:
    outdir = tmp_path / strategy
    sample = run_one(
        strategy=strategy,
        n_per_setting=200,
        seed=123,
        oracle_charge_bits=0,
        outdir=outdir,
    )

    # Baselines: exact for deterministic/probability-table strategies; Tsirelson is sampled.
    if expected is not None:
        assert sample.chsh == expected
    else:
        assert abs(float(sample.chsh) - (2.0 * (2.0**0.5))) < 0.2

    # Receipt-driven semantic enforcement: supra/pr without REVEAL sets ERR.
    if strategy in {"supra_16_5", "pr"}:
        assert sample.err == 1
    else:
        assert sample.err == 0

    # Sanity: ledger always accounts for instruction execution.
    assert sample.mu_execution >= 1


def test_oracle_charge_affects_information_mu(tmp_path: Path) -> None:
    outdir_free = tmp_path / "pr_free"
    outdir_oracle = tmp_path / "pr_oracle"

    free = run_one(
        strategy="pr",
        n_per_setting=50,
        seed=321,
        oracle_charge_bits=0,
        outdir=outdir_free,
    )
    charged = run_one(
        strategy="pr",
        n_per_setting=50,
        seed=321,
        oracle_charge_bits=64,
        outdir=outdir_oracle,
    )

    assert free.chsh == Fraction(4, 1)
    assert charged.chsh == Fraction(4, 1)
    assert free.err == 1
    assert charged.err == 0
    assert charged.mu_information >= free.mu_information + 64.0


def test_default_policy_charges_nonlocal_strategies(tmp_path: Path) -> None:
    lhv = run_one(
        strategy="lhv",
        n_per_setting=50,
        seed=1,
        oracle_charge_bits=None,
        outdir=tmp_path / "lhv",
    )
    supra = run_one(
        strategy="supra_16_5",
        n_per_setting=50,
        seed=1,
        oracle_charge_bits=None,
        outdir=tmp_path / "supra",
    )
    pr = run_one(
        strategy="pr",
        n_per_setting=50,
        seed=1,
        oracle_charge_bits=None,
        outdir=tmp_path / "pr",
    )

    assert lhv.mu_information == 0.0
    assert supra.mu_information >= 64.0
    assert pr.mu_information >= 64.0

    assert lhv.err == 0
    assert supra.err == 0
    assert pr.err == 0
