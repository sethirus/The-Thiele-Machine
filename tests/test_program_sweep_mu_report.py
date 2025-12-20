from __future__ import annotations

from pathlib import Path

from thielecpu.program_sweep import default_workloads, run_sweep


def test_program_sweep_smoke(tmp_path: Path) -> None:
    report = run_sweep(default_workloads(factoring_n=15), base_outdir=tmp_path, quiet=True)

    index = report["index"]

    emit = index["emit_bits"]
    assert "emit_info_gain" in emit["reasons"]
    assert emit["summary"]["mu_information"] >= 8

    reveal = index["reveal_cert"]
    assert any(r.startswith("reveal_module") for r in reveal["reasons"].keys())
    assert reveal["summary"]["mu_information"] >= 8

    factoring = index["pyexec_factoring"]
    assert any(r.startswith("factoring_revelation_") for r in factoring["reasons"].keys())
    # Factoring revelation should charge legacy μ-information (and canonical μ-execution via info_charge).
    assert factoring["summary"]["mu_information"] > 0
