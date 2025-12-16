from __future__ import annotations

from fractions import Fraction
from pathlib import Path

from thielecpu.isa import CSR

from thielecpu.state import State
from thielecpu.vm import VM

from tools.bell_receipts import load_probability_table_csv, program_from_trials, trials_from_probability_table
from tools.chsh_receipts import chsh_from_receipts_path, decode_trials_from_receipts


def test_receipt_chsh_bridge_supra_16_5(tmp_path: Path) -> None:
    prob_csv = Path(__file__).parents[1] / "artifacts" / "bell" / "supra_quantum_16_5.csv"
    outdir = tmp_path / "receipt_chsh_supra"
    outdir.mkdir(parents=True, exist_ok=True)

    table = load_probability_table_csv(prob_csv)
    trials_expected = trials_from_probability_table(table)
    program = program_from_trials(trials_expected)
    program.insert(1, ("REVEAL", "1 64 supra_16_5"))

    vm = VM(State())
    vm.run(program, outdir)

    assert int(vm.state.csr.get(CSR.ERR, 0)) == 0
    assert float(vm.state.mu_information) >= 64.0

    receipts_path = outdir / "step_receipts.json"
    assert receipts_path.exists(), "VM did not write step_receipts.json"

    trials_observed = decode_trials_from_receipts(receipts_path)
    assert len(trials_observed) == len(trials_expected)

    s_value = chsh_from_receipts_path(receipts_path)
    assert s_value == Fraction(16, 5)


def test_pyexec_cannot_forge_chsh_trial_receipt(tmp_path: Path) -> None:
    outdir = tmp_path / "receipt_chsh_nonforgeable"
    outdir.mkdir(parents=True, exist_ok=True)

    program = [
        ("PNEW", "{1,2}"),
        # Attempt to forge a trial via PYEXEC; should not be counted.
        ("PYEXEC", "print('CHSH_0000')"),
        ("EMIT", "done"),
    ]

    vm = VM(State())
    vm.run(program, outdir)

    receipts_path = outdir / "step_receipts.json"
    assert decode_trials_from_receipts(receipts_path) == []
