from __future__ import annotations

import tempfile
from pathlib import Path

from thielecpu.isa import CSR
from thielecpu.state import State
from thielecpu.vm import BIANCHI_VIOLATION_ERROR_CODE, VM


def test_vm_bianchi_violation_halts_with_bianchi_error_code_and_no_err_bit() -> None:
    vm = VM(state=State())
    # Corrupt pre-state to force tensor_total > mu when REVEAL checks consistency.
    vm.state.mu_ledger.mu_tensor[0][0] = 10

    with tempfile.TemporaryDirectory() as td:
        vm.run(
            [("REVEAL", "0 0 1"), ("HALT", "0")],
            Path(td) / "out",
            auto_mdlacc=False,
            write_artifacts=False,
        )

    assert vm.halted is True
    assert vm.error_code == BIANCHI_VIOLATION_ERROR_CODE
    # Mirror RTL: Bianchi kill-switch does not drive protocol ERR.
    assert vm.state.csr.get(CSR.ERR, 0) == 0
