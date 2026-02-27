from __future__ import annotations

import tempfile
from pathlib import Path

from thielecpu.state import State
from thielecpu.vm import CHSH_X1_SURCHARGE, VM
from thielecpu.isa import CSR


def _run_vm(instrs: list[tuple[str, str]]) -> VM:
    vm = VM(state=State())
    with tempfile.TemporaryDirectory() as td:
        vm.run(instrs, Path(td) / "out", auto_mdlacc=False, write_artifacts=False)
    return vm


def test_vm_chsh_x1_requires_reveal_tensor_certificate() -> None:
    vm = _run_vm([
        ("CHSH_TRIAL", "1 0 0 0 7"),
        ("HALT", "0"),
    ])
    assert vm.state.csr.get(CSR.ERR, 0) == 1


def test_vm_chsh_x1_applies_surcharge_and_allows_with_reveal() -> None:
    vm = _run_vm([
        ("REVEAL", "0 0 1"),
        ("CHSH_TRIAL", "1 0 0 0 7"),
        ("HALT", "0"),
    ])
    assert vm.state.csr.get(CSR.ERR, 0) == 0
    assert vm.state.mu_ledger.total == (1 + 7 + CHSH_X1_SURCHARGE)
