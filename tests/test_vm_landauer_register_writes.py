# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

from pathlib import Path
from tempfile import TemporaryDirectory

from thielecpu.assemble import parse
from thielecpu.state import State
from thielecpu.vm import VM


def _run_register_program() -> tuple[int, int]:
    program_text = """
XOR_SWAP 0 1
XOR_SWAP 1 2
XFER 3 0
HALT
"""
    with TemporaryDirectory() as tmpdir:
        outdir = Path(tmpdir)
        thm_path = outdir / "register_ops.thm"
        thm_path.write_text(program_text, encoding="utf-8")
        program = parse(thm_path.read_text(encoding="utf-8").splitlines(), outdir)
        vm = VM(State())
        vm.register_file[0] = 3
        vm.register_file[1] = 1
        vm.register_file[2] = 2
        vm.run(program, outdir)
        return vm.state.mu_ledger.total, vm.state.mu_ledger.landauer_entropy


def test_register_writes_charge_entropy_only():
    mu_total, entropy = _run_register_program()
    assert mu_total == 0
    assert entropy > 0
