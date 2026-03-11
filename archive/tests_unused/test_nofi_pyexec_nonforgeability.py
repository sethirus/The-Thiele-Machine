"""CHSH-free NoFI regression: PYEXEC cannot forge certification evidence.

In the Coq kernel semantics, `instr_pyexec` does not set the certification CSR.
The Python VM must match that: untrusted PYEXEC code should not be able to set
`CSR.CERT_ADDR` directly.

This test enforces *non-forgeability* at the evidence channel level.
"""

from __future__ import annotations

import json
from pathlib import Path


def test_pyexec_cannot_forge_cert_addr(tmp_path: Path) -> None:
    from thielecpu.state import State
    from thielecpu.vm import VM

    outdir = tmp_path / "nofi_pyexec_nonforge"
    vm = VM(State())

    # Attempt to forge CERT_ADDR by referencing `self`.
    # This must fail because `self` is intentionally not injected into the PYEXEC scope.
    program = [
        ("PNEW", "{1}"),
        ("PYEXEC", "self.state.csr['CERT_ADDR'] = 'forged'"),
        ("EMIT", "done"),
    ]

    vm.run(program, outdir)

    summary = json.loads((outdir / "summary.json").read_text(encoding="utf-8"))
    assert str(summary.get("cert", "")) == "", "PYEXEC must not be able to forge cert evidence"
