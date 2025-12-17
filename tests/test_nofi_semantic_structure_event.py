"""Regression: No-Free-Insight semantic structure-addition is detectable in execution.

This test is intentionally CHSH-free.

We validate the *semantic* notion of “structure addition” in the runtime VM:
starting from a clean certification CSR, any run that ends with a non-empty
certificate string must have performed some step that changed CERT_ADDR from
empty -> non-empty.

This is the Python analogue of:
- coq/kernel/RevelationRequirement.v :: structure_addition_in_run
- coq/kernel/RevelationRequirement.v :: supra_cert_implies_structure_addition_in_run

It is not a policy test; it is an execution-trace test.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest


@pytest.mark.parametrize(
    "program",
    [
        # Minimal certificate-setting via REVEAL.
        [("PNEW", "{1}"), ("REVEAL", "1 64 cert_payload"), ("EMIT", "done")],
        # Certificate-setting via LASSERT (sat path should set a cert addr).
        # Use existing CNF fixtures from tests/ if present.
    ],
)
def test_semantic_structure_addition_detectable_from_trace(tmp_path: Path, program) -> None:
    from thielecpu.state import State, CSR
    from thielecpu.vm import VM

    outdir = tmp_path / "nofi_semantic"
    vm = VM(State())

    # Record cert addr before/after each step via VM receipts.
    vm.run(program, outdir)

    summary = json.loads((outdir / "summary.json").read_text(encoding="utf-8"))
    final_cert = str(summary.get("cert", ""))

    step_receipts = json.loads((outdir / "step_receipts.json").read_text(encoding="utf-8"))

    # If final cert is empty, this test case is ill-posed.
    assert final_cert, "program should end with a non-empty cert"

    # Our semantic event: some executed step makes cert_addr transition from empty -> non-empty.
    transitioned = False
    for entry in step_receipts:
        pre_cert = str(entry.get("pre_state", {}).get("cert_addr", ""))
        post_cert = str(entry.get("post_state", {}).get("cert_addr", ""))
        if (not pre_cert) and post_cert:
            transitioned = True
            break

    assert transitioned, "expected a cert transition during execution"

    # Also sanity-check VM's live state agrees with summary.
    assert str(vm.state.csr.get(CSR.CERT_ADDR, "")) == final_cert
