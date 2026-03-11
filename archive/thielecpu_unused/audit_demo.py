from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
from typing import Any, Dict, List, Tuple

from thielecpu.receipts import verify_signature
from thielecpu.state import State
from thielecpu.vm import VM


@dataclass(frozen=True)
class AuditRunResult:
    outdir: Path
    mu_ledger: List[Dict[str, Any]]
    summary: Dict[str, Any]
    receipts: List[Dict[str, Any]]


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _run_program(program: List[Tuple[str, str]], outdir: Path) -> AuditRunResult:
    vm = VM(State())
    vm.run(program, outdir)

    mu_ledger = _read_json(outdir / "mu_ledger.json")
    summary = _read_json(outdir / "summary.json")
    receipts = _read_json(outdir / "step_receipts.json")
    return AuditRunResult(outdir=outdir, mu_ledger=mu_ledger, summary=summary, receipts=receipts)


def run_mu_audit_demo(out_base: Path) -> Dict[str, Any]:
    """Run two VM workloads that compute the same answer but differ in explicit revelation.

    Workload A uses REVEAL (explicit information-flow / provenance).
    Workload B does not.

    Returns a dict suitable for JSON serialization.
    """

    out_a = out_base / "a_reveal"
    out_b = out_base / "b_plain"

    answer_code = "print('ANSWER=42')\n__result__ = 42\n"

    # Keep the computation identical. Only difference is whether we explicitly REVEAL.
    program_a: List[Tuple[str, str]] = [
        ("PNEW", "{1,2,3}"),
        ("REVEAL", "1 12 demo_cert:structure_assumption"),
        ("PYEXEC", answer_code),
        ("HALT", ""),
    ]
    program_b: List[Tuple[str, str]] = [
        ("PNEW", "{1,2,3}"),
        ("PYEXEC", answer_code),
        ("HALT", ""),
    ]

    res_a = _run_program(program_a, out_a)
    res_b = _run_program(program_b, out_b)

    def _total_info(summary: Dict[str, Any]) -> float:
        return float(summary.get("mu_information", 0.0))

    def _total_mu(summary: Dict[str, Any]) -> float:
        return float(summary.get("mu_total_legacy", 0.0))

    # Quick cryptographic sanity: verify at least one receipt signature.
    receipt_ok = False
    if res_a.receipts:
        first = res_a.receipts[0]
        payload = {
            "step": first["step"],
            "instruction": first["instruction"],
            "pre_state": first["pre_state"],
            "post_state": first["post_state"],
            "observation": first["observation"],
            "pre_state_hash": first["pre_state_hash"],
            "post_state_hash": first["post_state_hash"],
        }
        receipt_ok = bool(verify_signature(payload, first["signature"]))

    report = {
        "a_reveal": {
            "outdir": str(res_a.outdir),
            "summary": res_a.summary,
            "mu_ledger_len": len(res_a.mu_ledger),
            "receipts_len": len(res_a.receipts),
        },
        "b_plain": {
            "outdir": str(res_b.outdir),
            "summary": res_b.summary,
            "mu_ledger_len": len(res_b.mu_ledger),
            "receipts_len": len(res_b.receipts),
        },
        "diff": {
            "mu_information_delta": _total_info(res_a.summary) - _total_info(res_b.summary),
            "mu_total_legacy_delta": _total_mu(res_a.summary) - _total_mu(res_b.summary),
            "receipt_signature_verified": receipt_ok,
        },
    }

    return report
