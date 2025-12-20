from __future__ import annotations

import json
import logging
from pathlib import Path

from thielecpu.audit_demo import run_mu_audit_demo


_PHASES = [
    "INIT",
    "DISCOVER",
    "CLASSIFY",
    "DECOMPOSE",
    "EXECUTE",
    "MERGE",
    "VERIFY",
    "SUCCESS",
]


def _phase(name: str) -> None:
    print(f"[{name}]".ljust(12), end="")
    print("█" * 24)


def main() -> None:
    # Keep the demo output clean by suppressing INFO logs from the structured logger.
    logging.getLogger("thielecpu").setLevel(logging.WARNING)

    out_base = Path("out") / "audit_mu_vs_logging"

    for phase in _PHASES[:-1]:
        _phase(phase)

    report = run_mu_audit_demo(out_base)

    _phase("SUCCESS")
    print()
    print("Result: both runs compute ANSWER=42")
    print(f"A outdir: {report['a_reveal']['outdir']}")
    print(f"B outdir: {report['b_plain']['outdir']}")
    print()
    print("Audit signal:")
    print(f"- Δ mu_information = {report['diff']['mu_information_delta']}")
    print(f"- Δ mu_total_legacy = {report['diff']['mu_total_legacy_delta']}")
    print(f"- Receipt signature verified = {report['diff']['receipt_signature_verified']}")

    (out_base / "report.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"\nWrote {out_base / 'report.json'}")


if __name__ == "__main__":
    main()
