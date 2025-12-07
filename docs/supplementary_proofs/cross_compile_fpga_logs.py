"""Cross-compile FPGA synthesis logs into a structured parity report."""
from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Dict

REPO_ROOT = Path(__file__).resolve().parents[1]
LOG_PATH = REPO_ROOT / "audit_logs" / "agent_hardware_verification.log"
TESTBENCH_PATH = REPO_ROOT / "hardware" / "synthesis_trap" / "thiele_graph_solver_tb.v"
OUTPUT_PATH = REPO_ROOT / "supplementary_proofs" / "hardware_software_parity.json"

LOG_PATTERN = re.compile(
    r"^(Sequential|Autonomous) solver μ_question=(?P<question>\d+), "
    r"μ_info=(?P<info>\d+) \(Q16\), μ_total=(?P<total>\d+) \(Q16\)$"
)

TESTBENCH_PATTERNS = {
    "mu_question_bits": re.compile(r"Expected question-bit total of (?P<value>\d+)", re.UNICODE),
    "mu_information_q16": re.compile(r"Expected information gain of (?P<value>\d+) \(Q16\)", re.UNICODE),
    "mu_total_q16": re.compile(r"Expected μ-total of (?P<value>\d+) \(Q16\)", re.UNICODE),
}


def parse_hardware_log(path: Path) -> Dict[str, Dict[str, int]]:
    """Extract sequential/autonomous µ-totals from the hardware verification log."""
    results: Dict[str, Dict[str, int]] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        match = LOG_PATTERN.search(line.strip())
        if match:
            key = match.group(1).lower()
            results[key] = {
                "mu_question_bits": int(match.group("question")),
                "mu_information_q16": int(match.group("info")),
                "mu_total_q16": int(match.group("total")),
            }
    if not results:
        raise RuntimeError(f"No FPGA parity results found in {path}.")
    if set(results) != {"sequential", "autonomous"}:
        raise RuntimeError(
            "Expected both sequential and autonomous solver totals; "
            f"found {sorted(results)}."
        )
    return results


def parse_expected_totals(path: Path) -> Dict[str, int]:
    """Extract the canonical totals embedded in the HDL test bench."""
    source = path.read_text(encoding="utf-8")
    expected: Dict[str, int] = {}
    for key, pattern in TESTBENCH_PATTERNS.items():
        match = pattern.search(source)
        if not match:
            raise RuntimeError(f"Failed to locate expected value for {key} in {path}.")
        expected[key] = int(match.group("value"))
    return expected


def build_parity_report() -> Dict[str, object]:
    hardware = parse_hardware_log(LOG_PATH)
    expected = parse_expected_totals(TESTBENCH_PATH)

    parity = {
        variant: {field: (values[field] == expected[field]) for field in expected}
        for variant, values in hardware.items()
    }

    return {
        "hardware_totals": hardware,
        "expected_totals": expected,
        "parity_checks": parity,
    }


def main() -> None:
    report = build_parity_report()
    OUTPUT_PATH.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {OUTPUT_PATH.relative_to(REPO_ROOT)}")


if __name__ == "__main__":
    main()
