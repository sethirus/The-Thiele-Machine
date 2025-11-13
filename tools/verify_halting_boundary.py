#!/usr/bin/env python3
"""Run and report on the halting baseline-versus-VM agreement checks.

This verifier expects two JSON artefacts produced by
``tools.halting_stress_test`` and ``tools.halting_survey`` respectively:

``artifacts/halting/results.json``
    Records curated toy programs (``halt_immediately`` through
    ``diagonal_like``), the baseline interpreter's verdict, the Thiele VM
    verdict, and whether the two agree.

``artifacts/halting/survey_summary.json``
    Summarises the bounded random survey, including the number of sampled
    programs, maximum program length, step budget, and any disagreements.

The script regenerates both artefacts using the library helpers, emits a
human-readable summary, and exits with status 1 if *any* disagreement is
detected.  A zero exit status certifies that, within the configured bounds,
the VM never contradicts the baseline interpreter and no anomalies were
encountered.
"""

from __future__ import annotations

import argparse
from pathlib import Path

try:  # Support invocation via ``python tools/verify_halting_boundary.py``
    from tools.halting_stress_test import run_analysis as run_stress_analysis
    from tools.halting_survey import run_survey
except ModuleNotFoundError:  # pragma: no cover - runtime convenience
    import sys

    REPO_ROOT = Path(__file__).resolve().parent.parent
    sys.path.insert(0, str(REPO_ROOT))
    from tools.halting_stress_test import run_analysis as run_stress_analysis
    from tools.halting_survey import run_survey


DEFAULT_STRESS_OUTPUT = Path("artifacts/halting/results.json")
DEFAULT_SURVEY_OUTPUT = Path("artifacts/halting/survey_summary.json")


def _format_stress_table(stress_report: dict) -> str:
    """Return a compact text table summarising curated program results."""

    header = "program               baseline   vm        agreement"
    rows = [header, "-" * len(header)]
    for entry in stress_report.get("programs", []):
        program = entry.get("program", "<unknown>")
        baseline = entry.get("baseline", {}).get("status", "?")
        vm_status = entry.get("vm", {}).get("status", "?")
        agreement = "yes" if entry.get("agreement") else "NO"
        rows.append(f"{program:<20} {baseline:<9} {vm_status:<9} {agreement}")
    return "\n".join(rows)


def run_halting_checks(
    *,
    stress_max_steps: int,
    stress_output: Path,
    survey_max_length: int,
    survey_sample_size: int,
    survey_max_steps: int,
    survey_output: Path,
) -> tuple[dict, dict]:
    """Execute the stress test and enumerative survey, raising on disagreement."""

    stress_report = run_stress_analysis(stress_max_steps, stress_output)
    disagreements = [
        item for item in stress_report["programs"] if not item.get("agreement", False)
    ]
    if disagreements:
        raise RuntimeError(
            "Halting stress test uncovered disagreements: "
            + ", ".join(entry["program"] for entry in disagreements)
        )

    survey_summary = run_survey(
        survey_max_length, survey_sample_size, survey_max_steps, survey_output
    )
    anomalies = survey_summary.get("anomalies", [])
    if anomalies:
        raise RuntimeError(
            "Halting survey detected {} disagreements".format(len(anomalies))
        )

    return stress_report, survey_summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--stress-max-steps",
        type=int,
        default=32,
        help="Step budget for the curated stress tests.",
    )
    parser.add_argument(
        "--stress-output",
        type=Path,
        default=DEFAULT_STRESS_OUTPUT,
        help="Where to write the curated stress-test JSON summary.",
    )
    parser.add_argument(
        "--survey-max-length",
        type=int,
        default=3,
        help="Maximum program length for the enumerative survey.",
    )
    parser.add_argument(
        "--survey-sample-size",
        type=int,
        default=40,
        help="Number of random programs to sample in the survey.",
    )
    parser.add_argument(
        "--survey-max-steps",
        type=int,
        default=64,
        help="Interpreter step budget for the survey runs.",
    )
    parser.add_argument(
        "--survey-output",
        type=Path,
        default=DEFAULT_SURVEY_OUTPUT,
        help="Where to write the survey JSON summary.",
    )
    args = parser.parse_args()

    try:
        stress_report, survey_summary = run_halting_checks(
            stress_max_steps=args.stress_max_steps,
            stress_output=args.stress_output,
            survey_max_length=args.survey_max_length,
            survey_sample_size=args.survey_sample_size,
            survey_max_steps=args.survey_max_steps,
            survey_output=args.survey_output,
        )
    except Exception as exc:  # pragma: no cover - CLI reporting convenience
        print(f"Halting boundary verification FAILED: {exc}")
        return 1

    print("Halting boundary verification passed.")
    print(_format_stress_table(stress_report))
    print(
        "Survey: {checked} programs sampled (length ≤ {max_length}, steps ≤ {max_steps}); anomalies = {anomalies}".format(
            checked=survey_summary.get("checked", "?"),
            max_length=survey_summary.get("max_length", "?"),
            max_steps=survey_summary.get("max_steps", "?"),
            anomalies=len(survey_summary.get("anomalies", [])),
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
