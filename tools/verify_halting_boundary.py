#!/usr/bin/env python3
"""Run the halting baseline vs VM agreement checks."""

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


def run_halting_checks(
    *,
    stress_max_steps: int,
    stress_output: Path,
    survey_max_length: int,
    survey_sample_size: int,
    survey_max_steps: int,
    survey_output: Path,
) -> None:
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

    run_halting_checks(
        stress_max_steps=args.stress_max_steps,
        stress_output=args.stress_output,
        survey_max_length=args.survey_max_length,
        survey_sample_size=args.survey_sample_size,
        survey_max_steps=args.survey_max_steps,
        survey_output=args.survey_output,
    )

    print(
        "Halting stress tests and survey completed without VM/baseline disagreements."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
