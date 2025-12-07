import subprocess
import sys
from pathlib import Path

from tools import generate_admit_report


def test_report_matches_checked_in_file() -> None:
    report = generate_admit_report.render_report(
        generate_admit_report.generate_findings(generate_admit_report.REPO_ROOT)
    )

    reference = (generate_admit_report.REPO_ROOT / "coq" / "ADMIT_REPORT.txt").read_text(
        encoding="utf-8"
    )

    assert report == reference


def test_cli_writes_requested_output(tmp_path: Path) -> None:
    output_path = tmp_path / "report.txt"

    result = subprocess.run(
        [sys.executable, "-m", "tools.generate_admit_report", "--output", str(output_path)],
        check=True,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0
    assert output_path.read_text(encoding="utf-8") == (
        generate_admit_report.REPO_ROOT / "coq" / "ADMIT_REPORT.txt"
    ).read_text(encoding="utf-8")

