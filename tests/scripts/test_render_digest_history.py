from datetime import datetime, timezone
import json
from pathlib import Path

from scripts.render_digest_history import render_digest_history


def test_render_digest_history_empty(tmp_path: Path) -> None:
    history_path = tmp_path / "history.json"
    output_path = tmp_path / "docs" / "digest_history.md"

    result_path = render_digest_history(history_path, output_path, generated_at=datetime(2025, 1, 1, tzinfo=timezone.utc))

    content = result_path.read_text(encoding="utf-8")
    assert "No manifest digests recorded yet" in content
    assert "Generated from" in content


def test_render_digest_history_with_records(tmp_path: Path) -> None:
    history_path = tmp_path / "history.json"
    history_path.write_text(
        json.dumps(
            [
                {
                    "run_tag": "ci-20250101",
                    "manifest_digest_sha256": "deadbeef",
                    "updated": "2025-01-01T00:00:00Z",
                },
                {
                    "run_tag": "ci-20250102",
                    "manifest_digest_sha256": "deadbeef",
                    "updated": "2025-01-02T00:00:00Z",
                },
            ]
        ),
        encoding="utf-8",
    )
    output_path = tmp_path / "docs" / "digest_history.md"

    render_digest_history(history_path, output_path, limit=1, generated_at=datetime(2025, 1, 3, tzinfo=timezone.utc))

    lines = output_path.read_text(encoding="utf-8").splitlines()
    assert "| Run tag | manifest_digest_sha256 | Updated |" in lines
    assert any("ci-20250102" in line for line in lines)
    assert "runs=2" in " ".join(lines)
    assert lines[-1].endswith("last_updated=2025-01-02T00:00:00Z.")
