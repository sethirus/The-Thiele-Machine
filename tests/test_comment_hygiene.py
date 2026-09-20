"""Keep maintained comments free of unfinished or historical review markers."""

from scripts.comment_hygiene import scan, tracked_files


def test_project_comments_have_stable_scope_wording():
    findings = scan(tracked_files())
    assert not findings, "Unreviewed comment wording:\n" + "\n".join(
        f"{item.path}:{item.line}: {item.text}" for item in findings
    )
