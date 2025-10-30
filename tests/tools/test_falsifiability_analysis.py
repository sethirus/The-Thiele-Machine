"""Exercise the falsifiability analysis helpers against archived proofpacks."""

from __future__ import annotations

from pathlib import Path

from tools.falsifiability_analysis import (
    SUMMARY_END_MARKER,
    SUMMARY_START_MARKER,
    analyze_cross_domain,
    analyze_landauer,
    analyze_turbulence,
    render_markdown_summary,
    update_readme_summary,
)


ROOT = Path("artifacts/experiments")


def test_landauer_margins_respect_epsilon() -> None:
    stats = analyze_landauer(ROOT, epsilon=0.05)
    # The public proofpacks should contain multiple deterministic trials.
    assert stats.trial_count > 0
    # No trial should exceed the slack.
    assert stats.worst_violation <= 1e-9


def test_turbulence_blind_slower_than_sighted() -> None:
    stats = analyze_turbulence(ROOT)
    assert stats is not None
    # Blind runs must take longer on average than sighted ones.
    assert stats.ratio("blind", "sighted") > 1.0
    # Each module should also show a slowdown.
    for module_ratio in stats.module_ratios("blind", "sighted").values():
        assert module_ratio > 1.0


def test_cross_domain_ratio_reports() -> None:
    stats = analyze_cross_domain(ROOT)
    assert stats is not None
    # The helper should return a finite ratio even if the dataset is shallow.
    assert stats.final_runtime_ratio > 0.0


def test_markdown_summary_contains_key_metrics() -> None:
    landauer_stats = analyze_landauer(ROOT, epsilon=0.05)
    turbulence_stats = analyze_turbulence(ROOT)
    cross_domain_stats = analyze_cross_domain(ROOT)
    summary = render_markdown_summary(landauer_stats, turbulence_stats, cross_domain_stats)
    assert "Landauer" in summary
    assert "2.489" in summary  # expected blind/sighted runtime ratio snapshot
    assert "0.000" in summary  # zero slack should remain zeroed


def test_update_readme_summary_replaces_block(tmp_path: Path) -> None:
    readme = tmp_path / "README.md"
    original = (
        "prefix\n"
        f"{SUMMARY_START_MARKER}\nold\n{SUMMARY_END_MARKER}\n"
        "suffix\n"
    )
    readme.write_text(original, encoding="utf-8")
    update_readme_summary(readme, "new-line")
    updated = readme.read_text(encoding="utf-8")
    assert "old" not in updated
    assert "new-line" in updated
