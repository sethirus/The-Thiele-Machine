from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parent
CURRENT_FILE = Path(__file__).name

FORBIDDEN_PATTERNS = [
    ("script-style prints", "print("),
    ("main-block harness", 'if __name__ == "__main__":'),
    ("pytest.main harness", "pytest.main("),
    ("success-banner text", "ALL TESTS PASSED"),
    ("simulator skip-on-none", 'pytest.skip("sim unavailable")'),
    ("simulator skip-on-none", 'pytest.skip("Verilog simulation returned None")'),
    ("simulator skip-on-none", 'pytest.skip("run_verilog returned None'),
    # The copy-over-and-warn idiom: a freshness test that, on mismatch,
    # overwrites the committed artifact with the freshly generated one and
    # emits a warning instead of asserting. Such a test cannot fail, so it
    # cannot distinguish "the committed artifact is correct" from "the
    # committed artifact is corrupt" -- it silently repairs the very drift it
    # exists to detect. Two tests did this (test_rtl_text_transform_audit.py
    # and test_master_summary_artifacts.py) and both now assert instead.
    # Banned here so the idiom cannot come back.
    ("self-repairing freshness gate", "shutil.copy2("),
    ("warn-instead-of-assert gate", "warnings.warn("),
]


def test_active_tests_do_not_contain_shortcut_harness_patterns() -> None:
    offenders: list[str] = []

    for path in sorted(ROOT.glob("test_*.py")):
        if path.name == CURRENT_FILE:
            continue
        text = path.read_text(encoding="utf-8")
        for label, needle in FORBIDDEN_PATTERNS:
            if needle in text:
                offenders.append(f"{path.name}: contains {label} -> {needle}")

    assert not offenders, "\n".join(offenders)