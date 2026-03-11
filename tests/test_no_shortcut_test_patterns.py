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