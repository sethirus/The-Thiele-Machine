"""The search that tries to break Part II finds nothing, and its controls find something.

scripts/break_it.py searches small machines for a counterexample to each
central result of Part II, and runs the same search with each premise
dropped. Here the quick search runs: every result must come back with no
counterexample, and every control must find one, or the search could not
have caught a failure.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def load():
    spec = importlib.util.spec_from_file_location("break_it", ROOT / "scripts" / "break_it.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules["break_it"] = module
    spec.loader.exec_module(module)
    return module


def test_no_counterexample_and_every_control_fires() -> None:
    results = load().run_all(quick=True)
    failures = [f"{r.label}: {r.counterexample}" for r in results if r.counterexample]
    silent = [f"{r.label}: {c.premise}" for r in results for c in r.controls if not c.found]
    assert not failures, "counterexamples:\n" + "\n".join(failures)
    assert not silent, "controls that found nothing:\n" + "\n".join(silent)


def test_every_searched_label_is_in_the_book() -> None:
    text = (ROOT / "monograph" / "monograph.tex").read_text(encoding="utf-8")
    missing = [r.label for r in load().run_all(quick=True) if f"\\label{{{r.label}}}" not in text]
    assert not missing, missing

