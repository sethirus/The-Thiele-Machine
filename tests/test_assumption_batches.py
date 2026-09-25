"""Protect the full receipt against omitted queries and hidden Coq errors."""
from pathlib import Path
import importlib.util
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("assumption_batches", ROOT / "scripts/run_assumption_batches.py")
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def test_probe_header_and_comments_do_not_become_queries():
    source = "(** Comprehensive Print Assumptions probe. *)\nRequire Arith.\nPrint Assumptions Nat.add_0_r.\n(* section *)\nPrint Assumptions Nat.add_0_l.\n"
    prefix, queries = MODULE.split_probe(source)
    assert prefix.endswith("Require Arith.\n")
    assert queries == ["Print Assumptions Nat.add_0_r.", "Print Assumptions Nat.add_0_l."]


def test_unexpected_command_cannot_silently_disappear():
    with pytest.raises(ValueError):
        MODULE.split_probe("Print Assumptions Nat.add_0_r.\nRequire MissingLibrary.\n")


def test_missing_result_rejects_the_batch():
    with pytest.raises(ValueError):
        MODULE.validate_output("Closed under the global context\n", "", 2)


@pytest.mark.parametrize("error", ["Error: Cannot find a physical path", "Anomaly: failure", "  Fatal error: stopped"])
def test_coq_error_rejects_even_a_complete_result_count(error):
    with pytest.raises(ValueError):
        MODULE.validate_output("Closed under the global context\n", error, 1)


def test_real_coq_output_checks_both_closed_and_axiomatic_results():
    result = subprocess.run(["coqtop", "-quiet"], input="Require Import Arith Classical_Prop.\nPrint Assumptions Nat.add_0_r.\nPrint Assumptions classic.\nQuit.\n", text=True, capture_output=True, check=True)
    output = MODULE.validate_output(result.stdout, result.stderr, 2)
    assert output.startswith("Closed under the global context\n")
    assert "Axioms:" in output and "classic" in output


def _save_batch(directory: Path, source: str, output: str) -> None:
    (directory / "1-1.v").write_text(source)
    (directory / "1-1.output.txt").write_text(output)
    (directory / "1-1.errors.txt").write_text("")


def test_saved_batch_is_reused_only_for_the_same_queries(tmp_path):
    source = "Require Arith.\nPrint Assumptions Nat.add_0_r.\nQuit.\n"
    _save_batch(tmp_path, source, "Closed under the global context\n")
    assert MODULE.load_saved_batch(tmp_path, 0, 1, source) == (0, "Closed under the global context\n", "")
    changed = "Require Arith.\nPrint Assumptions Nat.add_0_l.\nQuit.\n"
    assert MODULE.load_saved_batch(tmp_path, 0, 1, changed) is None


def test_saved_batch_without_its_source_is_not_reused(tmp_path):
    source = "Require Arith.\nPrint Assumptions Nat.add_0_r.\nQuit.\n"
    _save_batch(tmp_path, source, "Closed under the global context\n")
    (tmp_path / "1-1.v").unlink()
    assert MODULE.load_saved_batch(tmp_path, 0, 1, source) is None
