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
    MODULE.publish_completed_batch(directory, 0, 1, source, output, "")


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


@pytest.mark.parametrize("new_source,new_objects", [("source-b", "objects-a"), ("source-a", "objects-b")])
def test_same_queries_cannot_reuse_answers_from_different_proofs(tmp_path, new_source, new_objects):
    query = "Require Arith.\nPrint Assumptions Nat.add_0_r.\nQuit.\n"
    old = MODULE.bind_corpus(query, "source-a", "objects-a")
    _save_batch(tmp_path, old, "Closed under the global context\n")
    assert MODULE.load_saved_batch(tmp_path, 0, 1, old) is not None
    changed = MODULE.bind_corpus(query, new_source, new_objects)
    assert MODULE.load_saved_batch(tmp_path, 0, 1, changed) is None


def test_compiled_fingerprint_tracks_proof_objects(tmp_path):
    coq = tmp_path / "coq"
    coq.mkdir()
    (coq / "_CoqProject").write_text("Proof.v\n")
    (coq / "Proof.v").write_text("Lemma proof : True. Proof. exact I. Qed.\n")
    obj = coq / "Proof.vo"
    obj.write_bytes(b"first compiled proof")
    first = MODULE.compiled_digest(tmp_path)
    obj.write_bytes(b"different compiled proof")
    assert MODULE.compiled_digest(tmp_path) != first


def test_interrupted_replacement_cannot_relabel_old_answers(tmp_path):
    old = MODULE.bind_corpus("Print Assumptions old.\n", "old-source", "old-objects")
    new = MODULE.bind_corpus("Print Assumptions new.\n", "new-source", "new-objects")
    _save_batch(tmp_path, old, "Closed under the global context\n")
    # The runner writes the new source before invoking Coq. An interruption
    # leaves the previous answers on disk beside this different source.
    (tmp_path / "1-1.v").write_text(new)
    assert MODULE.load_saved_batch(tmp_path, 0, 1, new) is None


def test_legacy_batch_without_completion_record_is_not_reused(tmp_path):
    source = "Print Assumptions Nat.add_0_r.\n"
    (tmp_path / "1-1.v").write_text(source)
    (tmp_path / "1-1.output.txt").write_text("Closed under the global context\n")
    (tmp_path / "1-1.errors.txt").write_text("")
    assert MODULE.load_saved_batch(tmp_path, 0, 1, source) is None


@pytest.mark.parametrize("suffix,value", [
    ("output.txt", "Axioms:\nforged : False\n"),
    ("errors.txt", "different diagnostics\n"),
    ("complete.json", "not JSON"),
])
def test_modified_batch_payload_is_not_reused(tmp_path, suffix, value):
    source = "Print Assumptions Nat.add_0_r.\n"
    _save_batch(tmp_path, source, "Closed under the global context\n")
    (tmp_path / f"1-1.{suffix}").write_text(value)
    assert MODULE.load_saved_batch(tmp_path, 0, 1, source) is None


def test_failed_batch_cannot_publish_completion(tmp_path):
    with pytest.raises(ValueError):
        MODULE.publish_completed_batch(tmp_path, 0, 1, "source", "", "Error: failed")
    assert not (tmp_path / "1-1.complete.json").exists()


def test_batch_imports_follow_qualified_library_boundaries():
    prefix = "(* generated *)\nRequire Kernel.One.\nRequire Kernel.OneMore.\nRequire Other.\n"
    queries = ["Print Assumptions Kernel.One.Nested.result."]
    assert MODULE.batch_prefix(prefix, queries) == "Require Kernel.One.\n"


@pytest.mark.parametrize("prefix,query", [
    ("Require Kernel.One.\n", "Print Assumptions Unmapped.result."),
    ("Require Kernel.One.\nSet Printing All.\n", "Print Assumptions Kernel.One.result."),
])
def test_unrecognized_import_context_keeps_the_full_prefix(prefix, query):
    assert MODULE.batch_prefix(prefix, [query]) == prefix


def test_selective_imports_preserve_real_assumption_results():
    prefix = "Require Coq.Arith.PeanoNat.\nRequire Coq.Logic.Classical_Prop.\n"
    query = "Print Assumptions Coq.Arith.PeanoNat.Nat.add_0_r."
    reduced = MODULE.batch_prefix(prefix, [query])
    assert "Classical_Prop" not in reduced
    answers = []
    for imports in (prefix, reduced):
        result = subprocess.run(["coqtop", "-quiet"], input=imports + query + "\nQuit.\n",
                                text=True, capture_output=True, check=True)
        answers.append(MODULE.validate_output(result.stdout, result.stderr, 1))
    assert answers[0] == answers[1]
