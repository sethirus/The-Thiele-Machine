"""Protect the full receipt against omitted queries, hidden Coq errors, and stale answers."""
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


def test_missing_result_rejects_the_group():
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


# --- grouping by owning library -------------------------------------------

def test_queries_group_by_owning_library_in_probe_order():
    prefix = "(* generated *)\nRequire Kernel.One.\nRequire Kernel.OneMore.\nRequire Other.\n"
    queries = ["Print Assumptions Kernel.One.a.", "Print Assumptions Kernel.One.Nested.b.",
               "Print Assumptions Kernel.OneMore.c.", "Print Assumptions Other.d."]
    assert MODULE.group_queries(prefix, queries) == [
        ("Kernel.One", queries[:2]), ("Kernel.OneMore", [queries[2]]), ("Other", [queries[3]])]


def test_unowned_query_gets_no_library():
    groups = MODULE.group_queries("Require Kernel.One.\n", ["Print Assumptions Unmapped.x."])
    assert groups == [(None, ["Print Assumptions Unmapped.x."])]


def test_unrecognized_import_context_owns_nothing():
    prefix = "Require Kernel.One.\nSet Printing All.\n"
    assert MODULE.group_queries(prefix, ["Print Assumptions Kernel.One.x."]) == [
        (None, ["Print Assumptions Kernel.One.x."])]


# --- resolving the compiled library ----------------------------------------

def _touch(path: Path) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(b"compiled")
    return path


def test_library_resolves_through_load_path_and_root(tmp_path):
    lib = _touch(tmp_path / "kernel/foundation/Step.vo")
    root = _touch(tmp_path / "Top.vo")
    pairs = MODULE.load_path(["-R", "kernel/foundation", "Kernel", "-R", "kernel/nfi", "Kernel"])
    assert MODULE.resolve_library("Kernel.Step", tmp_path, pairs) == lib.resolve()
    assert MODULE.resolve_library("Top", tmp_path, pairs) == root.resolve()


def test_ambiguous_or_missing_library_is_not_resolved(tmp_path):
    _touch(tmp_path / "kernel/foundation/Step.vo")
    _touch(tmp_path / "kernel/nfi/Step.vo")
    pairs = MODULE.load_path(["-R", "kernel/foundation", "Kernel", "-R", "kernel/nfi", "Kernel"])
    assert MODULE.resolve_library("Kernel.Step", tmp_path, pairs) is None
    assert MODULE.resolve_library("Kernel.Missing", tmp_path, pairs) is None


# --- the answer cache -------------------------------------------------------

QUERIES = ["Print Assumptions Kernel.One.a."]
CLOSED = "Closed under the global context\n"


def test_cache_key_changes_with_every_input():
    base = MODULE.cache_key("Kernel.One", "lib-a", QUERIES, "coq-1", ["-R", "k", "Kernel"])
    assert base != MODULE.cache_key("Kernel.One", "lib-b", QUERIES, "coq-1", ["-R", "k", "Kernel"])
    assert base != MODULE.cache_key("Kernel.One", "lib-a", QUERIES + QUERIES, "coq-1", ["-R", "k", "Kernel"])
    assert base != MODULE.cache_key("Kernel.One", "lib-a", QUERIES, "coq-2", ["-R", "k", "Kernel"])
    assert base != MODULE.cache_key("Kernel.One", "lib-a", QUERIES, "coq-1", ["-Q", "k", "Kernel"])
    assert base != MODULE.cache_key("Kernel.Two", "lib-a", QUERIES, "coq-1", ["-R", "k", "Kernel"])


def test_saved_answer_is_reused_only_for_its_key_module_and_queries(tmp_path):
    MODULE.save_cached(tmp_path, "k1", "Kernel.One", QUERIES, CLOSED, "")
    assert MODULE.load_cached(tmp_path, "k1", "Kernel.One", QUERIES) == (CLOSED, "")
    assert MODULE.load_cached(tmp_path, "k2", "Kernel.One", QUERIES) is None
    assert MODULE.load_cached(tmp_path, "k1", "Kernel.Two", QUERIES) is None
    assert MODULE.load_cached(tmp_path, "k1", "Kernel.One", ["Print Assumptions Kernel.One.b."]) is None


@pytest.mark.parametrize("field,value", [("stdout", "Axioms:\nforged : False\nAxioms:\n"),
                                         ("stderr", "Error: stale"), ("key", "other")])
def test_modified_saved_answer_is_not_reused(tmp_path, field, value):
    import json
    MODULE.save_cached(tmp_path, "k1", "Kernel.One", QUERIES, CLOSED, "")
    path = tmp_path / "k1.json"
    record = json.loads(path.read_text())
    record[field] = value
    path.write_text(json.dumps(record))
    assert MODULE.load_cached(tmp_path, "k1", "Kernel.One", QUERIES) is None


def test_incomplete_write_is_not_reused(tmp_path):
    MODULE.save_cached(tmp_path, "k1", "Kernel.One", QUERIES, CLOSED, "")
    (tmp_path / "k1.json").rename(tmp_path / "k1.pending")
    assert MODULE.load_cached(tmp_path, "k1", "Kernel.One", QUERIES) is None


def test_prune_keeps_only_the_answers_in_use(tmp_path):
    MODULE.save_cached(tmp_path, "k1", "Kernel.One", QUERIES, CLOSED, "")
    MODULE.save_cached(tmp_path, "k2", "Kernel.One", QUERIES, CLOSED, "")
    (tmp_path / "k3.pending").write_text("{}")
    MODULE.prune_cache(tmp_path, {"k1"})
    assert sorted(p.name for p in tmp_path.iterdir()) == ["k1.json"]
    assert MODULE.load_cached(tmp_path, "k1", "Kernel.One", QUERIES) == (CLOSED, "")


def test_failed_answer_cannot_be_saved(tmp_path):
    with pytest.raises(ValueError):
        MODULE.save_cached(tmp_path, "k1", "Kernel.One", QUERIES, "", "Error: failed")
    assert not (tmp_path / "k1.json").exists()


# --- the facts the cache relies on, checked on real Coq ---------------------

def _coqc(directory: Path, name: str) -> Path:
    subprocess.run(["coqc", "-R", ".", "T", f"{name}.v"], cwd=directory, check=True,
                   capture_output=True, text=True)
    return directory / f"{name}.vo"


def test_compiled_library_changes_when_a_dependency_changes(tmp_path):
    (tmp_path / "A.v").write_text("Definition base := 1.\n")
    (tmp_path / "B.v").write_text("Require T.A.\nLemma uses : True. Proof. exact I. Qed.\n")
    _coqc(tmp_path, "A")
    first = MODULE.file_sha256(_coqc(tmp_path, "B"))
    (tmp_path / "A.v").write_text("Definition base := 2.\n")
    _coqc(tmp_path, "A")
    assert MODULE.file_sha256(_coqc(tmp_path, "B")) != first


def test_answer_with_only_its_library_loaded_matches_the_full_prefix():
    prefix = "Require Coq.Arith.PeanoNat.\nRequire Coq.Logic.Classical_Prop.\n"
    query = "Print Assumptions Coq.Logic.Classical_Prop.NNPP."
    (module, _), = MODULE.group_queries(prefix, [query])
    answers = []
    for imports in (prefix, f"Require {module}.\n"):
        result = subprocess.run(["coqtop", "-quiet"], input=imports + query + "\nQuit.\n",
                                text=True, capture_output=True, check=True)
        answers.append(MODULE.validate_output(result.stdout, result.stderr, 1))
    assert answers[0] == answers[1]


def test_shared_session_output_is_cut_back_by_library():
    output = "Closed under the global context\nAxioms:\nclassic : forall P, P \\/ ~ P\nClosed under the global context\n"
    pieces = MODULE.split_answers(output, [1, 2])
    assert pieces == ["Closed under the global context\n",
                      "Axioms:\nclassic : forall P, P \\/ ~ P\nClosed under the global context\n"]
    with pytest.raises(ValueError):
        MODULE.split_answers(output, [1, 1])
