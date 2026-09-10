"""Receipt comparison tolerates run metadata but detects changed proof evidence."""
import importlib.util
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('receipt_check', ROOT / 'scripts/check_assumption_receipt.py')
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

PROBE = 'Require Arith.\nPrint Assumptions first.\nPrint Assumptions second.\n'
OUTPUT = 'Closed under the global context\nAxioms:\nClassical_Prop.classic : forall P : Prop, P \\/ ~ P\n'
META = {'alignment_ok': True, 'unexpected_lines_in_output': 0, 'generated': 'first run',
        'raw_output_sha256': 'one', 'stderr_excerpt': 'Coq <', 'summary': {'theorems_probed': 2}}


def compare(output=OUTPUT, probe=PROBE, meta=None):
    MODULE.compare_receipts(PROBE, OUTPUT, META, probe, output, META if meta is None else meta)


def test_run_metadata_and_loading_messages_do_not_change_proof_results():
    fresh = {**META, 'generated': 'another run', 'raw_output_sha256': 'two', 'stderr_excerpt': 'Coq < Coq <'}
    compare(output=OUTPUT.replace('Axioms:', 'Fetching opaque proofs from disk for Coq.Init.Logic\nAxioms:'), meta=fresh)


@pytest.mark.parametrize('old,new', [('classic', 'another_axiom'), ('P \\/ ~ P', 'P /\\ ~ P')])
def test_axiom_name_or_type_change_is_detected(old, new):
    with pytest.raises(ValueError, match='Theorem/axiom'):
        compare(output=OUTPUT.replace(old, new))


def test_axiom_becoming_closed_is_detected():
    with pytest.raises(ValueError, match='Theorem/axiom'):
        compare(output='Closed under the global context\nClosed under the global context\n')


def test_renamed_query_is_detected():
    with pytest.raises(ValueError, match='Theorem/axiom'):
        compare(probe=PROBE.replace('second', 'third'))


def test_missing_result_is_detected():
    with pytest.raises(ValueError, match='queries but'):
        compare(output='Closed under the global context\n')


def test_summary_changes_are_detected():
    with pytest.raises(ValueError, match='metadata differs'):
        compare(meta={**META, 'summary': {'theorems_probed': 3}})


def test_unexpected_output_cannot_be_ignored():
    with pytest.raises(ValueError):
        compare(output=OUTPUT+'Error: failed proof load\n')


def test_reported_misalignment_is_rejected():
    with pytest.raises(ValueError, match='misalignment'):
        compare(meta={**META, 'alignment_ok': False})
