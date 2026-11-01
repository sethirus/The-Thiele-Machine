"""Release fingerprint updates leave the surrounding authorial text alone."""
import hashlib
import json

import pytest

from scripts.sync_release_receipt import synchronize


def test_updates_both_fingerprints_only(tmp_path):
    receipt = tmp_path / 'receipt.json'
    receipt.write_text(json.dumps({'corpus_digest': 'a' * 64}))
    record = tmp_path / 'record.txt'
    before = 'Author text.\nSHA-256 ' + '0' * 32 + '\n          ' + '0' * 32
    before += '\ncorpus digest ' + '0' * 32 + '\n                ' + '0' * 32 + '\nEnd.\n'
    record.write_text(before)
    synchronize(record, receipt)
    sha = hashlib.sha256(receipt.read_bytes()).hexdigest()
    assert record.read_text() == before.replace(
        'SHA-256 ' + '0' * 32 + '\n          ' + '0' * 32,
        'SHA-256 ' + sha[:32] + '\n          ' + sha[32:],
    ).replace('0' * 32, 'a' * 32)


def test_missing_field_leaves_record_untouched(tmp_path):
    receipt = tmp_path / 'receipt.json'
    receipt.write_text(json.dumps({'corpus_digest': 'a' * 64}))
    record = tmp_path / 'record.txt'
    record.write_text('No receipt fields.\n')
    with pytest.raises(ValueError):
        synchronize(record, receipt)
    assert record.read_text() == 'No receipt fields.\n'
