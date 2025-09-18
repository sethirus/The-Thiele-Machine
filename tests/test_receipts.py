import sys, os
sys.path.append(os.path.dirname(os.path.dirname(__file__)))
import json
import hashlib
import os
import tempfile

from scripts.thiele_verify import verify_dir


def test_valid_receipt():
    with tempfile.TemporaryDirectory() as d:
        cert = 'ok'
        data = {
            'steps': [
                {
                    'step_id': 0,
                    'partition_id': 0,
                    'axiom_ids': [],
                    'certificate': cert,
                    'certificate_hash': hashlib.sha256(cert.encode()).hexdigest(),
                    'step_hash': hashlib.sha256(cert.encode()).hexdigest(),
                    'mu_delta': 1,
                }
            ],
            'mu_total': 1,
        }
        path = os.path.join(d, 'r.json')
        with open(path, 'w') as f:
            json.dump(data, f)
        total = verify_dir(d)
        assert total == 1


def test_corrupt_receipt():
    with tempfile.TemporaryDirectory() as d:
        cert = 'ok'
        data = {
            'steps': [
                {
                    'step_id': 0,
                    'partition_id': 0,
                    'axiom_ids': [],
                    'certificate': cert,
                    'certificate_hash': 'deadbeef',
                    'mu_delta': 1,
                }
            ],
            'mu_total': 1,
        }
        with open(os.path.join(d, 'r.json'), 'w') as f:
            json.dump(data, f)
        try:
            verify_dir(d)
            assert False, 'expected failure'
        except ValueError:
            pass
