# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import sys, os
sys.path.append(os.path.dirname(os.path.dirname(__file__)))
import hashlib
import json
import os
import tempfile

import pytest

from scripts.thiele_verify import verify_dir
from examples.xor_tseitin import run_demo as xor_demo


def test_no_free_sight():
    info = xor_demo(save=False)
    assert info['mu_refined'] >= info['mu_blind']


def test_paradox_inf():
    with tempfile.TemporaryDirectory() as d:
        cert = '0=1'
        data = {
            'steps': [
                {
                    'step_id': 0,
                    'partition_id': 0,
                    'axiom_ids': [],
                    'certificate': cert,
                    'certificate_hash': hashlib.sha256(cert.encode()).hexdigest(),
                    'mu_delta': 'INF',
                }
            ],
            'mu_total': 'INF',
        }
        with open(os.path.join(d, 'p.json'), 'w') as f:
            json.dump(data, f)
        with pytest.raises(ValueError):
            verify_dir(d)
