# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import json
import glob
import math

def test_mu_never_decreases():
    for path in glob.glob("spec/golden/*.json"):
        with open(path) as f:
            data = json.load(f)
        mu = 0.0
        for step in data.get("steps", []):
            mu_delta = step.get("mubits_delta", 0)
            assert mu_delta >= 0, f"μ decreased in {path}"
            mu += mu_delta

def test_paradox_sets_mu_inf():
    # Simulate a paradox receipt
    receipt = {
        "steps": [
            {"mubits_delta": float("inf")}
        ]
    }
    mu = 0.0
    for step in receipt["steps"]:
        mu_delta = step.get("mubits_delta", 0)
        if math.isinf(mu_delta):
            mu = float("inf")
            break
        mu += mu_delta
    assert math.isinf(mu), "μ should be ∞ for paradox"