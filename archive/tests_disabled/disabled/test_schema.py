# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import json
import glob
import os
import jsonschema

def test_golden_receipts_schema():
    with open("docs/spec/receipt.schema.json") as f:
        schema = json.load(f)
    for path in glob.glob("spec/golden/*.json"):
        with open(path) as g:
            data = json.load(g)
        if "steps" not in data:
            continue
        jsonschema.validate(instance=data, schema=schema)