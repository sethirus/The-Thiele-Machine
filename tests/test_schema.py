import json
import glob
import os
import jsonschema

def test_golden_receipts_schema():
    with open("spec/receipt.schema.json") as f:
        schema = json.load(f)
    for path in glob.glob("spec/golden/*.json"):
        with open(path) as g:
            data = json.load(g)
        jsonschema.validate(instance=data, schema=schema)