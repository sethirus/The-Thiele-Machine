import json
data = {"id": "lion_cub_02", "is_kitten": 0.92, "is_dangerous": 0.85}
print(json.dumps(data, indent=2, sort_keys=True))
