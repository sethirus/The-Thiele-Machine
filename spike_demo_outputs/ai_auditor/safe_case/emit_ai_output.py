import json
data = {"id": "kitten_01", "is_kitten": 0.98, "is_dangerous": 0.01}
print(json.dumps(data, indent=2, sort_keys=True))
