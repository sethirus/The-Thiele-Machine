import sys
import json
import requests

with open(sys.argv[1], 'r') as f:
    text = f.read()

payload = {"text": text}
try:
    r = requests.post("http://localhost:7331/verify", json=payload)
    print(json.dumps(r.json(), indent=2))
except Exception as e:
    print(f"Error: {e}")
