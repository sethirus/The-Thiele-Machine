#!/usr/bin/env python3
"""Run pip-audit and fail if any HIGH/CRITICAL or new unallowed vulnerabilities are present."""
import json
import subprocess
import sys
from pathlib import Path

ALLOWED = set()  # Optionally list allowed vuln IDs here (CVE ids)
OUT = Path('artifacts/pip_audit.json')

p = subprocess.run(['pip-audit', '-f', 'json', '--local'], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
if p.returncode != 0 and p.stdout == b'':
    print('pip-audit failed to run:', p.stderr.decode(), file=sys.stderr)
    sys.exit(2)

try:
    data = json.loads(p.stdout.decode())
except Exception as e:
    print('Failed to parse pip-audit JSON output:', e, file=sys.stderr)
    print('Raw output:', p.stdout.decode(), file=sys.stderr)
    sys.exit(2)

OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text(json.dumps(data, indent=2))

vuln_count = 0
for dep in data.get('dependencies', []):
    for v in dep.get('vulns', []):
        if v.get('id') in ALLOWED:
            continue
        vuln_count += 1
        print(f"VULN: {dep.get('name')}@{dep.get('version')}: {v.get('id')} - {v.get('description')[:200].strip()}...")

if vuln_count > 0:
    print(f"\nERROR: Found {vuln_count} vulnerable dependencies. See {OUT}")
    sys.exit(1)

print('pip-audit: no unexpected vulnerabilities found')
sys.exit(0)
