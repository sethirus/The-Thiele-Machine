#!/usr/bin/env python3
"""Reproduce all completed research suites; the grouped-mask experiment is excluded."""
from pathlib import Path
import json
import subprocess
import sys

root = Path(__file__).resolve().parent
suites = [
    ('baseline', '.', 'verify.py'),
    ('followup', 'followup', 'verify_followup.py'),
    ('wide-interval', 'followup', 'verify_wide.py'),
    ('succinct-interval', 'interval-succinct', 'verify_inplace.py'),
    ('machine-preservation', 'machine-preservation', 'verify.py'),
    ('partition-preservation', 'partition-preservation', 'verify.py'),
    ('partition-costs', 'partition-costs', 'verify.py'),
]
results = []
for name, directory, script in suites:
    result = subprocess.run([sys.executable, script], cwd=root / directory,
                            capture_output=True, text=True)
    log = root / directory / ('handoff-' + name + '.txt')
    log.write_text(result.stdout + result.stderr)
    results.append({'suite': name, 'exit_code': result.returncode,
                    'output': str(log.relative_to(root))})
    print(name + ': ' + ('PASS' if result.returncode == 0 else 'FAIL'), flush=True)
(root / 'HANDOFF-VERIFICATION.json').write_text(json.dumps(results, indent=2) + '\n')
sys.exit(any(r['exit_code'] != 0 for r in results))
