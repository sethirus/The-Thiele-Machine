# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/bin/bash
set -e


# Robustly create results directory at repo root regardless of working directory
REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
RESULTS_DIR="$REPO_ROOT/results"
mkdir -p "$RESULTS_DIR"
LEMMA_FILE="$RESULTS_DIR/lemmas.txt"
: > "$LEMMA_FILE"

if command -v coqc >/dev/null 2>&1; then
  echo "Running Coq proofs"
  (cd coq/thielemachine/coqproofs && coqc ThieleMachine.v >/dev/null && echo "tm_cpu_simulates_step cost_of_paradox_is_infinite" | tee -a "$LEMMA_FILE")
  (cd coq/thielemachine/coqproofs && coqc Separation.v >/dev/null && echo "thiele_machine_exponential_separation" | tee -a "$LEMMA_FILE")
else
  echo "proofs skipped (coqc missing)"
  echo "proofs skipped" > "$LEMMA_FILE"
fi

python - <<'PY'
from examples.xor_tseitin import run_demo as xor_demo
from examples.at_most_k import run_demo as amk_demo
from examples.graph_partition import run_demo as gp_demo
xor_demo()
amk_demo()
gp_demo()
PY

python scripts/thiele_verify.py receipts

python scripts/challenge.py verify receipts | tee results/challenge.log

python - <<'PY'
from examples.at_most_k import run_demo
info = run_demo(save=False)
assert info['result'] == (sum([1,0,1]) <= 2)
print('Conservativity ✓')
PY

python - <<'PY'
from examples.xor_tseitin import run_demo
info = run_demo(save=False)
assert info['mu_refined'] >= info['mu_blind']
print('No-Free-Sight ✓')
PY

mkdir -p receipts/paradox
python - <<'PY'
import json, hashlib
cert = 'x=0 and x=1'
data = {'steps':[{'step_id':0,'partition_id':0,'axiom_ids':['contradiction'],'certificate':cert,'certificate_hash':hashlib.sha256(cert.encode()).hexdigest(),'mu_delta':'INF'}], 'mu_total':'INF'}
with open('receipts/paradox/paradox.json','w') as f: json.dump(data,f)
PY
if python scripts/thiele_verify.py receipts/paradox >/tmp/paradox.log 2>&1; then
  cat /tmp/paradox.log
  echo 'Paradox check failed'
  exit 1
else
  cat /tmp/paradox.log
  echo 'Paradox ⇒ μ=∞ ✓'
fi
rm -rf receipts/paradox

tmpdir=$(mktemp -d)
cp receipts/xor_tseitin.json "$tmpdir/corrupt.json"
python - "$tmpdir/corrupt.json" <<'PY'
import json, sys
p = sys.argv[1]
with open(p) as f:
    data = json.load(f)
data['steps'][0]['certificate'] = 'bad'
with open(p, 'w') as f:
    json.dump(data, f)
PY
if python scripts/thiele_verify.py "$tmpdir" >/tmp/audit.log 2>&1; then
  cat /tmp/audit.log
  echo 'Auditability check failed'
  exit 1
else
  cat /tmp/audit.log
  echo 'Auditability ✓'
fi
rm -r "$tmpdir"

python - <<'PY'
import json, hashlib, os, subprocess, datetime
paths=[('xor_tseitin','receipts/xor_tseitin.json','examples/xor_tseitin_plot.png'),('at_most_k','receipts/at_most_k.json','examples/at_most_k_plot.png'),('graph_partition','receipts/graph_partition.json','examples/graph_partition_plot.png')]
commit=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip()
timestamp=datetime.datetime.utcnow().isoformat()+'Z'
challenge=''
if os.path.exists('results/challenge.log'):
    with open('results/challenge.log') as cf:
        challenge=cf.read().strip()
os.makedirs('results', exist_ok=True)
with open('results/RESULTS.md','w') as out:
    out.write('# Run results\n\n')
    out.write(f'commit `{commit}`\n\n')
    out.write(f'timestamp `{timestamp}`\n\n')
    out.write('## Plots\n')
    for name,rp,plot in paths:
        if os.path.exists(plot):
            out.write(f'![{name}]({plot})\n')
    out.write('\n## Receipts\n')
    for name,rp,_ in paths:
        if os.path.exists(rp):
            with open(rp) as fh:
                data=json.load(fh)
            mu=sum(float(s['mu_delta']) for s in data.get('steps',[]) if s.get('mu_delta')!='INF')
            digest=hashlib.sha256(open(rp,'rb').read()).hexdigest()[:8]
            out.write(f'- {name}: μ={mu}, digest={digest}\n')
    out.write('\n## Proofs\n')
    if os.path.exists('results/lemmas.txt'):
        with open('results/lemmas.txt') as lf:
            for line in lf:
                out.write(f'- {line.strip()}\n')
    out.write('\n## Challenge harness\n')
    out.write('`$ python scripts/challenge.py verify receipts`\n')
    if challenge:
        out.write(f'{challenge}\n')
PY
