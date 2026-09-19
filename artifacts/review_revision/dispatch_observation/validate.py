"""Rebuild and dependency-check the actual dispatch observation bridge."""
from pathlib import Path
import hashlib
import json
import subprocess
import time
import sys

FAMILY_ONLY = sys.argv[1:] == ["--family-only"]
if sys.argv[1:] and not FAMILY_ONLY:
    raise SystemExit("usage: validate.py [--family-only]")

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
COQ = ROOT / 'coq'
FLAGS = []
for line in (COQ / '_CoqProject').read_text().splitlines():
    if line.startswith(('-R ', '-Q ', '-I ')):
        FLAGS.extend(line.split())
SOURCES = [
    'coq/kami_hw/ActionObservation.v',
    'coq/kami_hw/DispatchObservation.v',
    'coq/kami_hw/DispatchAbstractionBridge.v',
    'coq/kami_hw/DispatchAddFamily.v',
    'coq/kami_hw/ActionEvaluator.v',
    'coq/kami_hw/DispatchExecution.v',
    'coq/kami_hw/ThieleCPUCore.v',
    'coq/kami_hw/Abstraction.v',
    'vendor/kami/Kami/Semantics.v',
    'coq/_CoqProject',
]
report = {'sources': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
                      for p in SOURCES}, 'checks': []}

def run(name, command):
    start = time.monotonic()
    with (HERE / (name + '.log')).open('w') as log:
        result = subprocess.run(command, cwd=COQ, stdout=log, stderr=subprocess.STDOUT)
    report['checks'].append({'name': name, 'command': command, 'cwd': str(COQ),
                             'exit_code': result.returncode,
                             'seconds': time.monotonic() - start})
    (HERE / ('family-validation.json' if FAMILY_ONLY else 'validation.json')).write_text(json.dumps(report, indent=2) + '\n')
    print(f'{name}: exit {result.returncode}', flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)

for source in (SOURCES[3:4] if FAMILY_ONLY else SOURCES[:4]):
    run(Path(source).stem, ['coqc', *FLAGS, '-time', str(ROOT / source)])
run('family-integrated-build' if FAMILY_ONLY else 'integrated-build',
    ['make', '-j2', 'kami_hw/DispatchAbstractionBridge.vo', 'kami_hw/DispatchAddFamily.vo'])
if not FAMILY_ONLY:
    run('contracts', ['coqc', *FLAGS, str(HERE / 'Contracts.v')])
run('family-contracts', ['coqc', *FLAGS, str(HERE / 'FamilyContracts.v')])
run('cast-probe', ['coqc', *FLAGS, str(HERE / 'CastProbe.v')])
run('family-coqchk' if FAMILY_ONLY else 'coqchk',
    ['coqchk', *FLAGS, '-silent', '-o',
     *(['KamiHW.DispatchAddFamily'] if FAMILY_ONLY else
       ['KamiHW.DispatchAbstractionBridge', 'KamiHW.DispatchAddFamily'])])
