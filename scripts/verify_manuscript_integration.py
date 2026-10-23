#!/usr/bin/env python3
"""Build and kernel-check the Integrated manuscript modules in their production namespace."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build/manuscript-check'
MODULES = ['EarnedCore', 'CompleteHost', 'SharpHost', 'SliceCore', 'Representation',
           'SlicedEstablishment', 'PassiveGeometry', 'GeometryLimits', 'Erasure',
           'NativeSliceBoundary']
MODULES += ['Multiplicity', 'StructuralMeter', 'Task', 'PeriodicIntersection', 'MultiExecution', 'SynchronizedCapacity', 'CommutationObstruction', 'TwoArms', 'CommutingGrid', 'AccountingBridge', 'MeterRepresentation', 'Monitor', 'Fibre', 'EditionCapacity', 'EditionHistory', 'CertifiedHistory', 'MaskWitness', 'ArchiveBound', 'HistoryCapacity', 'NativeFactAccounting', 'NativeErasure']


def statements(body):
    stack, names = [], []
    for line in body.splitlines():
        m = re.match(r'^Module (\w+)\.', line)
        e = re.match(r'^End (\w+)\.', line)
        n = re.match(r'^\s*(?:Theorem|Lemma|Corollary)\s+(\w+)', line)
        if m:
            stack.append(m[1])
        if n:
            names.append('.'.join([*stack, n[1]]))
        if e and stack and e[1] == stack[-1]:
            stack.pop()
    return names


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    result = {'status': 'running', 'scope': 'Integrated manuscript modules and EarnedCore; not the whole corpus'}
    result_path = OUT / 'proof-results.json'
    result_path.write_text(json.dumps(result, indent=2)+'\n')
    logs, commands, names, hashes = [], [], {}, {}
    def run(command):
        p = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
        logs.append('$ '+ ' '.join(command)+'\n'+p.stdout+p.stderr)
        (OUT / 'proof-check.log').write_text('\n'.join(logs))
        commands.append({'command': command, 'returncode': p.returncode})
        if p.returncode:
            raise RuntimeError(logs[-1][-6000:])
        return p.stdout
    try:
        for m in MODULES:
            p = ROOT / 'minimal' / (m+'.v')
            body = p.read_text()
            assert not re.search(r'\b(?:Admitted|admit|Axiom|Abort)\b',
                                 re.sub(r'\(\*.*?\*\)', '', body, flags=re.S)), m
            names[m] = statements(body)
            hashes[str(p.relative_to(ROOT))] = hashlib.sha256(p.read_bytes()).hexdigest()
        run(['make', '-C', 'coq', '-j2', *['../minimal/'+m+'.vo' for m in MODULES]])
        probe = OUT / 'Assumptions.v'
        probe.write_text('From Minimal Require Import '+' '.join(MODULES)+'.\n'+
                        '\n'.join(f'Print Assumptions Minimal.{m}.{n}.'
                                  for m, ns in names.items() for n in ns)+'\n')
        stdout = run(['coqc', '-Q', 'minimal', 'Minimal', '-Q', 'build/manuscript-check',
                      'ManuscriptIntegration', str(probe.relative_to(ROOT))])
        count = sum(map(len, names.values()))
        assert stdout.count('Closed under the global context') == count
        run(['coqchk', '-Q', 'minimal', 'Minimal', '-Q', 'build/manuscript-check',
             'ManuscriptIntegration', *['Minimal.'+m for m in MODULES], 'ManuscriptIntegration.Assumptions'])
        assert all(hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h for p,h in hashes.items())
        result.update(status='passed', statements=names, named_statements=count,
                      closed_under_global_context=True, kernel_checked=True, sha256=hashes)
    except Exception as e:
        result.update(status='failed', error=str(e))
        raise
    finally:
        result['commands'] = commands
        result_path.write_text(json.dumps(result,indent=2)+'\n')
    print(f'PASS: {count} named statements, closed assumptions, coqchk; production namespace Minimal.')

if __name__=='__main__':
    main()
