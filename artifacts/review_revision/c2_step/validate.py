"""C2 single-cycle step refinement validation.  Every command runs under a time limit and
a resident-memory ceiling; a breach is recorded as a failure with its cause.
Usage: validate.py [check-name ...]  (default: all checks)."""
from pathlib import Path
import subprocess, json, hashlib, time, os, signal, sys
ROOT = Path(__file__).resolve().parents[3]
COQ = ROOT / 'coq'
HERE = Path(__file__).resolve().parent
FLAGS = []
for line in (COQ / '_CoqProject').read_text().splitlines():
    if line.startswith(('-R ', '-Q ', '-I ')):
        FLAGS.extend(line.split())
MODS = ['RuleNext', 'RuleStep', 'StepEval', 'StepFields', 'StepWordFacts',
        'StepRefineCommon', 'PopcountSWAR', 'StepRefine', 'StepFieldsMorph', 'StepRefineMorph', 'RuleEnabled',
        'ChshArith', 'ChshDecoded', 'ChshStepFields', 'ChshFsm', 'ChshPhases', 'ChshRun', 'ChshRetire',
        'FsmDecoded', 'LassertSpec', 'LassertStepFields', 'LassertWord', 'LassertRetire',
        'MorphTensorGap', 'CouplingFsmEnds', 'CouplingFsmLoad', 'CouplingFsmNorm', 'CouplingFsmRun',
        'CouplingMorphRich', 'CouplingMorphKami', 'CouplingMorphRetire',
        'CouplingFsmCopy', 'CouplingFsmJoin', 'BoundaryRun']
SRC = [COQ / 'kami_hw' / (m + '.v') for m in MODS] + [COQ / 'kami_hw' / 'ThieleCPUCore.v',
       COQ / 'kami_hw' / 'Abstraction.v', COQ / 'kami_hw' / 'ImplementationContract.v']
GENS = ['generate_rule_next.py', 'generate_step_eval.py', 'generate_step_fields.py', 'generate_step_refine.py',
        'generate_step_fields_morph.py', 'generate_step_refine_morph.py', 'generate_rule_enabled.py',
        'generate_chsh_decoded.py', 'generate_chsh_step_fields.py', 'generate_chsh_fsm.py', 'generate_chsh_phases.py',
        'generate_chsh_run.py', 'generate_chsh_retire.py',
        'generate_fsm_next.py', 'generate_fsm_decoded.py', 'fsm_decoded_specs.txt', 'generate_lassert_step_fields.py', 'generate_hw_boundary.py']
TIME_LIMIT = 900
# coqchk rechecks the whole dependency closure (Kami, kernel), not only these modules.
LIMITS = {'coqchk': 2400}
RSS_LIMIT_KB = 1800 * 1024
MIN_AVAIL_KB = 1200 * 1024

def rss_tree(pid):
    out = subprocess.run(['ps', '-o', 'pid=,ppid=,rss=', '-e'], capture_output=True, text=True).stdout
    rows = [tuple(int(x) for x in l.split()) for l in out.splitlines() if l.strip()]
    kids = {pid}; changed = True
    while changed:
        changed = False
        for p, pp, r in rows:
            if pp in kids and p not in kids:
                kids.add(p); changed = True
    return max((r for p, pp, r in rows if p in kids), default=0)

def avail_kb():
    return int(next(l.split()[1] for l in Path('/proc/meminfo').read_text().splitlines()
                    if l.startswith('MemAvailable:')))

commands = [('dry-run', ['make', '-n', 'all']),
            ('contracts', ['coqc', *FLAGS, '-time', str(HERE / 'Contracts.v')]),
            ('coqchk', ['coqchk', *FLAGS, '-silent', '-o'] + ['KamiHW.' + m for m in MODS])]
wanted = set(sys.argv[1:]) or {n for n, _ in commands}
unknown = wanted - {n for n, _ in commands}
if unknown:
    raise SystemExit('Unknown checks: ' + ', '.join(sorted(unknown)))
out = HERE / 'validation.json'
report = json.loads(out.read_text()) if out.exists() else {}
# Tie each result to the input it actually checked. A partial rerun must not
# certify old checker output against newly recorded source hashes.
def input_hashes():
    paths = set(COQ.rglob('*.v'))
    for vendor in ['kami/Kami', 'bbv', 'coq-undecidability/theories']:
        paths.update((ROOT / 'vendor' / vendor).rglob('*.v'))
    paths.update(SRC)
    paths.update(ROOT / 'scripts' / g for g in GENS)
    paths.update([COQ / '_CoqProject', HERE / 'Contracts.v', Path(__file__)])
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}

inputs = input_hashes()
fingerprint = hashlib.sha256(json.dumps(inputs, sort_keys=True).encode()).hexdigest()
report.update({'sources': {s.name: hashlib.sha256(s.read_bytes()).hexdigest() for s in SRC},
               'generators': {g: hashlib.sha256((ROOT / 'scripts' / g).read_bytes()).hexdigest() for g in GENS},
               'limits': {'seconds': TIME_LIMIT, 'per_check_seconds': LIMITS, 'rss_kb': RSS_LIMIT_KB, 'minimum_available_kb': MIN_AVAIL_KB},
               'inputs': inputs, 'input_fingerprint': fingerprint, 'status': 'running'})
checks = {c['name']: c for c in report.get('checks', [])}
out.write_text(json.dumps(report, indent=2) + '\n')
for name, cmd in commands:
    if name not in wanted:
        continue
    start = time.monotonic(); peak = 0; breach = None
    with (HERE / (name + '.log')).open('w') as log:
        p = subprocess.Popen(cmd, cwd=COQ, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        while p.poll() is None:
            time.sleep(1)
            peak = max(peak, rss_tree(p.pid))
            if peak > RSS_LIMIT_KB:
                breach = 'rss'
            elif avail_kb() < MIN_AVAIL_KB:
                breach = 'system-memory'
            elif time.monotonic() - start > LIMITS.get(name, TIME_LIMIT):
                breach = 'time'
            if breach:
                os.killpg(p.pid, signal.SIGTERM); p.wait(); break
    checks[name] = {'name': name, 'command': cmd, 'cwd': str(COQ), 'exit_code': p.returncode,
                    'seconds': round(time.monotonic() - start, 3), 'peak_rss_kb': peak, 'limit_breach': breach,
                    'input_fingerprint': fingerprint,
                    'inputs_unchanged': input_hashes() == inputs}
    if name == 'dry-run':
        checks[name]['compilation_pending'] = any(
            'COQC ' in line for line in (HERE / 'dry-run.log').read_text().splitlines())
    report['checks'] = list(checks.values())
    out.write_text(json.dumps(report, indent=2) + '\n')
    print(name, p.returncode, breach or '', round(time.monotonic() - start, 1), 's', peak // 1024, 'MB', flush=True)
    if (p.returncode != 0 or breach or not checks[name]['inputs_unchanged']
            or checks[name].get('compilation_pending')):
        report['status'] = 'failed'; out.write_text(json.dumps(report, indent=2) + '\n')
        raise SystemExit(1)
current = [name for name, cmd in commands if name in checks
           and checks[name].get('input_fingerprint') == fingerprint
           and checks[name].get('inputs_unchanged')
           and not checks[name].get('compilation_pending')
           and checks[name]['command'] == cmd
           and checks[name]['exit_code'] == 0 and not checks[name]['limit_breach']]
report['pending_checks'] = [name for name, _ in commands if name not in current]
report['status'] = 'passed' if not report['pending_checks'] else 'incomplete'
out.write_text(json.dumps(report, indent=2) + '\n')
