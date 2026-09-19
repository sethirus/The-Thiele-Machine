"""B4 Rice-theorem validation.  Every command runs under a time limit and
a resident-memory ceiling; a breach is recorded as a failure with its cause."""
from pathlib import Path
import subprocess, json, hashlib, time, os, signal
ROOT = Path(__file__).resolve().parents[3]
COQ = ROOT / 'coq'
HERE = Path(__file__).resolve().parent
FLAGS = []
for line in (COQ / '_CoqProject').read_text().splitlines():
    if line.startswith(('-R ', '-Q ', '-I ')):
        FLAGS.extend(line.split())
MODS = ['MM2ComplementUndec', 'VMSelfRice', 'VMSelfRiceUndec']
SRC = [COQ / 'kernel/foundation' / (m + '.v') for m in MODS]
TIME_LIMIT = 900
RSS_LIMIT_KB = 1800 * 1024

def rss_tree(pid):
    total = 0
    try:
        out = subprocess.run(['ps', '-o', 'pid=,ppid=,rss=', '-e'], capture_output=True, text=True).stdout
    except Exception:
        return 0
    rows = [tuple(int(x) for x in l.split()) for l in out.splitlines() if l.strip()]
    kids = {pid}
    changed = True
    while changed:
        changed = False
        for p, pp, r in rows:
            if pp in kids and p not in kids:
                kids.add(p); changed = True
    return max((r for p, pp, r in rows if p in kids), default=0)

report = {'sources': {s.name: hashlib.sha256(s.read_bytes()).hexdigest() for s in SRC},
          'limits': {'seconds': TIME_LIMIT, 'rss_kb': RSS_LIMIT_KB},
          'status': 'running', 'checks': []}
commands = [('build-' + m, ['coqc', *FLAGS, '-time', str(s)]) for m, s in zip(MODS, SRC)]
commands += [('integration', ['make', 'kernel/foundation/VMSelfRiceUndec.vo']),
             ('contracts', ['coqc', *FLAGS, str(HERE / 'Contracts.v')]),
             ('coqchk', ['coqchk', *FLAGS, '-silent', '-o'] + ['Kernel.' + m for m in MODS])]
for name, cmd in commands:
    start = time.monotonic(); peak = 0; breach = None
    with (HERE / (name + '.log')).open('w') as log:
        p = subprocess.Popen(cmd, cwd=COQ, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        while p.poll() is None:
            time.sleep(1)
            peak = max(peak, rss_tree(p.pid))
            if peak > RSS_LIMIT_KB:
                breach = 'rss'
            elif time.monotonic() - start > TIME_LIMIT:
                breach = 'time'
            if breach:
                os.killpg(p.pid, signal.SIGTERM); p.wait(); break
    rc = p.returncode
    report['checks'].append({'name': name, 'command': cmd, 'cwd': str(COQ), 'exit_code': rc,
                             'seconds': round(time.monotonic() - start, 3),
                             'peak_rss_kb': peak, 'limit_breach': breach})
    ok = rc == 0 and breach is None
    if not ok:
        report['status'] = 'failed'
    (HERE / 'validation.json').write_text(json.dumps(report, indent=2) + '\n')
    print(name, rc, breach or '', round(time.monotonic() - start, 1), 's', peak // 1024, 'MB', flush=True)
    if not ok:
        raise SystemExit(1)
report['status'] = 'passed'
(HERE / 'validation.json').write_text(json.dumps(report, indent=2) + '\n')
