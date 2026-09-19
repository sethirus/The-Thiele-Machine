#!/usr/bin/env python3
"""Rebuild repository Coq sources and vendored dependencies in a fresh local tree.

Requires native Coq/OCaml, GNU make and CSDP. Never installs packages, downloads
sources, invokes a container runtime, or copies precompiled proof objects.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shlex
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
FOLDERS = ('coq', 'vendor/bbv', 'vendor/kami',
           'vendor/coq-undecidability/theories')
CONFIGS = ('coq/_CoqProject', 'coq/Makefile.local',
           'vendor/bbv/Makefile', 'vendor/bbv/_CoqProject',
           'vendor/kami/Makefile', 'vendor/kami/_CoqProject',
           'vendor/coq-undecidability/theories/Makefile',
           'vendor/coq-undecidability/theories/_CoqProject',
           'vendor/coq-undecidability/LICENSE',
           'vendor/coq-undecidability/UPSTREAM.md',
           'scripts/reproduce_coq.py', 'scripts/check_review_contracts.py')
DEFAULT_PROBES = ('artifacts/review_revision/cm2_delivery_probe.v',
                  'artifacts/review_revision/dispatch_delivery_probe.v',
                  'artifacts/review_revision/core_execution_probe.v',
                  'artifacts/review_revision/dispatch_observation/Contracts.v',
                  'artifacts/review_revision/dispatch_observation/FamilyContracts.v',
                  'artifacts/review_revision/dispatch_observation/CastProbe.v',
                  'artifacts/review_revision/specialization_repair/Contracts.v',
                  'artifacts/review_revision/self_interpreter/Contracts.v',
                  'artifacts/review_revision/rice/Contracts.v',
                  'artifacts/review_revision/c1_c2/Contracts.v',
                  'artifacts/review_revision/c2_dispatch/Contracts.v',
                  'artifacts/review_revision/c2_invariants/Contracts.v')
# c2_dispatch/FetchFactoring.v is deliberately not a probe: its own header
# calls it "exact AST preservation of the fetch factoring, before later CPU
# changes," and it is -- a literal transcript of the "step" rule's AST from
# the 2026-09-14 fetch-factoring session, checked by `reflexivity` against
# nth_error (getRules thieleCore) 0. The CPU rule has since changed by design
# (the high_value_locked fault removed from the mc_phase guard, the COMPOSE
# label table write added, and more), each change its own audited session in
# STATUS.md. Re-running this file asserts the rule never changed since that
# one session, which is false on purpose. Kept in the tree as the historical
# record it already was; not re-verified as live evidence.
_ROOT_RE = re.compile(r'^-(R|Q)\s+(\S+)\s+(\S+)$')


def discover_project_libraries(coqproject: Path) -> list[str]:
    """Every module coq/_CoqProject lists, as its coqchk-qualified name.

    Parsed from the project file itself (not a frozen list) so this never
    drifts out of date as files are added, the way a hand-maintained tuple
    silently did.
    """
    roots: list[tuple[tuple[str, ...], str]] = []
    files: list[str] = []
    for line in coqproject.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        m = _ROOT_RE.match(line)
        if m:
            _, phys, log = m.groups()
            roots.append((Path(phys).parts, log))
        elif line.endswith('.v'):
            files.append(line)

    def to_logical(fpath: str) -> str:
        parts = Path(fpath).parts
        best: tuple[int, str] | None = None
        for phys_parts, log in roots:
            n = len(phys_parts)
            if parts[:n] == phys_parts and (best is None or n > best[0]):
                best = (n, log)
        if best is None:
            return Path(fpath).stem
        n, log = best
        stem_parts = list(parts[n:-1]) + [Path(parts[-1]).stem]
        return '.'.join(([log] if log else []) + stem_parts)

    return sorted({to_logical(f) for f in files})


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def collect_inputs(root: Path, probes: list[str]) -> list[Path]:
    inputs = {p for folder in FOLDERS for p in (root / folder).rglob('*.v')
              if '.git' not in p.parts}
    inputs.update(root / name for name in CONFIGS)
    for name in probes:
        path = (root / name).resolve()
        if root not in path.parents or path.suffix != '.v':
            raise ValueError('probes must be .v files inside the repository')
        inputs.add(path)
    return sorted(inputs)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        help='Fresh directory; defaults to artifacts/reproduction/<UTC time>')
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('--probe', action='append')
    parser.add_argument('--library', action='append')
    parser.add_argument('--prepare-only', action='store_true',
                        help='Snapshot inputs and commands without compiling; not a passing build')
    parser.add_argument('--resume', action='store_true',
                        help='Resume --output after verifying its captured source and tool hashes')
    args = parser.parse_args()
    if args.resume and not args.output:
        parser.error('--resume requires --output')
    if args.jobs < 1:
        parser.error('jobs must be positive')
    output = (args.output or ROOT / 'artifacts/reproduction' /
              datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')).resolve()
    if output == ROOT or output in ROOT.parents or any(
            output == ROOT / f or ROOT / f in output.parents for f in FOLDERS):
        parser.error('output must not contain the checkout or lie in a source directory')
    previous = None
    if args.resume:
        previous = json.loads((output / 'reproduction.json').read_text())
        if previous['status'] == 'passed':
            parser.error('this reproduction already passed')
        if args.probe or args.library:
            parser.error('resume retains the captured probes and libraries')
    probes = previous['probes'] if previous else args.probe or list(DEFAULT_PROBES)
    libraries = previous['libraries'] if previous else (
        args.library or discover_project_libraries(ROOT / 'coq/_CoqProject'))
    inputs = collect_inputs(ROOT, probes)
    missing = [str(p.relative_to(ROOT)) for p in inputs if not p.is_file()]
    if missing:
        parser.error('missing repository inputs: ' + ', '.join(missing))
    source = output / 'source'
    if previous:
        manifest_path = output / 'source-manifest.json'
        if digest(manifest_path) != previous['source_manifest_sha256']:
            parser.error('captured source manifest has changed')
        manifest = json.loads(manifest_path.read_text())
        if any(not (source / name).is_file() or digest(source / name) != item['sha256']
               for name, item in manifest.items()):
            parser.error('captured source has changed')
    else:
        output.mkdir(parents=True, exist_ok=False)
        manifest = {}
        for path in inputs:
            name = path.relative_to(ROOT)
            target = source / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(path.read_bytes())
            manifest[str(name)] = {'sha256': digest(target), 'bytes': target.stat().st_size}
        assert not any(source.rglob('*.vo'))
        (source / 'build/kami_hw').mkdir(parents=True)
        (source / 'vendor/kami/Kami/Ext/Ocaml').mkdir(parents=True, exist_ok=True)
        (output / 'source-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    flags = []
    for line in (source / 'coq/_CoqProject').read_text().splitlines():
        if line.startswith(('-R ', '-Q ', '-I ')):
            flags.extend(shlex.split(line))
    commands = [
        ('bbv-build', source, ['make', '-C', 'vendor/bbv', f'-j{args.jobs}']),
        ('kami-build', source, ['make', '-C', 'vendor/kami', f'-j{args.jobs}']),
        ('project-makefile', source / 'coq', ['coq_makefile', '-f', '_CoqProject', '-o', 'Makefile']),
        ('coq-build', source, ['make', '-C', 'coq', f'-j{args.jobs}']),
    ]
    commands += [(f'probe-{i:02d}', source / 'coq',
                  ['coqtop', '-batch', *flags, '-l', str(source / p)])
                 for i, p in enumerate(probes)]
    commands.append(('coqchk', source / 'coq', ['coqchk', '-silent', '-o', *flags, *libraries]))
    env = os.environ.copy()
    # Replace inherited project lookup paths: only this snapshot's libraries.
    env['COQPATH'] = os.pathsep.join(str(source / f) for f in ('vendor/bbv/src', 'vendor/kami'))
    env.pop('COQBIN', None)
    env['OCAMLRUNPARAM'] = 'l=64M'
    report = {'started_utc': datetime.now(timezone.utc).isoformat(),
              'scope': 'Fresh source-only native rebuild using the local toolchain; not independent review or a separate operating environment.',
              'status': 'prepared', 'host_compiled_artifacts_copied': False,
              'coqchk_bypass_flags': False, 'network_commands': False,
              'source_manifest_sha256': digest(output / 'source-manifest.json'),
              'source_file_count': len(manifest), 'runner_sha256': digest(Path(__file__)),
              'environment': {k: env[k] for k in ('COQPATH', 'OCAMLRUNPARAM')},
              'commands': [{'name': n, 'cwd': str(c), 'argv': a, 'exit_code': None}
                           for n, c, a in commands], 'probes': probes, 'libraries': libraries}
    report_path = output / 'reproduction.json'
    if previous:
        report = previous
        report.setdefault('resumptions', []).append({
            'time_utc': datetime.now(timezone.utc).isoformat(),
            'previous_status': previous['status'], 'runner_sha256': digest(Path(__file__))})

    def save() -> None:
        report_path.write_text(json.dumps(report, indent=2) + '\n')

    save()
    print(f'Reproduction directory: {output}', flush=True)
    if args.prepare_only:
        return 0
    required = ('coqc', 'coqtop', 'coqchk', 'coq_makefile', 'ocamlc', 'make', 'csdp')
    report['tools'] = {name: shutil.which(name) for name in required}
    missing_tools = [name for name in required if report['tools'][name] is None]
    if missing_tools:
        report.update(status='failed', exit_code=127, missing_tools=missing_tools)
        save()
        print('Missing native tools: ' + ', '.join(missing_tools), file=sys.stderr)
        return 127
    tool_hashes = {name: digest(Path(path).resolve()) for name, path in report['tools'].items()}
    if previous and report.get('tool_sha256') and tool_hashes != report['tool_sha256']:
        parser.error('native tool binaries changed; start a fresh reproduction')
    report['tool_sha256'] = tool_hashes
    with (output / 'tool-versions.log').open('w') as log:
        for cmd in (['coqc', '--version'], ['coqchk', '--version'],
                    ['ocamlc', '-version'], ['make', '--version']):
            subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT, env=env, check=True)
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    wanted = 64 * 1024 * 1024
    resource.setrlimit(resource.RLIMIT_STACK, (wanted if hard == resource.RLIM_INFINITY else min(wanted, hard), hard))
    report['stack_limit_bytes'] = resource.getrlimit(resource.RLIMIT_STACK)[0]
    result = 0
    try:
        for entry in report['commands']:
            if entry['exit_code'] == 0:
                continue
            report['status'] = 'running'
            save()
            print(f"Running {entry['name']}", flush=True)
            log_path = output / (entry['name'] + '.log')
            if log_path.exists():
                suffix = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
                log_path.rename(output / (entry['name'] + '.' + suffix + '.log'))
            with log_path.open('w') as log:
                result = subprocess.run(entry['argv'], cwd=entry['cwd'], env=env,
                                        stdout=log, stderr=subprocess.STDOUT).returncode
            entry['exit_code'] = result
            save()
            if result:
                break
    except KeyboardInterrupt:
        result = 130
    except OSError as error:
        result = 127
        report['execution_error'] = str(error)
    finally:
        resource.setrlimit(resource.RLIMIT_STACK, (soft, hard))
        report['source_mismatches_after_build'] = [
            name for name, item in manifest.items()
            if not (source / name).is_file() or digest(source / name) != item['sha256']]
        result = result or int(bool(report['source_mismatches_after_build']))
        report.update(status='passed' if result == 0 else 'failed', exit_code=result,
                      finished_utc=datetime.now(timezone.utc).isoformat())
        report['logs'] = {p.name: digest(p) for p in output.glob('*.log')}
        save()
    if result == 0:
        (output / 'result.txt').write_text('passed\n')
    print(f"Reproduction {report['status']} (exit {result})", flush=True)
    return result


if __name__ == '__main__':
    sys.exit(main())
