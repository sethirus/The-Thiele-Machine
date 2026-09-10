#!/usr/bin/env python3
"""Compare a regenerated assumption receipt with the committed proof results."""
from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from coq_proof_scope import FULL_ASSUMPTION_PROBE
from run_assumption_batches import split_probe

ROOT = Path(__file__).resolve().parents[1]
RECEIPT = 'artifacts/print_assumptions_all_proofs.json'
OUTPUT = 'artifacts/print_assumptions_all_proofs.txt'
RUN_FIELDS = {'generated', 'raw_output_sha256', 'stderr_excerpt'}


def theorem_results(probe: str, output: str) -> dict[str, tuple[str, ...]]:
    _, queries = split_probe(probe)
    blocks: list[list[str]] = []
    for line in output.splitlines():
        if not line.strip() or line.startswith('Fetching opaque proofs from disk for '):
            continue
        if line in ('Closed under the global context', 'Axioms:'):
            blocks.append([line])
        elif not blocks:
            raise ValueError(f'Unexpected output before a result: {line}')
        else:
            blocks[-1].append(line)
    if len(blocks) != len(queries):
        raise ValueError(f'{len(queries)} queries but {len(blocks)} results')
    if len(set(queries)) != len(queries):
        raise ValueError('Duplicate assumption query')
    results = {}
    for query, block in zip(queries, blocks):
        if block[0] == 'Closed under the global context':
            if len(block) != 1:
                raise ValueError(f'Unexpected text after closed result for {query}')
            results[query] = ()
            continue
        declarations: list[list[str]] = []
        for line in block[1:]:
            if not line[0].isspace():
                declarations.append([line.strip()])
            elif declarations:
                declarations[-1].append(line.strip())
            else:
                raise ValueError(f'Axiom continuation without a name for {query}')
        normalized = [' '.join(parts) for parts in declarations]
        if not normalized or any(not re.match(r"^[\w.']+\s*:\s*\S", item) for item in normalized):
            raise ValueError(f'Malformed axiom declaration for {query}')
        results[query] = tuple(sorted(normalized))
    return results


def compare_receipts(old_probe: str, old_output: str, old_meta: dict,
                     fresh_probe: str, fresh_output: str, fresh_meta: dict) -> None:
    for metadata in (old_meta, fresh_meta):
        if not metadata.get('alignment_ok') or metadata.get('unexpected_lines_in_output') != 0:
            raise ValueError('Receipt reports misalignment or unexpected output')
    old = theorem_results(old_probe, old_output)
    fresh = theorem_results(fresh_probe, fresh_output)
    if old != fresh:
        changed = sorted(q for q in old.keys() | fresh.keys() if old.get(q) != fresh.get(q))
        raise ValueError('Theorem/axiom results differ:\n' + '\n'.join(changed[:20]))
    old_stable = {k: v for k, v in old_meta.items() if k not in RUN_FIELDS}
    fresh_stable = {k: v for k, v in fresh_meta.items() if k not in RUN_FIELDS}
    if old_stable != fresh_stable:
        fields = sorted(k for k in old_stable.keys() | fresh_stable.keys()
                        if old_stable.get(k) != fresh_stable.get(k))
        raise ValueError('Receipt metadata differs: ' + ', '.join(fields))


def committed(path: str) -> str:
    return subprocess.run(['git', 'show', f'HEAD:{path}'], cwd=ROOT, text=True,
                          capture_output=True, check=True).stdout


def main() -> None:
    try:
        compare_receipts(committed(FULL_ASSUMPTION_PROBE), committed(OUTPUT),
                         json.loads(committed(RECEIPT)),
                         (ROOT / FULL_ASSUMPTION_PROBE).read_text(),
                         (ROOT / OUTPUT).read_text(), json.loads((ROOT / RECEIPT).read_text()))
    except (ValueError, subprocess.CalledProcessError) as error:
        print(f'[assumption-receipt-check] FAIL: {error}', file=sys.stderr)
        raise SystemExit(1)
    print('[assumption-receipt-check] All theorem/axiom results and stable metadata match.')


if __name__ == '__main__':
    main()
