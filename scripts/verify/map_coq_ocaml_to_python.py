#!/usr/bin/env python3
import re, json, os

ROOT = '/workspaces/The-Thiele-Machine'
OCAML_SIG = os.path.join(ROOT, 'build', 'thiele_core.mli')
PY_DIRS = ['thielecpu', 'src', 'thielemachine']

def extract_ocaml_vals(path):
    vals = []
    if not os.path.exists(path):
        return vals
    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
        for line in f:
            m = re.match(r'\s*val\s+(\w+)', line)
            if m:
                vals.append(m.group(1))
    return sorted(set(vals))

def find_python_defs(name):
    hits = []
    pat = re.compile(r'\bdef\s+' + re.escape(name) + r'\b')
    for d in PY_DIRS:
        base = os.path.join(ROOT, d)
        if not os.path.isdir(base):
            continue
        for dirpath, _, filenames in os.walk(base):
            for fn in filenames:
                if not fn.endswith('.py'):
                    continue
                path = os.path.join(dirpath, fn)
                try:
                    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
                        for i, line in enumerate(f, 1):
                            if pat.search(line):
                                hits.append(f"{os.path.relpath(path, ROOT)}:{i}:{line.strip()}")
                                break
                except Exception:
                    continue
    return hits

def main():
    vals = extract_ocaml_vals(OCAML_SIG)
    mapping = {}
    for v in vals:
        mapping[v] = find_python_defs(v)
    os.makedirs(os.path.join(ROOT, 'artifacts'), exist_ok=True)
    with open(os.path.join(ROOT, 'artifacts/coq_ocaml_python_mapping.json'), 'w', encoding='utf-8') as f:
        json.dump({'ocaml_vals_count': len(vals), 'mapping': mapping}, f, indent=2)
    print('WROTE artifacts/coq_ocaml_python_mapping.json')

if __name__ == '__main__':
    main()
