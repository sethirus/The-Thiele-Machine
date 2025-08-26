import argparse
import hashlib
import json
import os
import sys


def verify_dir(directory: str) -> float:
    total = 0.0
    for name in sorted(os.listdir(directory)):
        if not name.endswith('.json'):
            continue
        path = os.path.join(directory, name)
        with open(path, 'r') as fh:
            data = json.load(fh)
        mu_total = 0.0
        for step in data.get('steps', []):
            cert = step.get('certificate')
            h = hashlib.sha256(cert.encode()).hexdigest() if cert is not None else None
            if cert is None or step.get('certificate_hash') != h:
                raise ValueError(f"hash mismatch in {name}")
            mu = step.get('mu_delta')
            if mu == 'INF' or data.get('mu_total') == 'INF':
                raise ValueError(f"infinite mu in {name}")
            mu_total += float(mu)
        total += mu_total
        print(f"{name}: mu {mu_total}")
    print(f"total mu {total}")
    return total


def main() -> int:
    p = argparse.ArgumentParser(description='verify Thiele receipts')
    p.add_argument('directory')
    args = p.parse_args()
    try:
        verify_dir(args.directory)
    except ValueError as e:
        print(str(e))
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
