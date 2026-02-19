#!/usr/bin/env python3
import subprocess
import sys
import shlex

TIMEOUT = 60

def collect_tests():
    # Use pytest to list node ids
    p = subprocess.run([sys.executable, '-m', 'pytest', '--collect-only', '-q'], capture_output=True, text=True)
    if p.returncode not in (0,1):
        print('Failed to collect tests', p.returncode)
        print(p.stdout)
        print(p.stderr)
        sys.exit(2)
    lines = [l.strip() for l in p.stdout.splitlines() if l.strip()]
    return lines

def run_test(nodeid):
    print(f"Running: {nodeid}")
    try:
        p = subprocess.run([sys.executable, '-m', 'pytest', nodeid, '-q'], timeout=TIMEOUT)
        return ('ok' if p.returncode == 0 else 'failed', p.returncode)
    except subprocess.TimeoutExpired:
        return ('timeout', None)

def main():
    tests = collect_tests()
    if not tests:
        print('No tests collected')
        return 0
    for node in tests:
        status, code = run_test(node)
        if status == 'ok':
            continue
        elif status == 'failed':
            print(f"Test failed: {node} (exit {code})")
            return 1
        elif status == 'timeout':
            print(f"Test timed out (> {TIMEOUT}s): {node}")
            # print helpful next-step info
            print('Suggestion: inspect the test file and any external resources it uses.')
            return 2
    print('All tests completed under timeout')
    return 0

if __name__ == '__main__':
    sys.exit(main())
