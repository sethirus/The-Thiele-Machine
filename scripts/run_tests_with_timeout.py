#!/usr/bin/env python3
import subprocess
import sys
import time
import os


def collect_tests():
    p = subprocess.run(["pytest", "--collect-only", "-q"], capture_output=True, text=True)
    lines = [l.strip() for l in p.stdout.splitlines() if l.strip()]
    return lines


def run_test(nodeid, timeout=60):
    start = time.time()
    try:
        p = subprocess.run(["pytest", "-q", nodeid], capture_output=True, text=True, timeout=timeout)
        dur = time.time() - start
        return p.returncode, dur, p.stdout + p.stderr
    except subprocess.TimeoutExpired as e:
        dur = time.time() - start
        out = (e.stdout or "") + (e.stderr or "")
        return None, dur, out


def safe_name(nodeid):
    return nodeid.replace("/", "__").replace("::", "__").replace(" ", "_")


def main():
    timeout_seconds = 60
    nodeids = collect_tests()
    print(f"Collected {len(nodeids)} tests")
    if not nodeids:
        print("No tests collected; aborting.")
        sys.exit(1)

    os.makedirs("artifacts", exist_ok=True)

    for node in nodeids:
        print(f"Running: {node}")
        rc, dur, out = run_test(node, timeout=timeout_seconds)
        print(f"-> Duration: {dur:.1f}s  Return: {rc}")
        if rc is None or dur > timeout_seconds:
            print(f"Test exceeded {timeout_seconds}s: {node}")
            fname = os.path.join("artifacts", f"slow_{safe_name(node)}.log")
            with open(fname, "w") as f:
                f.write(out)
            print(f"Saved output to {fname}. Stopping to investigate.")
            sys.exit(2)

    print("All tests completed under timeout.")
    sys.exit(0)


if __name__ == '__main__':
    main()
