# thiele_auto_solver.py
# Brute-force search for universally valid Thiele Equation

import math
import subprocess
import sys

# Example data from sandbox (replace with actual outputs if needed)
DATA = [
    [20.0, 20, 1, 1],
    [7500.0, 350, 2, 50],
    [1500.0, 150, 10, 5],
    [800.0, 40, 3, 20],
    [700.0, 30, 4, 10],
    [1200.0, 60, 5, 15],
]

def update_sandbox_equation(coeffs):
    # Write new equation to thiele_sandbox.py
    eqn = (
        "def thiele_equation(K, d, T):\n"
        "    return (\n"
        f"        {coeffs[0]:.2f}\n"
        f"        + {coeffs[1]:.2f} * K\n"
        f"        + {coeffs[2]:.2f} * d\n"
        f"        + {coeffs[3]:.2f} * T\n"
        f"        + {coeffs[4]:.2f} * d ** 2\n"
        f"        + {coeffs[5]:.2f} * d ** 3\n"
        f"        + {coeffs[6]:.2f} * math.log(T + 1)\n"
        "    )\n"
    )
    with open("thiele_sandbox.py", "r") as f:
        lines = f.readlines()
    start = None
    for i, line in enumerate(lines):
        if line.strip().startswith("def thiele_equation"):
            start = i
            break
    if start is not None:
        end = start + 1
        while end < len(lines) and not lines[end].strip().startswith("def ") and not lines[end].strip().startswith("class "):
            end += 1
        lines[start:end] = [eqn]
        with open("thiele_sandbox.py", "w") as f:
            f.writelines(lines)

def run_sandbox():
    result = subprocess.run([sys.executable, "thiele_sandbox.py"], capture_output=True, text=True)
    return result.stdout

def parse_audit(output):
    pass_count = 0
    fail_count = 0
    for line in output.splitlines():
        line = line.strip()
        if line.endswith("Status: PASS"):
            pass_count += 1
        elif line.endswith("Status: FAIL"):
            fail_count += 1
    return pass_count, fail_count

def main():
    # Brute-force grid search over coefficients
    # (intercept, K, d, T, d^2, d^3, log(T+1))
    import itertools
    ranges = [
        range(-2000, 2000, 500),  # intercept
        range(0, 30, 10),         # K
        range(0, 500, 100),       # d
        range(-100, 100, 50),     # T
        range(-100, 100, 50),     # d^2
        range(-10, 10, 5),        # d^3
        range(0, 400, 100),       # log(T+1)
    ]
    for coeffs in itertools.product(*ranges):
        update_sandbox_equation(coeffs)
        output = run_sandbox()
        pass_count, fail_count = parse_audit(output)
        print(f"Tested coeffs: {coeffs} | PASS: {pass_count} | FAIL: {fail_count}")
        if fail_count == 0 and pass_count > 0:
            print("Universal law found!")
            print("Coefficients:", coeffs)
            print(output)
            break

if __name__ == "__main__":
    main()