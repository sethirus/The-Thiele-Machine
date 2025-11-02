# Thiele Example Programs

This directory contains example programs for the Thiele minimal kernel.

## Programs

1. **hello.thiele** - Simple hello world (demonstrated earlier)
2. **fizzbuzz.thiele** - FizzBuzz with conditional logic
3. **factorial.thiele** - Factorial calculator using loops
4. **primes.thiele** - Prime number generator with assertions

## Running

```bash
# First, reconstruct the kernel from receipts
python3 verifier/replay.py bootstrap_receipts

# Run a program
python3 thiele_min.py --run examples/hello.thiele

# With logging
python3 thiele_min.py --run examples/factorial.thiele --log output.json
```

## Receipt Generation

Each program execution can generate its own receipt:

```bash
python3 thiele_min.py --run examples/primes.thiele --log receipts.json
python3 thiele_min.py --verify receipts.json
```

This creates a cryptographic proof of execution.
