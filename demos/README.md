# Thiele Machine Demonstrations

This directory contains all demonstration code organized by purpose and complexity.

## Directory Structure

### `core-examples/` - Basic Thiele Programming

Simple, standalone Thiele programs demonstrating basic language features:

- `hello.thiele` - Classic "Hello, World!" program
- `fizzbuzz.thiele` - FizzBuzz implementation
- `primes.thiele` - Prime number generation
- `factorial.thiele` - Factorial computation
- `demo.thl` - Basic demonstration program

**Start here** if you're new to Thiele programming.

### `research-demos/` - Advanced Research Demonstrations

Complex demonstrations of research concepts:

#### `partition/` - Graph Partitioning and Structure-Aware Solving
- `graph_partition.py` - Graph partition demonstrations
- `xor_tseitin.py` - Tseitin transformation examples
- `at_most_k.py` - At-most-k constraint demonstrations

#### `oracles/` - Oracle Demonstrations
- `pdiscover_pdiscern_demo.py` - Discover/discern oracle usage

#### `architecture/` - System Architecture Demonstrations
- `demonstrate_isomorphism.py` - Category isomorphism demonstrations
- `populate_observatory.py` - Observatory population
- `forge_demo.py` - Empyrean Forge demonstrations
- `arch_sphere_demo.py` - Arch Sphere demonstrations
- `run_autotelic_engine.sh` - Autotelic engine runner
- `run_engine_of_truth.sh` - Engine of Truth runner
- `run_mitosis.sh` - Mitosis demonstration

#### `dialogue/` - Dialogue of the One
- `ask_the_universe.py` - Universe query interface
- `run_final_dialogue.py` - Final dialogue runner
- `demo_dialogue_of_the_one.sh` - Dialogue demonstration

#### `problem-solving/` - Problem-Solving Demonstrations
- `attempt.py` - Problem-solving attempts
- `solve.py` - Problem solver
- `thiele_break.py` - Breaking demonstrations

### `verification-demos/` - Verification and Testing

Demonstrations of verification capabilities:

#### `bell-inequality/` - Bell Inequality Verification
- `bell_inequality_demo.py` - Bell inequality verification demonstrations

#### `riemann-hunt/` - Riemann Hypothesis Experiments
- `hunt_riemann.py` - Basic Riemann hunt
- `hunt_riemann_adaptive.py` - Adaptive Riemann hunt
- `hunt_riemann_massive.py` - Massive-scale Riemann hunt

#### `adversarial/` - Adversarial Testing
- `run_adversarial_test.sh` - Adversarial test runner

## Running Demonstrations

### Core Examples

```bash
# Run a basic Thiele program
python3 -m thielecpu demos/core-examples/hello.thiele

# Generate primes
python3 -m thielecpu demos/core-examples/primes.thiele
```

### Research Demos

```bash
# Run partition demonstration
python3 demos/research-demos/partition/graph_partition.py

# Run architecture demo
python3 demos/research-demos/architecture/demonstrate_isomorphism.py

# Run dialogue
./demos/research-demos/dialogue/demo_dialogue_of_the_one.sh
```

### Verification Demos

```bash
# Run Bell inequality verification
python3 demos/verification-demos/bell-inequality/bell_inequality_demo.py

# Run Riemann hunt
python3 demos/verification-demos/riemann-hunt/hunt_riemann.py
```

## See Also

- [`../examples/README.md`](../examples/README.md) - Additional example programs and test cases
- [`../scripts/README.md`](../scripts/README.md) - Utility and build scripts
- [`../roadmap-enhancements/`](../roadmap-enhancements/) - v1.2 roadmap enhancements (ZK proofs, web demos, etc.)
