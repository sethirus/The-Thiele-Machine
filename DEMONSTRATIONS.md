# Thiele Machine Demonstrations

This document provides an overview of all demonstrations in the Thiele Machine repository, clearly distinguishing between those that use **real mathematical solvers** (Z3, PySAT, etc.) and those that use **mock implementations** for illustrative purposes.

## Real Solver Demonstrations

These demonstrations use actual constraint solvers and SAT solvers to perform real computations:

### priced_sight_demo.py
- **Purpose**: Main computational priced sight demonstration interface
- **Solver Usage**: Uses PricedSightRunner with real Z3 integration and PySAT baseline comparisons
- **Key Components**:
  - Instance generation via PricedSightRunner
  - Model discovery with real Z3 solving
  - Proof emission with cryptographic receipts
  - Baseline solver testing with external SAT solvers (glucose4, minisat22, etc.)
- **Real Solvers**: Z3 (SMT), PySAT with external SAT solvers
- **Location**: `demos/priced_sight_demo.py`

### priced_sight_runner.py
- **Purpose**: Core priced sight demonstration runner
- **Solver Usage**: Implements real PySAT solver testing with timeout handling
- **Key Components**:
  - Blind baseline comparison with cadical/glucose4/minisat22/lingeling
  - Threading-based timeout handling for solver comparisons
  - Real solver performance measurement
- **Real Solvers**: PySAT with external SAT solvers (CaDiCaL, Glucose, MiniSat, Lingeling)
- **Location**: `scripts/priced_sight_runner.py`

### models/implementations.py
- **Purpose**: Concrete model implementations with real Z3 solving
- **Solver Usage**: GF2LinearModel and SymmetryModel use real Z3 solvers
- **Key Components**:
  - Z3 Solver creation and constraint addition
  - Real satisfiability checking with actual results
  - No mock random success - genuine constraint solving
- **Real Solvers**: Z3 SMT solver
- **Location**: `models/implementations.py`

### tensorflow_heist_demo.py
- **Purpose**: Automated neural network weight recovery using constraint solving
- **Solver Usage**: Uses Z3 to recover exact neural network weights from evidence
- **Key Components**:
  - Browser automation to extract visual weight representations
  - Z3 constraint solving to recover numerical weights
  - Verification of recovered weights against training data
- **Real Solvers**: Z3 SMT solver
- **Location**: `demos/tensorflow_heist_demo/tensorflow_heist_complete.py`

### cerberus_demo.py
- **Purpose**: Cryptographic hash collision demonstration
- **Solver Usage**: Uses Z3 to find hash collisions symbolically
- **Key Components**:
  - Symbolic hash function modeling
  - Z3 constraint solving for collision finding
  - Cryptographic receipt generation
- **Real Solvers**: Z3 SMT solver
- **Location**: `demos/cerberus_demo/cerberus_demo.py`

### tsp_optimizer.py
- **Purpose**: Traveling Salesman Problem optimization
- **Solver Usage**: Uses Z3 for TSP constraint solving
- **Key Components**:
  - Z3-based binary search for optimal TSP tours
  - Subprocess isolation for Z3 execution
  - Real constraint solving with timeouts
- **Real Solvers**: Z3 SMT solver
- **Location**: `scripts/tsp_optimizer.py`

### proof_system.py
- **Purpose**: SAT solving with proof generation
- **Solver Usage**: Uses PySAT solvers for real SAT solving
- **Key Components**:
  - PySAT solver integration
  - Proof logging and verification
  - External SAT solver support
- **Real Solvers**: PySAT with external SAT solvers
- **Location**: `scripts/proof_system.py`

## Mock Solver Demonstrations

These demonstrations use simplified or mock implementations to illustrate concepts without performing actual constraint solving:

### structure_discovery_demo.py
- **Purpose**: No-hints structure discovery benchmark
- **Solver Usage**: Mock MDL scoring and simplified solving logic
- **Key Components**:
  - Heuristic-based model scoring (not real constraint solving)
  - Simplified GF(2), modular, and symmetry solving
  - No actual Z3 or SAT solver calls
- **Mock Elements**: MDL scoring heuristics, simplified solvers
- **Location**: `demos/structure_discovery_demo.py`

### rsa_partition_demo.py
- **Purpose**: Partition-based RSA factorization demonstration
- **Solver Usage**: Trial division (no constraint solvers)
- **Key Components**:
  - Classical trial division approach
  - No SMT or SAT solving
  - Illustrative partitioning without real constraints
- **Mock Elements**: No constraint solving, classical factorization
- **Location**: `demos/rsa_partition_demo.py`

### skeleton_key_demo.py
- **Purpose**: SHA-256 pre-image search demonstration
- **Solver Usage**: Brute-force search (no constraint solvers)
- **Key Components**:
  - Exhaustive search over small alphabet
  - No symbolic constraint solving
  - Deterministic small-space search
- **Mock Elements**: Brute force instead of constraint solving
- **Location**: `demos/skeleton_key_demo/skeleton_key_demo.py`

### universe_demo
- **Purpose**: Physical law consistency verification
- **Solver Usage**: Loads SMT2 axioms but doesn't solve them
- **Key Components**:
  - SMT2 file loading and parsing
  - No actual constraint solving execution
  - Illustrative axiom loading
- **Mock Elements**: No solver execution, just axiom loading
- **Location**: `demos/universe_demo/the_universe_as_a_thiele_machine.py`

### paradox_demo
- **Purpose**: Logical paradox demonstration via partitioning
- **Solver Usage**: Thiele VM PDISCOVER instruction (internal logic)
- **Key Components**:
  - VM-based paradox discovery
  - No external constraint solvers
  - Internal partition logic
- **Mock Elements**: VM-internal solving, no external solvers
- **Location**: `demos/paradox_demo/paradox_demo.py`

### chsh_mu_bits_law.py
- **Purpose**: Bell inequality µ-bits law derivation
- **Solver Usage**: Synthetic data and simple calculations
- **Key Components**:
  - Pre-computed Bell datasets
  - Deterministic strategy enumeration
  - No constraint solving
- **Mock Elements**: Synthetic data, no real Bell experiments
- **Location**: `demos/chsh_mu_bits_law.py`

### ablation_studies.py
- **Purpose**: Structure discovery ablation studies
- **Solver Usage**: Mock implementations and subprocess SAT calls
- **Key Components**:
  - Simplified model scoring
  - External SAT solver subprocess calls (not integrated)
  - Mock solving logic
- **Mock Elements**: Heuristic scoring, external subprocess calls
- **Location**: `demos/ablation_studies.py`

## Installation Requirements for Real Solvers

To run demonstrations with real solvers, install the following:

### Z3 Solver
```bash
pip install z3-solver
```
- Required for: priced_sight_demo.py, models/implementations.py, tensorflow_heist_demo.py, cerberus_demo.py, tsp_optimizer.py
- Version: 4.15.1 or later
- Homepage: https://github.com/Z3Prover/z3

### PySAT with External SAT Solvers
```bash
pip install python-sat
```

External SAT solvers (install separately):

#### CaDiCaL
```bash
# Option 1: pip install (recommended)
pip install cadical

# Option 2: From source
git clone https://github.com/arminbiere/cadical.git
cd cadical
./configure
make
sudo make install
```
- Homepage: https://github.com/arminbiere/cadical
- Used by: priced_sight_runner.py, proof_system.py

#### Glucose
```bash
# Option 1: pip install
pip install glucose

# Option 2: From source
git clone https://github.com/audemard/glucose.git
cd glucose/simp
make
# Copy binary to PATH or specify path in PySAT
```
- Homepage: https://github.com/audemard/glucose
- Used by: priced_sight_runner.py, proof_system.py

#### MiniSat
```bash
# Usually included with PySAT, but for standalone:
git clone https://github.com/niklasso/minisat.git
cd minisat
make
# Copy binary to PATH
```
- Homepage: https://github.com/niklasso/minisat
- Used by: priced_sight_runner.py, proof_system.py

#### Lingeling
```bash
git clone https://github.com/arminbiere/lingeling.git
cd lingeling
./configure
make
# Copy binary to PATH
```
- Homepage: https://github.com/arminbiere/lingeling
- Used by: priced_sight_runner.py, proof_system.py

### Verification of Installation
After installing solvers, verify they work:
```bash
python -c "import z3; print('Z3 version:', z3.get_version_string())"
python -c "from pysat.solvers import Glucose4; print('PySAT with Glucose4: OK')"
```

### Troubleshooting
- **Z3 import errors**: Ensure Python 3.11+ and correct virtual environment
- **PySAT solver not found**: Ensure external solver binaries are in PATH
- **Permission errors**: May need `sudo` for system-wide solver installation
- **Windows**: Use WSL or ensure binaries are in system PATH

## Solver Comparison Table

| Demonstration | Solver Type | Real vs Mock | Purpose | Performance | Use Case |
|---------------|-------------|--------------|---------|-------------|----------|
| priced_sight_demo.py | Z3 + PySAT | **Real** | Computational priced sight with model discovery | Variable (depends on instance size) | Production computational experiments |
| priced_sight_runner.py | PySAT | **Real** | SAT solver baseline comparisons | Fast (seconds) | Performance benchmarking |
| models/implementations.py | Z3 | **Real** | GF(2) linear and symmetry constraint solving | Fast (milliseconds) | Core constraint solving |
| tensorflow_heist_demo.py | Z3 | **Real** | Neural network weight recovery | Variable (minutes) | Cryptanalysis demonstrations |
| cerberus_demo.py | Z3 | **Real** | Hash collision finding | Fast (seconds) | Cryptographic demonstrations |
| tsp_optimizer.py | Z3 | **Real** | TSP optimization | Variable (seconds to minutes) | Optimization problems |
| proof_system.py | PySAT | **Real** | SAT solving with proofs | Fast (seconds) | Proof generation |
| structure_discovery_demo.py | Mock heuristics | **Mock** | Structure discovery illustration | Instant | Educational concepts |
| rsa_partition_demo.py | Trial division | **Mock** | RSA factoring concepts | Fast (seconds) | Pedagogical examples |
| skeleton_key_demo.py | Brute force | **Mock** | Pre-image search | Fast (seconds) | Small-scale demonstrations |
| universe_demo | Axiom loading | **Mock** | Consistency checking concepts | Instant | Philosophical illustrations |
| paradox_demo | VM internal | **Mock** | Partition logic | Fast (seconds) | Logic demonstrations |
| chsh_mu_bits_law.py | Synthetic data | **Mock** | Bell inequality analysis | Instant | Theoretical derivations |
| ablation_studies.py | Mock + subprocess | **Mock** | Ablation studies | Fast (seconds) | Comparative analysis |

## Key Differences: Real vs Mock Solvers

### Real Solver Characteristics
- **Mathematical Rigor**: Perform actual constraint solving with provable correctness
- **Scalability**: Can handle large, complex problems
- **Cryptographic Receipts**: Generate verifiable proofs of computation
- **Performance Variation**: Execution time depends on problem complexity
- **External Dependencies**: Require solver installations

### Mock Solver Characteristics
- **Educational Value**: Illustrate concepts without complex dependencies
- **Deterministic**: Fast, predictable execution for demonstrations
- **Simplified Logic**: Use heuristics or approximations instead of full solving
- **No External Tools**: Self-contained Python implementations
- **Concept Focus**: Emphasize algorithmic ideas over computational results

## Running Demonstrations

### Real Solver Demos
```bash
# Priced sight with real Z3 and PySAT
python demos/priced_sight_demo.py

# Neural network weight recovery
python demos/tensorflow_heist_demo/tensorflow_heist_complete.py

# Hash collision finding
python demos/cerberus_demo/cerberus_demo.py
```

### Mock Solver Demos
```bash
# Structure discovery (heuristic-based)
python demos/structure_discovery_demo.py

# RSA partitioning (trial division)
python demos/rsa_partition_demo.py --demo

# Bell inequality analysis (synthetic)
python demos/chsh_mu_bits_law.py
```

## Verification and Testing

All demonstrations produce cryptographic receipts. Verify with:
```bash
python scripts/challenge.py verify receipts
```

For Coq verification of formal properties:
```bash
cd coq
./verify_subsumption.sh
```

## Notes

- **Real solver demonstrations** perform actual mathematical computations and can take significant time
- **Mock solver demonstrations** illustrate concepts quickly but don't perform real constraint solving
- All demonstrations are designed to be educational and showcase different aspects of the Thiele Machine paradigm
- Real solver demonstrations require the corresponding solver libraries to be installed</content>
<parameter name="filePath">c:\Users\tbagt\TheThieleMachine\demos\DEMONSTRATIONS.md