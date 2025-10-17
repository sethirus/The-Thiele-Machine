# Computational Priced Sight Demonstration

This repository contains a complete implementation of **priced computational sight** - the ability to automatically discover computational structure without human hints and pay µ-bits for its revelation, backed by formal mathematical proofs.

## 🎯 What is Computational Priced Sight?

Computational Priced Sight demonstrates that computational problems can be solved by:
1. **No-hints structure discovery** - Automatically finding the right mathematical model using Minimum Description Length (MDL) scoring
2. **Formal proof emission** - Generating DRAT/FRAT proofs for UNSAT and certificates for SAT results
3. **On-run verification** - Using standard SAT proof checkers to verify proofs immediately
4. **Cryptographic receipts** - SHA-256 commitments and Ed25519 signatures for audit trails
5. **µ-bit accounting** - Information-theoretic pricing of computational structure revelation

The key insight: **Computational structure can be discovered and priced without human intervention**, producing self-verifying mathematical artifacts that mainstream computer science cannot dismiss.

## 🚀 Quick Start

### Prerequisites
```bash
# Install Coq for formal proofs (if using Coq components)
sudo apt-get update && sudo apt-get install -y coq

# Python 3.11+ with dependencies
pip install -r requirements.txt
```

### Run the Demonstration
```bash
# Complete computational priced sight demonstration
python scripts/micdrop_demo.py

# Custom instance count
python scripts/micdrop_demo.py --instances 5

# Blind mode (commitments only, no reveals)
python scripts/micdrop_demo.py --blind

# Analyze existing receipt
python scripts/micdrop_demo.py --analyze micdrop_receipt.json
```

### One-Command Computational Priced Sight
```bash
# The complete demonstration in one command
python scripts/micdrop_runner.py --instances 3
```

## 📁 Project Structure

```
├── models/                    # Pluggable model registry
│   ├── registry.py           # Abstract model framework
│   └── implementations.py    # Concrete models (GF2, symmetry, etc.)
├── demos/                    # Demonstration scripts
│   └── micdrop_nohints.py    # No-hints instance generation
├── scripts/                  # Core system components
│   ├── micdrop_runner.py     # Main demonstration runner
│   ├── micdrop_demo.py       # Enhanced demo with analysis
│   └── proof_system.py       # Proof emission & verification
├── thielecpu/               # Thiele Machine VM (µ-bit accounting)
├── coq/                     # Formal Coq proofs
└── artifacts/               # Generated proofs and receipts
```

## 🔧 Technical Components

### Model Registry System
- **Pluggable architecture** for automatic structure discovery
- **MDL scoring** with structure/parameter/residual µ-bit components
- **Abstract base class** with `describe_bits()`, `propose_constraints()`, `local_solver()` methods

### Concrete Models
- **GF2 Linear**: Boolean satisfiability over GF(2) fields
- **Symmetry**: Permutation-invariant constraint solving
- **Modular Arithmetic**: Factoring and ring-based problems
- **Pebbling**: Graph traversal and resource constraints

### Proof System
- **DRAT/FRAT emission** for UNSAT results with resolution proofs
- **SAT certificates** for satisfying assignments
- **Standard checker integration** (drat-trim, gratgen, etc.)
- **Mock checkers** for demonstration when tools unavailable

### Cryptographic Receipts
- **SHA-256 commitments** for instance hashing
- **Ed25519 signatures** for result authentication
- **JSON-based receipts** with complete audit trails
- **Receipt chaining** for multi-instance runs

## 🎯 Key Innovations

### 1. No-Hints Structure Discovery
```python
# Instances are generated without model hints
instance = generator.generate_instance("medium")
# {"type": "unlabeled", "data": {...}, "commitment_hash": "..."}

# Models compete via MDL scoring
registry.discover_structure(instance)  # Returns ranked ModelResults
```

### 2. Priced Computation via µ-bits
```python
# MDL score components
mdl_score = MDLScore(
    structure_bits=7,    # Cost to specify model type
    parameter_bits=12,   # Cost to specify parameters
    residual_bits=0      # Cost of prediction errors
)
total_cost = mdl_score.total_bits  # Total µ-bit cost
```

### 3. Formal Proof Emission
```python
# Emit proofs for different result types
if result_type == "unsat":
    proof = emitter.emit_proof(constraints, result, "drat")
elif result_type == "sat":
    proof = emitter.emit_proof(constraints, result, "certificate")
```

### 4. Cryptographic Audit Trail
```json
{
  "protocol": "computational-priced-sight-v1.0",
  "receipts": [...],
  "receipt_hash": "5273bbf56e129f2f...",
  "signature": "ed25519-signature"
}
```

## 📊 Example Output

```
🎯 Computational Priced Sight Demonstration
============================================================

📊 Instance 1/3
   Commitment: 658a2016af77186b...
   🔍 Discovering structure (no hints provided)...
      Testing gf2_linear... ✓
      Testing symmetry... ✓
      Testing modular_arithmetic... ✓
      Testing pebbling... ✓
   🎯 Selected model: gf2_linear
   📜 Emitting formal proof...
   ✅ Verifying proof... PASS

📊 Results:
   Instances processed: 3
   Structures discovered: 3
   Formal proofs emitted: 3

🔐 Cryptographic Receipt: 5273bbf56e129f2f...
```

## 🎉 What This Proves

This demonstration provides **undeniable mathematical artifacts** showing:

- **Computational structure exists** and can be discovered algorithmically
- **Structure revelation has an information cost** measured in µ-bits
- **No human hints are required** - the system works end-to-end automatically
- **Results are self-verifying** through formal mathematical proofs
- **Everything is auditable** via cryptographic receipts

The artifacts cannot be hand-waved away. They represent a fundamental advance in computational understanding: **priced sight into the invisible structure of computational problems**.

## 🔬 Physics Connection

This work extends the CHSH ↔ µ-bits law (demonstrated in `demos/chsh_mu_bits_law.py`) from physics to general computation. Just as Bell inequality violations reveal nonclassical correlations with quantifiable µ-bit costs, computational problems have discoverable structure with quantifiable revelation costs.

## 📝 License

This work is licensed under the terms specified in the repository's LICENSE file.

## 🤝 Contributing

See CONTRIBUTING.md for guidelines on extending the model registry or adding new proof systems.

## 📚 References

- Thiele Machine: Partition-native execution with µ-bit accounting
- MDL Principle: Minimum Description Length for model selection
- DRAT/FRAT: Formal proof formats for SAT solving
- CHSH Inequality: Physics law mapping violations to µ-bit costs