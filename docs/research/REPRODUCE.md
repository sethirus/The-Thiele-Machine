# Reproducing the Bell Inequality Violation

This guide provides streamlined commands for recreating the Bell-CHSH violation demonstrated by the Thiele Machine project. Choose the path that matches the tooling you have available.

## Option 1: Quick Reproduction (Python Only)

See the numerical witnesses without installing Coq.

**Requirements**

- Python 3.9 or newer

**Steps**

1. Clone the repository:
   ```bash
   git clone https://github.com/sethirus/The-Thiele-Machine.git
   cd The-Thiele-Machine
   ```
2. (Optional) Create and activate a virtual environment.
3. Install the Python package (editable mode is convenient when iterating on the codebase):
   ```bash
   pip install -e .
   ```
4. Run the standalone Python demo:
   ```bash
   python examples/bell_inequality_demo.py
   ```

**Expected Output**

The script prints the classical CHSH bound alongside the PR-box and Tsirelson witnesses, matching the values reproduced in `BELL_INEQUALITY_RESULTS.md`.

---

## Option 2: Full Formal Verification (Coq + Python)

Recreate the end-to-end artifact, including the mechanised Coq proof, deterministic receipts, and Python replay.

**Requirements**

- Python 3.9 or newer
- GNU Make
- Coq 8.18 (or later)

**Steps**

1. Clone the repository and, if desired, set up a Python virtual environment as shown above.
2. Install the Python dependencies as above if you have not already done so:
   ```bash
   pip install -e .
   ```
3. Ensure Coq is available. On Ubuntu 24.04+, install it via apt:
   ```bash
   sudo apt-get update && sudo apt-get install -y coq
   ```
4. Run the master verification script:
   ```bash
   ./verify_bell.sh
   ```

**What the Script Performs**

1. **Formal Proof Check:** Invokes `make -C coq thielemachine/coqproofs/BellInequality.vo` to recompile the mechanised Bell inequality development from scratch.
2. **Receipt Generation:** Calls `scripts/generate_tsirelson_receipts.py` to emit the canonical Tsirelson measurement trace (`examples/tsirelson_step_receipts.json`).
3. **Empirical Demonstration:** Executes `examples/bell_inequality_demo.py` to print the classical, PR-box, and Tsirelson CHSH values.
4. **Receipt Verification:** Runs `scripts/verify_truth.sh` to prove that the generated receipts align with the mechanised witness via the `concrete_receipts_sound` lemma.

**Expected Output**

The script streams the Coq compilation log, the Python witness values, and the receipt verifier status before finishing with a success banner:

```
✅ SUCCESS: Verified Bell inequality artifact
```

Your environment now hosts both the formal proof objects and the empirical receipts demonstrating the Bell-CHSH violation.

---

## Option 3: Bulletproof Docker Reproduction

Recreate the entire artifact inside a sterile container that pins the exact toolchain used for the v1.0.3 release.

**Requirements**

- Docker (or any OCI-compatible runtime)

**Steps**

```bash
git clone https://github.com/sethirus/The-Thiele-Machine.git
cd The-Thiele-Machine
docker build . -t thiele-machine-verification && docker run thiele-machine-verification
```

The build stage provisions Ubuntu 22.04, Coq 8.18.0, Python 3.12, and every system and Python dependency required by
`verify_bell.sh`. When the container finishes, it emits the canonical `✅ SUCCESS` banner, certifying that the proof, receipts,
and demonstrations all re-execute in a pristine environment with a fixed hash.
