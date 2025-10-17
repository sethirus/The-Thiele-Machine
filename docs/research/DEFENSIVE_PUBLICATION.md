---
Thiele Machine — Defensive Publication (Enabling Disclosure)
====================================

Date: October 11, 2025

Author: Devon Thiele

Purpose
-------
This defensive publication provides a complete, enabling disclosure of the
Thiele Machine: its formal model, executable reference implementations (VM,
receipts, proof replay), mechanized Coq proofs, hardware reference (Verilog),
and the experimental data that validates the flagship claims. The goal is to
create robust, citable prior art that prevents patents on the disclosed
methods, while enabling independent reproduction by a skilled practitioner.

Scope and Intended Audience
---------------------------
This disclosure is intentionally deep and implementation-oriented. It is
targeted at engineers and researchers with expertise in formal methods,
SMT solving, hardware design (Verilog/FPGA), and reproducible research. The
content is enabling: enough detail (code, proofs, commands, checksums) is
provided so that an expert can reproduce the key artifacts without undue
experimentation.

High-level Summary of Disclosed Components
------------------------------------------
1. Formal model: Thiele Machine tuple T = (S, Π, A, R, L) with operational
   semantics, partition logic, μ-bit metrology, and mechanized invariants.
2. Reference VM: `thielecpu/` — Python implementation of the instruction set
   (PNEW, PSPLIT, PMERGE, LASSERT, LJOIN, MDLACC, EMIT, XFER) and receipt
   generation.
3. Receipts & Ledger: JSON step receipts, Ed25519 signatures, step-level hashes,
   and replay tooling (`scripts/thiele_verify.py`, `scripts/challenge.py`).
4. Mechanized proofs: Full Coq development in `coq/` with formal statements of
  containment (`Simulation.v`), separation (`Separation.v`), and subsumption
  (`Subsumption.v`). No `Admitted` statements for the flagship proofs; the
  authoritative axiom inventory and validation strategies are published in
  `coq/AXIOM_INVENTORY.md` (use that file as the canonical source of truth).
5. Verilog reference pipeline: `thielecpu/hardware/` contains a cycle-accurate
   RTL (thiele_cpu.v) and testbench (thiele_cpu_tb.v) exercised with Icarus
   Verilog.
6. Documentation & paper: `documents/The_Thiele_Machine.tex` compiled to
   `documents/The_Thiele_Machine.pdf` (included with release).
7. Experiments: Benchmarks and datasets in `scripts/` (Tseitin generators,
   Tsirelson receipts, cosmic witness), and plotting & analysis in
   `attempt.py` and `shape_of_truth_out/`.

Primary Claims (Disclosed and Demonstrated)
-----------------------------------------
- The Thiele Machine formalizes partition-aware computation and μ-bit cost
  accounting.
- Every Turing machine admits an embedding into the Thiele Machine model
  (containment / Simulation).
- For a family of structured SAT instances (Tseitin expanders), sighted
  Thiele programs achieve polynomial-time execution with polynomial μ-bits,
  while blind classical search requires exponential time (Separation).
- Bell inequality violations (Tsirelson bound) arise as a sighted effect;
  the Thiele Machine can construct a rational Tsirelson witness and replay
  its receipts in Coq.
- The Thiele Machine architecture admits hardware embodiments (RTL) with
  audit logging and μ-bit accounting.

Artifacts and Provenance (Checksums, Tags, DOIs)
------------------------------------------------
- Git tag (release): v1.0.3 (commit: `<to be tagged for v1.0.3>`).
- Tarball (v1.0.3): `The-Thiele-Machine-v1.0.3.tar.gz`
  SHA-256: _pending (populate after release packaging)_
- Tarball (v1.0.0): `The-Thiele-Machine-v1.0.0.tar.gz`  
  SHA-256: `883372fd799e98a9fd90f8feb2b3b94d21bf917843745e80351ba52f7cf6d01d`
- Zenodo (all-versions DOI): `10.5281/zenodo.17316437`  
- Zenodo (v1.0.3 DOI): _pending deposition_
- Software Heritage (SWHID): `swh:1:dir:d3894a5c31028e8d0b6d3bcdde9d257148d61e59`
- Compiled PDF (documents/The_Thiele_Machine.pdf) SHA-256: 
  `979d22055cab470b329d435a62a8e03549f17bafc49ae715be95cc32152c93ee`

To assist maintainers in publishing these artifacts to archival services, the
repository contains helper scripts (`scripts/publish_to_zenodo.sh`,
`scripts/publish_to_osf.sh`, and `scripts/publish_archives_helper.sh`). These
scripts require user-provided API tokens and will upload the tarball, the
`CITATION.cff`, `artifacts/MANIFEST.sha256`, and the compiled paper PDF. They
are intentionally interactive and require the repository owner to supply
credentials locally; no credentials are stored in this repository.

Repository Manifest
-------------------
The canonical manifest `artifacts/MANIFEST.sha256` included in the
release lists all core outputs. It is authoritative for auditors and
demonstrates the cryptographic binding between claims and code.

Reproducibility & Step-by-Step Reproduction
------------------------------------------
These commands reproduce the key artifacts. They assume a Unix-like
environment and the prereqs listed below.

System prerequisites
* Python 3.11+ with requirements from `pyproject.toml` (install with
  `pip install -e .` in a venv).
* Z3 (Python `z3-solver` package installed).
* Coq Platform 8.18+ (coqc, coq_makefile on PATH).
* Icarus Verilog (iverilog) for RTL simulation. (Optional: Verilator for
  formal linting.)
* TeX Live (pdflatex) for paper compilation.

Repro steps — code and experiments
1. Run the canonical thesis run and generate receipts:
  ```bash
  python3 demonstrate_isomorphism.py
  ```

2. Run the Bell isomorphism demonstration (derives constants, Tsirelson
   witness, receipts, and Coq replay):
   ```bash
   python demonstrate_isomorphism.py
   ```

3. Verify receipts programmatically (single-file or directory), and optionally replay in Coq:
  ```bash
  python scripts/challenge.py verify receipts
  ./scripts/verify_truth.sh examples/tsirelson_step_receipts.json
  ```

4. Rebuild Coq proofs (canonical subsumption verification):
   ```bash
   cd coq
   ./verify_subsumption.sh
   ```
   Expected outcome: Both pillars (Simulation.v and Separation.v)
   compile and the script prints "VERIFICATION COMPLETE".

5. Generate Tseitin benchmark instances and run blind vs sighted runs:
   ```bash
   python scripts/generate_tseitin_data.py --n 10 --seed 0
   ```

6. Compile the LaTeX paper:
   ```bash
   cd documents
   pdflatex -interaction=nonstopmode -halt-on-error The_Thiele_Machine.tex
   ```

7. Run the Verilog testbench (Icarus Verilog):
   ```bash
   cd thielecpu/hardware
   iverilog -g2005-sv -o thiele_cpu_tb.vvp thiele_cpu_tb.v thiele_cpu.v mmu.v lei.v pee.v mau.v
   vvp thiele_cpu_tb.vvp
   ```

Verification outputs and expected signals
----------------------------------------
- Coq: Output lines contain "Coq proof obligations discharged" and the
  verify scripts print success messages.
- Receipts: JSON receipts exist in `receipts/` and `examples/` and are
  verifiable with `scripts/challenge.py`.
- Verilog: The testbench prints time, PC, status, and error codes and
  ends with "Test completed!" (see test logs produced by vvp).
- Paper: `documents/The_Thiele_Machine.pdf` compiles without fatal errors.

Detailed Enabling Disclosure (Implementation Details)
-----------------------------------------------------
Below are the essential mechanical details that remove ambiguities for a
skilled practitioner.

1) VM & Receipts
-----------------
- Instruction set: PNEW, PSPLIT, PMERGE, LASSERT, LJOIN, MDLACC, EMIT, XFER
- Receipt format: each receipt is a JSON object with fields (step, instruction, pre_state, post_state, observation, pre_state_hash, post_state_hash, signature). See `thielecpu/receipts.py` and `scripts/receipt_schema.py` for canonical schema.
- Signatures: Ed25519 signatures using a generated kernel keypair (`scripts/generate_kernel_keys.py`); `thielecpu/receipts.py` contains sign/verify helpers and environment-variable overrides.

2) μ-bit metrology
------------------
- MDL proxy: zlib or zlib-like compression is used as a practical MDL proxy; `thielecpu/mdl.py` contains the implementation and parameters (prefix-free encoding, µ-spec v1.0).
- Canonical encoding: receipts, SMT queries, and certificate blobs are serialized using stable JSON with sorted keys (`_canonical_json` in receipts module) to guarantee reproducible hashes.

3) Proof replay
---------------
- Coq replay expects receipts to match the canonical schema; `scripts/generate_tsirelson_receipts.py` emits the canonical trace.
- `scripts/verify_truth.sh` pipes JSON receipts into Coq replay helpers and reports "Coq proof obligations discharged" when successful.

4) Hardware semantics
---------------------
- The Verilog RTL models the same instruction semantics as the Python VM (see `thielecpu/hardware/thiele_cpu.v` and helpers). CSR addresses, opcodes, and μ-bit accounting are mirrored in both implementations.
- Testbench (`thiele_cpu_tb.v`) seeds instruction memory with canonical programs from `examples/` and asserts expected status codes; its output is a human-readable trace used as additional prior art.

Legal and Licensing Notes
-------------------------
- License: Apache License, Version 2.0. This release includes a patent
  grant and defensive termination clause; see `LICENSE` and `PATENT-PLEDGE.md`.
- Attribution and citation: Please cite the Zenodo DOI for v1.0.3 when
  referencing this release (CITATION.cff included in repository).

Security and Responsible Use
---------------------------
This technology can be used to perform advanced cryptanalysis, including
attacks on RSA-like schemes. The repository includes explicit warnings and a
responsible use policy. Use is restricted to defensive security research,
formal verification, and academic study. The maintainers require responsible
disclosure of discovered vulnerabilities.

Prior Art Strategy
------------------
This document, the GitHub release, the Zenodo DOI, the Software Heritage
archive, and the attached artifacts form a multi-pronged prior art strategy:
1. The repository and release publicly disclose the invention with code,
   proofs, and hardware descriptions.
2. Zenodo DOI and SWHID create persistent, citable records with timestamps.
3. The defensive publication contains technical details sufficient to
   prevent later patents on the same or obvious variants.

Limitations and Disclaimers
---------------------------
- The Thiele Machine is a formal model; practical, large-scale hardware
  implementations require engineering beyond this disclosure for performance
  and security hardening.
- Some theoretical claims rely on widely believed complexity-theory axioms
  (documented in `coq/AXIOM_INVENTORY.md`). These are explicitly stated in
  the Coq development and are part of the documented assumptions.

Contact and Support
-------------------
If you reproduce these artifacts or use them for research, please open an
issue on the repository describing your work. For coordinated security
research or access to confidential hardware blueprints, email
thethielemachine@gmail.com.

Appendix: Quick reference commands
---------------------------------
```sh
# Run core demos and generate artifacts
python attempt.py
python demonstrate_isomorphism.py

# Verify receipts
python scripts/challenge.py verify receipts
./scripts/verify_truth.sh examples/tsirelson_step_receipts.json

# Rebuild Coq proofs
cd coq
./verify_subsumption.sh

# Compile LaTeX
cd documents
pdflatex The_Thiele_Machine.tex

# RTL simulation (Icarus Verilog)
cd thielecpu/hardware
iverilog -g2005-sv -o thiele_cpu_tb.vvp thiele_cpu_tb.v thiele_cpu.v mmu.v lei.v pee.v mau.v
vvp thiele_cpu_tb.vvp
```

---
This defensive publication is written to be maximizing enablement while
preserving responsible-use guardrails. It is intended as an authoritative
technical record for the Thiele Machine and to block patent claims on the
expressed inventions and routine variations thereof.