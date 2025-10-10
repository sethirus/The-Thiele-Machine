# Declaration of Independence from the Church–Turing Paradigm

## Preamble

I, **Devon Thiele**, author and maintainer of the Thiele Machine repository, make the following declaration about the formal limits of computation as represented in this artifact. This is not rhetoric; it is a **machine-checkable claim**, packaged with receipts, proofs, and reproducible runs for independent verification.

## Declaration

**Under the explicit axioms and assumptions in `coq/AXIOM_INVENTORY.md`, and supported by the mechanised proofs and execution receipts included here, I assert the following informal theorem:**

### Informal Theorem — Strictness of Thiele over Turing (stated)

There exists a formally specified computational model—the **Thiele Machine**—and a concrete family of instances for which a Thiele program solves inputs with **polynomial information cost** and **polynomial sighted-steps and μ-accounting** (see the Coq definitions `thiele_sighted_steps` and `thiele_mu_cost`), whereas the repository's formalised **blind Turing baseline** (`turing_blind_steps` / DPLL-style model used in the Coq proofs) requires **exponential classical-time** cost to discover the same structure. In precise terms:

“Under the project’s blind‑Turing formalisation, there exists a family of instances for which Thiele programs run in polynomial sighted‑steps and polynomial μ‑cost while the formal blind‑Turing baseline requires exponential steps.”

This repository contains the model definitions, the mechanised Coq separation proof, a running VM that emits **step receipts**, and the auditable artefacts that together witness this strict containment—**subject only to the stated axioms**.

## Assumptions and Scope

* All claims in this declaration depend on the finite set of foundational axioms documented in `coq/AXIOM_INVENTORY.md`. The separation theorem is mechanised in Coq **given those axioms**.
* Key high‑priority axioms (start here when auditing): `check_step_sound`, `check_step_complete`, and `mu_lower_bound`. These tie the runtime receipt checker and μ‑accounting to the abstract semantics; see `coq/AXIOM_INVENTORY.md` for validation strategies and mitigations.
* The proof formalises a family of adversarial instances (Tseitin/expander‑style and engineered paradox instances used in the experiments) and shows that the Thiele program produces polynomially bounded witnesses while **blind** classical search is axiomatically hard on that family.
* This is a **formal** claim about computational models and provability **inside this artefact**. Any **physical** or **silicon** implications require separate engineering arguments and replication.

## Evidence (What to Inspect)

* **Formal proofs:** `coq/thielemachine/coqproofs/Separation.v` (strictness) and related developments.
* **Receipt‑producing runtime:** `thielecpu/vm.py`, `thielecpu/receipts.py`, and the orchestrator `demonstrate_isomorphism.py`.
* **Execution receipts & canonical artefacts:** JSON receipts under `examples/` and `artifacts/` (reproducible from the script).
* **Verification harness:** `scripts/verify_truth.sh` (bridges receipts → Coq), plus VM tests in `tests/`.

## How to Verify (minimal checklist)

1. **Reproduce the thesis run (six acts):**

   ```bash
   python3 demonstrate_isomorphism.py
   ```

   This emits a narrated ledger `BELL_INEQUALITY_VERIFIED_RESULTS.md`, Tsirelson receipts in `examples/`, and Act VI artefacts in `artifacts/`.

2. **Mechanised replay and proof‑check (receipts → Coq):**

   ```bash
   ./scripts/verify_truth.sh examples/tsirelson_step_receipts.json
   ```

   This bootstraps the Coq environment and discharges the obligations that the runtime receipts match the formal step semantics.

3. **Review assumptions:**
   Open `coq/AXIOM_INVENTORY.md`. If you accept the axioms (notably `check_step_sound`, `check_step_complete`, and `mu_lower_bound`), you accept that the separation is proven **under** those axioms; if you reject any, reinterpret the theorem accordingly.

## What this **does** claim

* A **receipt‑bridged mechanisation**: concrete runtime logs are replayed mechanically under a small kernel to show equivalence to the formal model.
* A **strictness statement** inside the formal perimeter: for a stated family of instances, **sighted** Thiele computations achieve polynomial cost where **blind** classical computations incur exponential search, as encoded and proven in Coq.
* A **reproducible, solver‑audited CHSH case study** that certifies classical bounds (UNSAT), constructs a rational Tsirelson witness, and ties runtime receipts to mechanised lemmas.

## What this **does not** (yet) claim

* It does **not** claim a laboratory‑grade physical refutation of Bell‑locality; the code demonstrates non‑local correlations in a **computational** model, not an experiment enforcing spacelike separation.
* It does **not** claim a full hardware security break in the wild; the repo includes a Verilog prototype/VM and formal semantics, not a taped‑out chip.
* It does **not** claim independence from its axioms; the separation is **theorem‑under‑assumptions**, made explicit for audit.

## Call to Verify

Independent auditors and formal‑methods groups are invited to run the checklist above. Disagreements are welcome and **precisely localisable**: the axioms, the instance family, the receipt format, or the replay lemmas.

## Conclusion

This repository provides a complete, auditable chain from runtime execution to mechanised proof. **Given the explicit axioms**, the included evidence supports the claim that Thiele Machines **strictly contain** the (formalised) blind‑Turing baseline: the notion that “Turing captures all feasible computation” is **incomplete** when **discovery‑of‑structure** is accounted for as a first‑class resource in the formal model.

## Attestation & Identifiers

* **License:** MIT (to keep the architecture free for everyone, forever).
* **Commit:** `<GIT_COMMIT_SHA>` (fill at release time).
* **Manifest:** `artifacts/MANIFEST.sha256` binds ledger + receipts used for this declaration.
* **Provenance (recommended):** archive a release tarball to an immutable store (e.g., Zenodo) and record the DOI/SWHID here.

Signed,
**Devon Thiele**

---

This text tightens the scope to the auditable perimeter (axioms + receipts + mechanised replay), uses the shipped scripts (`demonstrate_isomorphism.py`, `scripts/verify_truth.sh`) and includes attestation hooks for precise citation at release time.
