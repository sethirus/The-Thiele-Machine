# Audit status update — 2025-11-07

This note replaces the earlier narrative audit while keeping the historical findings available for reference.

## Previous concerns

- Partition experiments rerun after the audit failed three of the four preregistered criteria, leaving the blind-vs-sighted separation inconclusive.
- The fixed-point executable (`the_final_proof.py`) did not realise its claimed self-consuming proof.
- Operation Cosmic Witness relied on a fragile single-feature threshold and implied cosmological weight it did not earn.
- The Ed25519 kernel signing key was committed in plaintext, so signatures could not be trusted as authentic.

## Current status

- **Partition experiments:** `scripts/run_partition_ephemeral.py` now drives the reruns and exits successfully only when all four preregistered criteria pass. It stages outputs under `/tmp`, leaving no artefacts in the repository.
- **Key handling:** The bundled private key has been purged from history. Signing helpers generate local keys on demand, and signatures from before commit 2f783ee remain flagged as demo-only.
- **Cosmic Witness:** The documentation explicitly frames it as a toy CHSH-style classifier over 16 scalar CMB temperatures, with receipts certifying internal consistency rather than astrophysical insight.
- **Final proof:** `the_final_proof.py` is documented as an impossibility witness that records the barrier instead of producing a completed fixed-point proof; delivering that proof is future work.
