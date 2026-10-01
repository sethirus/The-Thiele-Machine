---
name: lassert-csr-err-decision
description: Devon chose (2026-09-15) that a failing LASSERT sets csr_err := 1 in the VM, like CHSH_LASSERT
metadata:
  type: project
---
Asked 2026-09-15 during C2 LASSERT retirement. step_lassert / vm_apply / kami_step latched vm_err on failure but left csr_err unchanged, while CHSH_LASSERT and every other error path set csr_err := 1; the hardware has no csr_err register (observation derives it from err). Devon chose "VM sets csr_err": change the kernel VM, vm_apply and kami_step so a failing LASSERT also sets csr_err := 1.

**Why:** smallest change that removes the inconsistency; no hardware change.

**How to apply:** kernel edit then re-check embed proofs (EmbedStep, FullEmbedStep, SimulationProof); keep the Python VM consistent; record in C2_DIVERGENCE_LEDGER.md. Related: [[c2-cpu-matches-vm-decision]], [[c2-step-refinement-pipeline]].
