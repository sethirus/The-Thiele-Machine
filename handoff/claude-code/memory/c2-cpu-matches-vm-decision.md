---
name: c2-cpu-matches-vm-decision
description: Devon chose (2026-09-14) to change the CPU to match vm_apply/kami_step where they diverge on VM-visible state
metadata: 
  node_type: memory
  type: project
  originSessionId: 88c89020-0abf-49a1-8484-4d797efa8d7e
  modified: 2026-09-14T15:20:44.848Z
---

Asked 2026-09-14 during C2. The CPU diverged from vm_apply/kami_step on VM-visible state in ways no admission premise can exclude. Devon chose "Change CPU to match VM":
- remove the logic-gate lock (LASSERT logic_acc XOR 0xCAFEEACE, per-step mstatus rewrite, high_value_locked fault on REVEAL/PDISCOVER/CHSH_TRIAL);
- HALT advances pc;
- PDISCOVER stops writing regs[dst];
- remove the CHSH_TRIAL x=1 mu surcharge and the zero-tensor gate.
Hardware-only counters (info_gain, LASSERT scratch in the rich shadow) get aligned on the kami_step/observation side, not by changing the VM.

**Why:** vm_apply is the substrate of record; kami_step is linked to it by FullEmbedStep, so the VM side cannot move without re-proving the kernel.

**How to apply:** Guards the VM lacks but that yield a specified error (Bianchi, locality, partition overflow, NFI, rich/morph faults) stay as outside-domain outcomes with admission premises. After CPU edits: regenerate BSV/Verilog with BSC 2024.07, update RTL tests and docs, re-audit C3. Related: [[c1c2-scope-decision]], [[guarded-coq-builds]].
