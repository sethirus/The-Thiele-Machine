---
name: compose-label-tensor-decision
description: "Devon 2026-09-15 — CPU stores per-descriptor ';' label count for COMPOSE; CPU MORPH_TENSOR always faults ERR_MORPH_NOT_FOUND"
metadata: 
  node_type: memory
  type: project
  originSessionId: 755fcefc-aad3-49e7-8f51-633700fbe406
  modified: 2026-09-15T02:06:52.597Z
---

Asked 2026-09-15 during C2 morph-family retirement.

1. COMPOSE label: kernel/kami_step label l1 ++ ";" ++ l2; CPU stored no labels (observation ""). Reachable represented labels are ";" repeated k. Devon chose **CPU stores ';' count**: per-descriptor label-count table; COMPOSE commits k1+k2+1, MORPH/MORPH_ID 0; hwb_rich reports ";"^k; capacity premise. No VM change.
2. MORPH_TENSOR: snapshot regions are prefixes `seq 0 size`, so kernel disjointness always fails and kami_step always gives ERR_MORPH_NOT_FOUND (probe lemma `snap_graph_tensor_none`, ~/.cache/thiele-guard/probe/TensorGap.v). Devon chose **CPU always faults**: MORPH_TENSOR latches err with ERR_MORPH_NOT_FOUND, charges cost, advances pc.

3. Revised the same day: the kernel's `empty_coupling_data` label is "empty", so morphisms without a descriptor (MORPH_ID, identity, legacy self-MORPH) have label "empty" and COMPOSE with them yields "empty;...". Devon chose **CPU stores atom count + mask**: per descriptor a 6-bit atom count n and a 32-bit mask (bit i = atom i is "empty"); label = atoms joined by ";". MORPH commits n=1, mask=0; COMPOSE commits n1+n2 and mask1 + (mask2 << n1); a side without a valid descriptor contributes n=1, mask=1; capacity premise n1+n2 <= 32. Supersedes the ';'-count table.

**Why:** consistent with [[c2-cpu-matches-vm-decision]]; C1 forbids erasing labels to manufacture refinement.

**How to apply:** CPU edit in ThieleCPUCore.v, HWB/hwb_rich gain the label table, regenerate the generated proof files and RTL. MORPH (single) keeps the admission premise that the in-memory label is "" and pairs lie in regions. Related: [[lassert-csr-err-decision]], [[c2-step-refinement-pipeline]].
