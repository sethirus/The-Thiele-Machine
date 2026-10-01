---
name: v322-closeout-commit-inflight
description: v3.2.2 closeout landed as 42a374ed; receipt recipe, voice rules, hook-speed complaint
metadata:
  node_type: memory
  type: project
  originSessionId: a5c67d8f-1460-46c9-bc1c-722d5b65416d
  modified: 2026-09-24T23:58:29.309Z
---
The v3.2.2 closeout commit landed on work/v3.2.2-review-fixes as 42a374ed (2026-09-25) and is pushed: voice restoration, reviewer scope fixes, receipt runner fixes, recounted numbers (12,335 theorems). What remained after it was only the FPGA routing fix (see [[fpga-module-tensors-congestion]]).

Receipt regeneration recipe that works on this 2-core box: 500-query batches, 1800 s timeout, `--work-dir build/probe/receipt-work`, then delete that work dir (untracked files block the hook). README Proof Hygiene must keep "close under the global context" / "lean only on Coq-stdlib" (regex-pinned by tests/test_proof_hygiene_numbers.py).

Devon's standing instructions: every prose edit by hand in his voice, never scripted replacements (see [[prose-style-no-em-dashes]]); keep an author sentence whenever it is still true, rewrite only overclaims; no intermediate/process docs or leftovers in the repo at the end. He finds the pre-commit hook far too slow; a proportional hook was offered but NOT approved, so do not change the hook without asking.

Related: [[guarded-coq-builds]].
