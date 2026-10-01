---
name: b3-self-interpreter-closed
description: B3 closed 2026-09-14 by VMSelf* self-interpreter; STATUS at 80% (8/10) after B4 Rice closure; next C1/C2 then E
metadata:
  type: project
---
B3 closed 2026-09-14. Files: coq/kernel/foundation/VMSelf{Guest,Program,Correct,Run,Universal,Limitative}.v (registered in coq/_CoqProject). Evidence: artifacts/review_revision/self_interpreter/ (validate.py with time/RSS guards, Contracts.v, validation.json) and SELF_INTERPRETER_REVIEW.md. All of it has since been committed on work/v3.2.2-review-fixes; artifacts/review_revision is now a gitignored local directory.

Key names: U (122 instrs), hb boundary, h_step, self_interpreter_correct/_sound/_complete/_divergence(_live), self_interpreter_malformed, cm2_compile, self_mm2_halting_iff, self_host_synthetic_undecidability.

**Why:** Guest registers in host registers keep values unbounded (packed 64-bit slots cannot be universal).

**How to apply:** B4 next. Build the fixed-point / representability instance on VMSelfRun + VMUnboundedCM2Specialization. Keep STATUS.md "Live progress" rows current. Related: [[guarded-coq-builds]], [[v322-review-fixes-inflight]].

B4 closed 2026-09-14 via the contract's alternative-construction clause: Rice by reduction (VMSelfRice.v, VMSelfRiceUndec.v, MM2ComplementUndec.v; evidence artifacts/review_revision/rice/, RICE_REVIEW.md). No internal recursion theorem; total_run_obstruction explains why Substrate.run cannot be instantiated. The user may reject this interpretation. Trap: importing vendor PCP/FRACTRAN modules turns on implicit arguments and changes notation behaviour; keep those imports in small separate files.
