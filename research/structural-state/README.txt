STRUCTURAL-STATE RESEARCH — HANDOFF INDEX

Start with the repository-root CLAUDE_HANDOFF.txt. All work is on book-design.

Current abstract-model work:
  partition-costs/Read-first.txt      Latest memory/time study.
  partition-costs/Result.txt          Proofs and attributed complexity bounds.
  partition-preservation/Result.txt   Structural quotient and policy proofs.
  Partition-research-review.txt       Combined plaintext review.
  abstract-direction.txt             Scope and definition compatibility notes.

Earlier completed work, retained for reference:
  machine-preservation/              Concrete-machine semantic preservation;
                                     RetentionBound.v checks its Theorem 3 (Coq, optional).
  interval-succinct/                 Succinct interval freshness component.
  followup/                         Earlier bounds and interval models.
  Results.txt, monitors.py, verify.py Baseline freshness study.

Unverified, excluded from completed results:
  grouped-masks/                     Read UNVERIFIED.txt before touching.

Run all seven completed suites from repository root:
  python3 research/structural-state/run_checks.py

HANDOFF-VERIFICATION.json and handoff-*.txt record the fresh packaging checks.
Other verification records are preserved alongside their studies. Timing
samples may differ on another machine. Source fingerprints are checkout-relative.
ARCHIVE-INVENTORY.json records imported files and deliberately omitted source
downloads, images and duplicate archives. None of these notes establishes
novelty merely by being written, executable, or mathematically consistent.
