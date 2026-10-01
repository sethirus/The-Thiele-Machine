# Part 4, round 4 freeze: substantive physics boundary

Date: 2026-10-01

Rounds 1 through 3 remain unedited. The Part-boundary Inquisitor rejected the
round-3 item 4.4 target as a tautological restatement of `landauer_heat` and
correctly required representation invariance. It also exposed that the 4.3
scale witness was not tied to the VM state. Round 4 therefore strengthens,
rather than weakens, the frozen target:

- 4.3 now defines energy scales directly on `VMState.vm_mu` and compares them
  on every state with μ equal to one.
- 4.4 is the full finite-state permanent-flip heat bound, with the
  `landauer_heat` premise explicit.
- The proof file must establish entropy invariance under permutation of the
  finite state enumeration.

- `part4-pricing-physics-target.v.sha256`:
  `a5a0d77262f25aab6fcf2f4d379da3df917831d0566fe8d50dded9fbece2c29b`
- All source hashes, predictions, success and failure criteria, and literature
  baselines not superseded above remain as frozen in round 1.

Predicted outcomes remain 4.1 PROVED BUT KNOWN, 4.2 PARTIAL, 4.3 PARTIAL, and
4.4 PROVED BUT KNOWN. Success now also requires the strengthened statements to
pass Inquisitor without a scope suppression.
