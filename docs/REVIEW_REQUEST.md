# Independent Code Review Request

## Overview

The Thiele Machine is a formally verified partition-native computing system with a 3-layer isomorphic implementation (Coq → OCaml extraction → Python VM → Verilog RTL).

I am seeking **free, voluntary peer review** from the formal methods, programming languages, and verification communities.

## What to Review

### Core Claims (Priority Order)

1. **[PROVEN]** Mathematical correctness: Coq proofs compile without admits/axioms
2. **[IMPLEMENTED]** 3-layer isomorphism: Python VM ↔ extracted runner ↔ RTL state equivalence
3. **[PROVEN]** Tsirelson bound derivation: CHSH = 16/5 > 2√2 from no-signaling axioms
4. **[CONJECTURED]** Physical realizability of supra-quantum correlations

### Key Files to Review

**Formal Proofs:**
- [coq/sandboxes/AbstractPartitionCHSH.v](../coq/sandboxes/AbstractPartitionCHSH.v) - CHSH inequality separation
- [coq/thielemachine/coqproofs/TsirelsonBoundBridge.v](../coq/thielemachine/coqproofs/TsirelsonBoundBridge.v) - Bound bridge lemma
- [coq/kernel/VMState.v](../coq/kernel/VMState.v) - State semantics and canonicalization

**Isomorphism Tests:**
- [tests/test_partition_isomorphism_minimal.py](../tests/test_partition_isomorphism_minimal.py) - 100-case randomized campaign
- [tests/test_rtl_compute_isomorphism.py](../tests/test_rtl_compute_isomorphism.py) - RTL alignment
- [tests/test_equivalence_bundle.py](../tests/test_equivalence_bundle.py) - Cross-layer bundle

**Edge Case Tests:**
- [tests/test_partition_edge_cases.py](../tests/test_partition_edge_cases.py) - Partition operation boundaries
- [tests/test_mu_costs.py](../tests/test_mu_costs.py) - μ-conservation and limits

## How to Reproduce

### Prerequisites
```bash
# Coq 8.18.x, OCaml 4.14.x, Python 3.12.x, iverilog 12.x
# All available in dev container: .devcontainer/devcontainer.json
```

### Quick Verification (15 minutes)

```bash
# Clone repository
git clone https://github.com/sethirus/The-Thiele-Machine.git
cd The-Thiele-Machine

# Verify Coq builds clean (no admits/axioms)
make -C coq clean && make -C coq core

# Run Inquisitor strict mode
python scripts/inquisitor.py --strict --build

# Run isomorphism gates
python -m pytest -q tests/test_equivalence_bundle.py \
  tests/test_partition_isomorphism_minimal.py \
  tests/test_rtl_compute_isomorphism.py \
  tests/test_extracted_vm_runner.py \
  tests/test_rtl_mu_charging.py
```

Expected output:
- Coq: **SUCCESS** (warnings OK, no proof failures)
- Inquisitor: **INQUISITOR: OK** (0 HIGH findings)
- Tests: **15 passed in ~120s**

### Deep Dive (1-2 hours)

1. **Read the derivation:**
   - [coq/sandboxes/AbstractPartitionCHSH.v](../coq/sandboxes/AbstractPartitionCHSH.v) lines 1-100 (axioms)
   - Lines 490-546 (16/5 construction)
   - Lines 255-265 (PR-box CHSH = 4 proof)

2. **Trace isomorphism:**
   - Run: `build/extracted_vm_runner data/traces/pnew_simple.txt`
   - Compare JSON output to Python `State.get_state_snapshot()`
   - Check RTL: `iverilog -o thiele_tb thielecpu/hardware/thiele_cpu_tb.v && ./thiele_tb`

3. **Check edge cases:**
   - Run: `pytest -v tests/test_partition_edge_cases.py`
   - Run: `pytest -v tests/test_mu_costs.py::TestMaxModulesLimit`

## Specific Questions

### For Formal Methods Experts
1. Are the no-signaling axioms in [AbstractPartitionCHSH.v](../coq/sandboxes/AbstractPartitionCHSH.v) standard?
2. Is the CHSH = 16/5 derivation (lines 490-546) mathematically sound?
3. Does the proof of `(16/5)² > 8 ⟹ 16/5 > 2√2` (line 546) hold?

### For PL/Verification Experts
1. Is the extracted OCaml runner → Python VM correspondence valid?
2. Do the isomorphism tests cover sufficient cases?
3. Are there missing edge cases in partition operations?

### For Hardware Experts
1. Does the RTL implementation match the Python semantics?
2. Is the μ-charging mechanism correctly implemented in hardware?
3. Are there timing or synthesis issues?

## What I'm NOT Asking

- **Physical validation**: I explicitly label physical claims as [CONJECTURED]
- **Experimental verification**: This is $0 budget verification
- **Production readiness**: This is a research prototype

## How to Provide Feedback

### Option 1: GitHub Issues
Open issues at: https://github.com/sethirus/The-Thiele-Machine/issues

Tag with: `verification`, `review`, `formal-methods`, `hardware`, etc.

### Option 2: Email
Contact: [see CONTACT.txt](../CONTACT.txt)

### Option 3: Pull Request
Fix bugs or improve documentation directly.

## What I'll Do with Feedback

1. **Critical bugs**: Fix immediately and re-verify
2. **Proofs**: Strengthen or downgrade claims
3. **Documentation**: Clarify ambiguities
4. **Credit**: Acknowledge all helpful feedback in CHANGELOG.md

## Expected Review Time

- **Quick scan**: 15-30 minutes (run gates, check Inquisitor)
- **Proof review**: 1-2 hours (CHSH derivation only)
- **Full isomorphism audit**: 4-8 hours (all three layers)
- **Deep skeptic mode**: 16+ hours (attempt to break everything)

## Critical Bug Reports Welcome

If you find any of the following, please open a GitHub issue:

1. Admitted proofs in active Coq tree
2. Axioms in active Coq tree
3. Isomorphism violation (Python ≠ extracted ≠ RTL)
4. μ-conservation violation
5. CHSH bound derivation error

All bug reports will be acknowledged in CHANGELOG.md.

## Current Status

- **Last verified**: 2025-12-19
- **Coq build**: PASSING (warnings present, no failures)
- **Inquisitor**: OK (0 HIGH findings)
- **Isomorphism gates**: 15/15 PASSING
- **Known issues**: Adversarial fuzzing uses simplified harness (not source-of-truth)

## Community Channels

I plan to share this request on:
- [ ] Coq Discourse
- [ ] /r/programminglanguages
- [ ] Hacker News (Show HN)
- [ ] Formal Methods communities

## Timeline

- **Request posted**: 2025-12-19
- **First review deadline**: 2026-01-15 (4 weeks)
- **Incorporate feedback**: 2026-01-31
- **Final verification**: 2026-02-15

## License

All contributions will be under Apache 2.0 (see [LICENSE](../LICENSE)).

## Thank You

I deeply appreciate any time you spend reviewing this work. Even a 15-minute "quick scan" is valuable feedback for improving the verification story.

This is a solo research project with no budget or institutional backing. All feedback helps strengthen the scientific rigor.

---

**Date**: 2025-12-19  
**Version**: 1.0  
**Contact**: See [CONTACT.txt](../CONTACT.txt)  
**Note**: This is a solo project with no funding or institutional affiliation.
