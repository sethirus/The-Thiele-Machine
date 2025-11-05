# P=NP Sketch (Philosophical Only - NOT a Rigorous Proof)

> **Status update (October 2025):** The authoritative kernel proof lives in `coq/kernel/`. This README is preserved for the archived `coq/thielemachine` development.
⚠️ **This is a 65-line philosophical sketch, NOT a solution to P vs NP.**

**Critical Issue:** Defines `is_poly_time := True` (all functions polynomial by assumption). Results are **tautologies**, not complexity results.

**What this is:**
- Model observation about bundling certificates into state
- Philosophical commentary on computational architecture

**What this is NOT:**
- ❌ Solution to P vs NP millennium problem
- ❌ Claim that SAT is polynomial-time solvable
- ❌ Rigorous complexity result

**Build:** `make p_equals_np_thiele/proof.vo`

**For real Thiele Machine results:** See `thielemachine/coqproofs/Separation.v` and `attempt.py`
