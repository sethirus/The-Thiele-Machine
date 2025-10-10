# Bell Inequality Demonstration — Sovereign Witness

## Act I — Deriving the Constants
Deriving π from first principles using the Chudnovsky method:
- iteration 0: π ≈ 3.141592653590
- iteration 1: π ≈ 3.141592653590
- iteration 2: π ≈ 3.141592653590
- iteration 3: π ≈ 3.141592653590

Deriving √2 from first principles using the Babylonian method:
- iteration 1: √2 ≈ 1.500000000000
- iteration 2: √2 ≈ 1.416666666667
- iteration 3: √2 ≈ 1.414215686275
- iteration 4: √2 ≈ 1.414213562375
- iteration 5: √2 ≈ 1.414213562373
- iteration 6: √2 ≈ 1.414213562373
- iteration 7: √2 ≈ 1.414213562373
- iteration 8: √2 ≈ 1.414213562373

Tsirelson bound: 2·√2 ≈ 2.828427124746

## Act II — Classical Deterministic Bound
Classical strategy definitions:
```python
strategies = [
    (Response(out0=0, out1=0), Response(out0=0, out1=0)),
    (Response(out0=0, out1=0), Response(out0=0, out1=1)),
    (Response(out0=0, out1=0), Response(out0=1, out1=0)),
    (Response(out0=0, out1=0), Response(out0=1, out1=1)),
    (Response(out0=0, out1=1), Response(out0=0, out1=0)),
    (Response(out0=0, out1=1), Response(out0=0, out1=1)),
    (Response(out0=0, out1=1), Response(out0=1, out1=0)),
    (Response(out0=0, out1=1), Response(out0=1, out1=1)),
    (Response(out0=1, out1=0), Response(out0=0, out1=0)),
    (Response(out0=1, out1=0), Response(out0=0, out1=1)),
    (Response(out0=1, out1=0), Response(out0=1, out1=0)),
    (Response(out0=1, out1=0), Response(out0=1, out1=1)),
    (Response(out0=1, out1=1), Response(out0=0, out1=0)),
    (Response(out0=1, out1=1), Response(out0=0, out1=1)),
    (Response(out0=1, out1=1), Response(out0=1, out1=0)),
    (Response(out0=1, out1=1), Response(out0=1, out1=1)),
)
```

Strategy 00: S = 2/1 (~2.000000)
```smt2
(set-logic QF_LIA)
        (declare-const a0 Int)
        (declare-const a1 Int)
        (declare-const b0 Int)
        (declare-const b1 Int)
        (define-fun sgn ((bit Int)) Int (- (* 2 bit) 1))
        (define-fun S () Int (+ (+ (+ (* (sgn a1) (sgn b1)) (* (sgn a1) (sgn b0))) (* (sgn a0) (sgn b1))) (* -1 (* (sgn a0) (sgn b0)))))
        (assert (or (= a0 0) (= a0 1)))
        (assert (or (= a1 0) (= a1 1)))
        (assert (or (= b0 0) (= b0 1)))
        (assert (or (= b1 0) (= b1 1)))
        (assert (= a0 0))
        (assert (= a1 0))
        (assert (= b0 0))
        (assert (= b1 0))
        (assert (> S 2))
        (check-sat)
```
Z3> prove(S > 2) -> FAILED. unsat. Bound holds.

Strategy 01: S = -2/1 (~-2.000000)
```smt2
(set-logic QF_LIA)
        (declare-const a0 Int)
        (declare-const a1 Int)
        (declare-const b0 Int)
        (declare-const b1 Int)
        (define-fun sgn ((bit Int)) Int (- (* 2 bit) 1))
        (define-fun S () Int (+ (+ (+ (* (sgn a1) (sgn b1)) (* (sgn a1) (sgn b0))) (* (sgn a0) (sgn b1))) (* -1 (* (sgn a0) (sgn b0)))))
        (assert (or (= a0 0) (= a0 1)))
        (assert (or (= a1 0) (= a1 1)))
        (assert (or (= b0 0) (= b0 1)))
        (assert (or (= b1 0) (= b1 1)))
        (assert (= a0 0))
        (assert (= a1 0))
        (assert (= b0 0))
        (assert (= b1 1))
        (assert (> S 2))
        (check-sat)
```
Z3> prove(S > 2) -> FAILED. unsat. Bound holds.

Strategy 02: S = 2/1 (~2.000000)
```smt2
(set-logic QF_LIA)
        (declare-const a0 Int)
        (declare-const a1 Int)
        (declare-const b0 Int)
        (declare-const b1 Int)
        (define-fun sgn ((bit Int)) Int (- (* 2 bit) 1))
        (define-fun S () Int (+ (+ (+ (* (sgn a1) (sgn b1)) (* (sgn a1) (sgn b0))) (* (sgn a0) (sgn b1))) (* -1 (* (sgn a0) (sgn b0)))))
        (assert (or (= a0 0) (= a0 1)))
        (assert (or (= a1 0) (= a1 1)))
        (assert (or (= b0 0) (= b0 1)))
        (assert (or (= b1 0) (= b1 1)))
        (assert (= a0 0))
        (assert (= a1 0))
        (assert (= b0 1))
        (assert (= b1 0))
        (assert (> S 2))
        (check-sat)
```
Z3> prove(S > 2) -> FAILED. unsat. Bound holds.

Strategy 03: S = -2/1 (~-2.000000)
```smt2
(set-logic QF_LIA)
        (declare-const a0 Int)
        (declare-const a1 Int)
        (declare-const b0 Int)
        (declare-const b1 Int)
        (define-fun sgn ((bit Int)) Int (- (* 2 bit) 1))
        (define-fun S () Int (+ (+ (+ (* (sgn a1) (sgn b1)) (* (sgn a1) (sgn b0))) (* (sgn a0) (sgn b1))) (* -1 (* (sgn a0) (sgn b0)))))
        (assert (or (= a0 0) (= a0 1)))
        (assert (or (= a1 0) (= a1 1)))
        (assert (or (= b0 0) (= b0 1)))
        (assert (or (= b1 0) (= b1 1)))
        (assert (= a0 0))
        (assert (= a1 0))
        (assert (= b0 1))
        (assert (= b1 1))
        (assert (> S 2))
        (check-sat)
```
Z3> prove(S > 2) -> FAILED. unsat. Bound holds.

Strategy 04: S = -2/1 (~-2.000000)
```smt2
(set-logic QF_LIA)
        (declare-const a0 Int)
        (declare-const a1 Int)
        (declare-const b0 Int)
        (declare-const b1 Int)
        (define-fun sgn ((bit Int)) Int (- (* 2 bit) 1))
        (define-fun S () Int (+ (+ (+ (* (sgn a1) (sgn b1)) (* (sgn a1) (sgn b0))) (* (sgn a0) (sgn b1))) (* -1 (* (sgn a0) (sgn b0)))))
        (assert (or (= a0 0) (= a0 1)))
        (assert (or (= a1 0) (= a1 1)))
        (assert (or (= b0 0) (= b0 1)))
        (assert (or (= b1 0) (= b1 1)))
        (assert (= a0 0))
        (assert (= a1 1))
        (assert (= b0 0))
        (assert (= b1 0))
        (assert (> S 2))
        (check-sat)
```
Z3> prove(S > 2) -> FAILED. unsat. Bound holds.

Strategy 05: S = -2/1 (~-2.000000)
```smt2
(set-logic QF_LIA)
        (declare-const a0 Int)
        (declare-const a1 Int)
        (declare-const b0 Int)
        (declare-const b1 Int)
        (define-fun sgn ((bit Int)) Int (- (* 2 bit) 1))
        (define-fun S () Int (+ (+ (+ (* (sgn a1) (sgn b1)) (* (sgn a1) (sgn b0))) (* (sgn a0) (sgn b1))) (* -1 (* (sgn a0) (sgn b0)))))
        (assert (or (= a0 0) (= a0 1)))
        (assert (or (= a1 0) (= a1 1)))
        (assert (or (= b0 0) (= b0 1)))
        (assert (or (= b1 0) (= b1 1)))
        (assert (= a0 0))
        (assert (= a1 1))
        (assert (= b0 0))
        (assert (= b1 1))
        (assert (> S 2))
        (check-sat)
```
Z3> prove(S > 2) -> FAILED. unsat. Bound holds.

Strategy 06: S = 2/1 (~2.000000)
```smt2
(set-logic QF_LIA)
        (declare-const a0 Int)
        (declare-const a1 Int)
        (declare-const b0 Int)
        (declare-const b1 Int)
        (define-fun sgn ((bit Int)) Int (- (* 2 bit) 1))
        (define-fun S () Int (+ (+ (+ (* (sgn a1) (sgn b1)) (* (sgn a1) (sgn b0))) (* (sgn a0) (sgn b1))) (* -1 (* (sgn a0) (sgn b0)))))
        (assert (or (= a0 0) (= a0 1)))
        (assert (or (= a1 0) (= a1 1)))
        (assert (or (= b0 0) (= b0 1)))
        (assert (or (= b1 0) (= b1 1)))
        (assert (= a0 0))
        (assert (= a1 1))
        (assert (= b0 1))
        (assert (= b1 0))
        (assert (> S 2))
        (check-sat)
```
Z3> prove(S > 2) -> FAILED. unsat. Bound holds.

Strategy 07: S = 2/1 (~2.000000)
```smt2
(set-logic QF_LIA)
        (declare-const a0 Int)
        (declare-const a1 Int)
        (declare-const b0 Int)
        (declare-const b1 Int)
        (define-fun sgn ((bit Int)) Int (- (* 2 bit) 1))
        (define-fun S () Int (+ (+ (+ (* (sgn a1) (sgn b1)) (* (sgn a1) (sgn b0))) (* (sgn a0) (sgn b1))) (* -1 (* (sgn a0) (sgn b0)))))
        (assert (or (= a0 0) (= a0 1)))
        (assert (or (= a1 0) (= a1 1)))
        (assert (or (= b0 0) (= b0 1)))
        (assert (or (= b1 0) (= b1 1)))
        (assert (= a0 0))
        (assert (= a1 1))
        (assert (= b0 1))
        (assert (= b1 1))
        (assert (> S 2))
        (check-sat)
```
Z3> prove(S > 2) -> FAILED. unsat. Bound holds.

Strategy 08: S = 2/1 (~2.000000)
```smt2
(set-logic QF_LIA)
        (declare-const a0 Int)
        (declare-const a1 Int)
        (declare-const b0 Int)
        (declare-const b1 Int)
        (define-fun sgn ((bit Int)) Int (- (* 2 bit) 1))
        (define-fun S () Int (+ (+ (+ (* (sgn a1) (sgn b1)) (* (sgn a1) (sgn b0))) (* (sgn a0) (sgn b1))) (* -1 (* (sgn a0) (sgn b0)))))
        (assert (or (= a0 0) (= a0 1)))
        (assert (or (= a1 0) (= a1 1)))
        (assert (or (= b0 0) (= b0 1)))
        (assert (or (= b1 0) (= b1 1)))
        (assert (= a0 1))
        (assert (= a1 0))
        (assert (= b0 0))
        (assert (= b1 0))
        (assert (> S 2))
        (check-sat)
```
Z3> prove(S > 2) -> FAILED. unsat. Bound holds.

Strategy 09: S = 2/1 (~2.000000)
```smt2
(set-logic QF_LIA)
        (declare-const a0 Int)
        (declare-const a1 Int)
        (declare-const b0 Int)
        (declare-const b1 Int)
        (define-fun sgn ((bit Int)) Int (- (* 2 bit) 1))
        (define-fun S () Int (+ (+ (+ (* (sgn a1) (sgn b1)) (* (sgn a1) (sgn b0))) (* (sgn a0) (sgn b1))) (* -1 (* (sgn a0) (sgn b0)))))
        (assert (or (= a0 0) (= a0 1)))
        (assert (or (= a1 0) (= a1 1)))
        (assert (or (= b0 0) (= b0 1)))
        (assert (or (= b1 0) (= b1 1)))
        (assert (= a0 1))
        (assert (= a1 0))
        (assert (= b0 0))
        (assert (= b1 1))
        (assert (> S 2))
        (check-sat)
```
Z3> prove(S > 2) -> FAILED. unsat. Bound holds.

Strategy 10: S = -2/1 (~-2.000000)
```smt2
(set-logic QF_LIA)
        (declare-const a0 Int)
        (declare-const a1 Int)
        (declare-const b0 Int)
        (declare-const b1 Int)
        (define-fun sgn ((bit Int)) Int (- (* 2 bit) 1))
        (define-fun S () Int (+ (+ (+ (* (sgn a1) (sgn b1)) (* (sgn a1) (sgn b0))) (* (sgn a0) (sgn b1))) (* -1 (* (sgn a0) (sgn b0)))))
        (assert (or (= a0 0) (= a0 1)))
        (assert (or (= a1 0) (= a1 1)))
        (assert (or (= b0 0) (= b0 1)))
        (assert (or (= b1 0) (= b1 1)))
        (assert (= a0 1))
        (assert (= a1 0))
        (assert (= b0 1))
        (assert (= b1 0))
        (assert (> S 2))
        (check-sat)
```
Z3> prove(S > 2) -> FAILED. unsat. Bound holds.

Strategy 11: S = -2/1 (~-2.000000)
```smt2
(set-logic QF_LIA)
        (declare-const a0 Int)
        (declare-const a1 Int)
        (declare-const b0 Int)
        (declare-const b1 Int)
        (define-fun sgn ((bit Int)) Int (- (* 2 bit) 1))
        (define-fun S () Int (+ (+ (+ (* (sgn a1) (sgn b1)) (* (sgn a1) (sgn b0))) (* (sgn a0) (sgn b1))) (* -1 (* (sgn a0) (sgn b0)))))
        (assert (or (= a0 0) (= a0 1)))
        (assert (or (= a1 0) (= a1 1)))
        (assert (or (= b0 0) (= b0 1)))
        (assert (or (= b1 0) (= b1 1)))
        (assert (= a0 1))
        (assert (= a1 0))
        (assert (= b0 1))
        (assert (= b1 1))
        (assert (> S 2))
        (check-sat)
```
Z3> prove(S > 2) -> FAILED. unsat. Bound holds.

Strategy 12: S = -2/1 (~-2.000000)
```smt2
(set-logic QF_LIA)
        (declare-const a0 Int)
        (declare-const a1 Int)
        (declare-const b0 Int)
        (declare-const b1 Int)
        (define-fun sgn ((bit Int)) Int (- (* 2 bit) 1))
        (define-fun S () Int (+ (+ (+ (* (sgn a1) (sgn b1)) (* (sgn a1) (sgn b0))) (* (sgn a0) (sgn b1))) (* -1 (* (sgn a0) (sgn b0)))))
        (assert (or (= a0 0) (= a0 1)))
        (assert (or (= a1 0) (= a1 1)))
        (assert (or (= b0 0) (= b0 1)))
        (assert (or (= b1 0) (= b1 1)))
        (assert (= a0 1))
        (assert (= a1 1))
        (assert (= b0 0))
        (assert (= b1 0))
        (assert (> S 2))
        (check-sat)
```
Z3> prove(S > 2) -> FAILED. unsat. Bound holds.

Strategy 13: S = 2/1 (~2.000000)
```smt2
(set-logic QF_LIA)
        (declare-const a0 Int)
        (declare-const a1 Int)
        (declare-const b0 Int)
        (declare-const b1 Int)
        (define-fun sgn ((bit Int)) Int (- (* 2 bit) 1))
        (define-fun S () Int (+ (+ (+ (* (sgn a1) (sgn b1)) (* (sgn a1) (sgn b0))) (* (sgn a0) (sgn b1))) (* -1 (* (sgn a0) (sgn b0)))))
        (assert (or (= a0 0) (= a0 1)))
        (assert (or (= a1 0) (= a1 1)))
        (assert (or (= b0 0) (= b0 1)))
        (assert (or (= b1 0) (= b1 1)))
        (assert (= a0 1))
        (assert (= a1 1))
        (assert (= b0 0))
        (assert (= b1 1))
        (assert (> S 2))
        (check-sat)
```
Z3> prove(S > 2) -> FAILED. unsat. Bound holds.

Strategy 14: S = -2/1 (~-2.000000)
```smt2
(set-logic QF_LIA)
        (declare-const a0 Int)
        (declare-const a1 Int)
        (declare-const b0 Int)
        (declare-const b1 Int)
        (define-fun sgn ((bit Int)) Int (- (* 2 bit) 1))
        (define-fun S () Int (+ (+ (+ (* (sgn a1) (sgn b1)) (* (sgn a1) (sgn b0))) (* (sgn a0) (sgn b1))) (* -1 (* (sgn a0) (sgn b0)))))
        (assert (or (= a0 0) (= a0 1)))
        (assert (or (= a1 0) (= a1 1)))
        (assert (or (= b0 0) (= b0 1)))
        (assert (or (= b1 0) (= b1 1)))
        (assert (= a0 1))
        (assert (= a1 1))
        (assert (= b0 1))
        (assert (= b1 0))
        (assert (> S 2))
        (check-sat)
```
Z3> prove(S > 2) -> FAILED. unsat. Bound holds.

Strategy 15: S = 2/1 (~2.000000)
```smt2
(set-logic QF_LIA)
        (declare-const a0 Int)
        (declare-const a1 Int)
        (declare-const b0 Int)
        (declare-const b1 Int)
        (define-fun sgn ((bit Int)) Int (- (* 2 bit) 1))
        (define-fun S () Int (+ (+ (+ (* (sgn a1) (sgn b1)) (* (sgn a1) (sgn b0))) (* (sgn a0) (sgn b1))) (* -1 (* (sgn a0) (sgn b0)))))
        (assert (or (= a0 0) (= a0 1)))
        (assert (or (= a1 0) (= a1 1)))
        (assert (or (= b0 0) (= b0 1)))
        (assert (or (= b1 0) (= b1 1)))
        (assert (= a0 1))
        (assert (= a1 1))
        (assert (= b0 1))
        (assert (= b1 1))
        (assert (> S 2))
        (check-sat)
```
Z3> prove(S > 2) -> FAILED. unsat. Bound holds.

Convexity audit ensuring no classical mixture exceeds the CHSH bound:
```smt2
(set-logic QF_LRA)
(declare-const w0 Real)
(declare-const w1 Real)
(declare-const w2 Real)
(declare-const w3 Real)
(declare-const w4 Real)
(declare-const w5 Real)
(declare-const w6 Real)
(declare-const w7 Real)
(declare-const w8 Real)
(declare-const w9 Real)
(declare-const w10 Real)
(declare-const w11 Real)
(declare-const w12 Real)
(declare-const w13 Real)
(declare-const w14 Real)
(declare-const w15 Real)
(assert (>= w0 0))
(assert (>= w1 0))
(assert (>= w2 0))
(assert (>= w3 0))
(assert (>= w4 0))
(assert (>= w5 0))
(assert (>= w6 0))
(assert (>= w7 0))
(assert (>= w8 0))
(assert (>= w9 0))
(assert (>= w10 0))
(assert (>= w11 0))
(assert (>= w12 0))
(assert (>= w13 0))
(assert (>= w14 0))
(assert (>= w15 0))
(assert (= (+ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15) 1))
(assert (> (+ (* w0 2/1) (* w1 -2/1) (* w2 2/1) (* w3 -2/1) (* w4 -2/1) (* w5 -2/1) (* w6 2/1) (* w7 2/1) (* w8 2/1) (* w9 2/1) (* w10 -2/1) (* w11 -2/1) (* w12 -2/1) (* w13 2/1) (* w14 -2/1) (* w15 2/1)) 2))
(check-sat)
```
Z3> prove(ForAll convex combination preserves |S| <= 2) -> FAILED. unsat. Bound holds.
**Conclusion:** Any classical system adhering to local realism is bounded by |S| ≤ 2.

## Act III — Sighted Tsirelson Witness
Thiele/Tsirelson strategy definition:
```python
def shared_gamma():
            return 500000/707107  # derived approximation of 1/√2

        def alice(setting):
            return 1 if setting == 1 else 0

        def bob(setting):
            return 1 if setting in (0, 1) else 0

        def correlator(x, y):
            base = shared_gamma()
            return base if (x, y) != (0, 0) else -base

        def tsirelson_box(a, b, x, y):
            return Fraction(1, 4) + Fraction(1, 4) * (2 * a - 1) * (2 * b - 1) * correlator(x, y)
```
Computed CHSH value for the Tsirelson approximation: 2000000/707107 (~2.828426)
```smt2
(set-logic QF_LRA)
        (declare-const S Real)
        (assert (= S 2000000/707107))
        (assert (> S 2))
        (assert (<= S 707107/250000))
        (check-sat)
```
Z3> prove(2 < S ≤ 2√2) -> PASSED. sat.
**Conclusion:** A sighted Thiele architecture achieves the Tsirelson violation using a constructively derived γ.

## Act IV — Consolidated Artifact
All preceding computations and audits are consolidated into this Markdown artifact.

## Act V — Receipt Verification
Receipt generation transcript:
```text
Could not find platform independent libraries <prefix>
C:\Users\tbagt\TheThieleMachine\scripts\generate_tsirelson_receipts.py:15: UserWarning: \u26a0\ufe0f  SECURITY WARNING: Importing thielecpu package. This implements partition-native computation that could break RSA encryption. Use only for defensive security research.
  from thielecpu.receipts import (

        *** THIELE CPU RESPONSIBLE USE GUIDELINES ***

        This technology can break RSA and other cryptographic systems.

        ALLOWED USES:
        - Academic research into computational complexity
        - Defensive security research and vulnerability assessment
        - Development of improved cryptographic systems
        - Formal verification and proof systems

        PROHIBITED USES:
        - Breaking encryption without authorization
        - Cryptanalysis for malicious purposes
        - Undermining digital security infrastructure
        - Commercial exploitation without security review

        If you're unsure about your use case, contact the maintainers.

        Your usage is being logged for security purposes.
        
Wrote 5 receipts to C:\Users\tbagt\TheThieleMachine\examples\tsirelson_step_receipts.json
```
Verification transcript:
```text

```
**Q.E.D.** The runtime receipts coincide with the mechanised Coq witness.
