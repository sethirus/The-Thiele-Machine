#!/usr/bin/env python3
"""
Batch Audit of Riemann Zeros: Streamlined Version

Audits multiple zeros from Odlyzko's dataset using a single output file
and streamed results, avoiding folder bloat.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

from thielecpu.assemble import parse
from thielecpu.vm import VM
from thielecpu.state import State
from pathlib import Path
import json
from z3 import *
import io
from contextlib import redirect_stdout, redirect_stderr
import shutil

def generate_audit_smt(im_part):
    """Generate SMT content for auditing a specific zero."""
    return """
(set-logic QF_NRA)

; High-precision constants
(define-const PI Real 3.141592653589793)
(define-const E Real 2.718281828459045)

; Mathematical function definitions

; Exponential function approximation using Taylor series
(define-fun exp_approx ((x Real)) Real
  (+ 1.0
     (+ x
        (+ (/ (* x x) 2.0)
           (+ (/ (* x x x) 6.0)
              (+ (/ (* x x x x) 24.0)
                 (/ (* x x x x x) 120.0)))))))

; Natural logarithm approximation (improved)
(define-fun ln_approx ((x Real)) Real
  (if (> x 1.0)
    (- (- x 1.0) (/ (* (- x 1.0) (- x 1.0)) 2.0))
    0.0))

; Sine approximation using Taylor series
(define-fun sin_approx ((x Real)) Real
  (+ x
     (+ (- (/ (* x x x) 6.0))
        (+ (/ (* x x x x) 120.0)
           (- (/ (* x x x x x) 5040.0))))))

; Cosine approximation using Taylor series
(define-fun cos_approx ((x Real)) Real
  (+ 1.0
     (+ (- (/ (* x x) 2.0))
        (+ (/ (* x x x x) 24.0)
           (- (/ (* x x x x x x) 720.0))))))

; Complex power n^{{-s}} real part
(define-fun complex_pow_real ((n Real) (sigma Real) (t Real)) Real
  (* (exp_approx (* (- sigma) (ln_approx n))) (cos_approx (* t (ln_approx n)))))

; Complex power n^{{-s}} imaginary part
(define-fun complex_pow_imag ((n Real) (sigma Real) (t Real)) Real
  (* (exp_approx (* (- sigma) (ln_approx n))) (- (sin_approx (* t (ln_approx n))))))

; Riemann zeta function approximation using finite sum (real part)
(define-fun zeta_real_approx ((sigma Real) (t Real)) Real
  (+ (complex_pow_real 1.0 sigma t)
     (complex_pow_real 2.0 sigma t)
     (complex_pow_real 3.0 sigma t)
     (complex_pow_real 4.0 sigma t)
     (complex_pow_real 5.0 sigma t)
     (complex_pow_real 6.0 sigma t)
     (complex_pow_real 7.0 sigma t)
     (complex_pow_real 8.0 sigma t)
     (complex_pow_real 9.0 sigma t)
     (complex_pow_real 10.0 sigma t)))

; Imaginary part
(define-fun zeta_imag_approx ((sigma Real) (t Real)) Real
  (+ (complex_pow_imag 1.0 sigma t)
     (complex_pow_imag 2.0 sigma t)
     (complex_pow_imag 3.0 sigma t)
     (complex_pow_imag 4.0 sigma t)
     (complex_pow_imag 5.0 sigma t)
     (complex_pow_imag 6.0 sigma t)
     (complex_pow_imag 7.0 sigma t)
     (complex_pow_imag 8.0 sigma t)
     (complex_pow_imag 9.0 sigma t)
     (complex_pow_imag 10.0 sigma t)))

; Error bound
(define-fun error_bound ((sigma Real) (t Real)) Real
  (if (> sigma 0.5)
    (/ (^ 7.0 (- 1.0 sigma)) (- sigma 1.0))
    1.0))

; Declare the variables
(declare-const sigma Real)
(declare-const t Real)
(assert (= sigma 0.5))
(assert (= t {0}))

; Calculate approximated zeta values
(declare-const zeta_r Real)
(declare-const zeta_i Real)
(assert (= zeta_r (zeta_real_approx sigma t)))
(assert (= zeta_i (zeta_imag_approx sigma t)))

; Calculate error bound
(declare-const err Real)
(assert (= err (error_bound sigma t)))

; Audit assertion: assert that this point is NOT a zero (distance > threshold)
; If unsat, then it must be a zero within the approximation
(assert (> (+ (* zeta_r zeta_r) (* zeta_i zeta_i)) 0.0001))

(check-sat)
""".format(im_part)

def main():
    print("Thiele Machine: Batch Audit of Riemann Zeros")
    print("=" * 50)
    print("Auditing Odlyzko's zeros with single file output")
    print()

    # Read zeros
    with open('zeros1', 'r') as f:
        zeros = [float(line.strip()) for line in f.readlines()]

    num_zeros = len(zeros)
    print(f"Loaded {num_zeros} zeros from dataset")

    # Output file
    output_file = Path('batch_audit_results.txt')
    with open(output_file, 'w') as out_f:
        out_f.write("Batch Audit Results for Riemann Zeros\n")
        out_f.write("=" * 40 + "\n\n")

        passed = 0
        failed = 0
        unknown = 0

        for i, im_part in enumerate(zeros):
            print(f"Auditing zero {i+1}/{num_zeros}: Im(s) = {im_part}")

            # Generate SMT
            smt_content = generate_audit_smt(im_part)
            smt_path = Path(f"temp_audit_{i}.smt2")
            smt_path.write_text(smt_content)

            # Check SMT directly
            try:
                s = Solver()
                s.add(parse_smt2_string(smt_content))
                result = s.check()

                if result == unsat:
                    status = "PASSED"
                    passed += 1
                    print(f"  ✓ PASSED")
                elif result == sat:
                    status = "FAILED"
                    failed += 1
                    print(f"  ✗ FAILED")
                else:
                    status = "UNKNOWN"
                    unknown += 1
                    print(f"  ? UNKNOWN")

                # Write to file
                out_f.write(f"Zero {i+1}: Im(s) = {im_part} -> {status}\n")
                out_f.flush()  # Stream to file

            except Exception as e:
                print(f"  Error: {e}")
                out_f.write(f"Zero {i+1}: Im(s) = {im_part} -> ERROR: {e}\n")
                unknown += 1

            # Cleanup temp SMT
            if smt_path.exists():
                smt_path.unlink()

        # Summary
        out_f.write(f"\nSummary:\n")
        out_f.write(f"Passed: {passed}\n")
        out_f.write(f"Failed: {failed}\n")
        out_f.write(f"Unknown: {unknown}\n")
        out_f.write(f"Total: {num_zeros}\n")

    print(f"\nAudit complete. Results written to {output_file}")
    print(f"Passed: {passed}, Failed: {failed}, Unknown: {unknown}")

if __name__ == "__main__":
    main()