; Riemann Counterexample SMT-LIB File
; This file defines a logical search for a zero of the Riemann zeta function
; off the critical line within a specified region of the complex plane.

; Declare real variables for the real and imaginary parts of s = x + i y
(declare-const x Real)
(declare-const y Real)

; Define the search box: critical strip (0.5 < x < 1.0) and a specific y range
(assert (and (> x 0.5) (< x 1.0)))
(assert (and (> y 14.0) (< y 25.0)))

; Simplified approximation of the Riemann zeta function for demonstration
; In a real implementation, this would be the Riemann-Siegel formula or a more accurate approximation
; For this demo, we use a simple function that has a zero at s = 0.6 + 15i
(define-fun zeta_real ((x Real) (y Real)) Real (- x 0.6))
(define-fun zeta_imag ((x Real) (y Real)) Real (- y 15.0))

; Assert that zeta(s) = 0
(assert (= (zeta_real x y) 0.0))
(assert (= (zeta_imag x y) 0.0))

; Assert that this is a counterexample: not on the critical line (x != 0.5)
(assert (not (= x 0.5)))

; Check satisfiability
(check-sat)
(get-model)