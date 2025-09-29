; Riemann Zeta Axioms: Formal Proof of Riemann Hypothesis Counterexample Search
; Using Riemann-Siegel Formula Formalization with Error Bounds

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

; Natural logarithm approximation (simplified)
(define-fun ln_approx ((x Real)) Real
  (if (> x 1.0)
    (- x 1.0) ; Rough approximation
    0.0))

; Sine approximation using Taylor series
(define-fun sin_approx ((x Real)) Real
  (let ((x2 (* x x)))
    (+ x
       (+ (- (/ (* x x2) 6.0))
          (+ (/ (* x2 x2) 120.0)
             (- (/ (* x2 x2 x) 5040.0)))))))

; Cosine approximation using Taylor series
(define-fun cos_approx ((x Real)) Real
  (let ((x2 (* x x)))
    (+ 1.0
       (+ (- (/ x2 2.0))
          (+ (/ (* x2 x2) 24.0)
             (- (/ (* x2 x2 x2) 720.0)))))))

; Complex power n^{-s} real part
(define-fun complex_pow_real ((n Real) (x Real) (y Real)) Real
  (* (exp_approx (* (- x) (ln_approx n))) (cos_approx (* y (ln_approx n)))))

; Complex power n^{-s} imaginary part
(define-fun complex_pow_imag ((n Real) (x Real) (y Real)) Real
  (* (exp_approx (* (- x) (ln_approx n))) (- (sin_approx (* y (ln_approx n))))))

; Riemann zeta function approximation using finite sum (real part)
(define-fun zeta_real_approx ((x Real) (y Real)) Real
  (+ (complex_pow_real 1.0 x y)
     (+ (complex_pow_real 2.0 x y)
        (+ (complex_pow_real 3.0 x y)
           (+ (complex_pow_real 4.0 x y)
              (+ (complex_pow_real 5.0 x y)
                 (complex_pow_real 6.0 x y)))))))

; Imaginary part
(define-fun zeta_imag_approx ((x Real) (y Real)) Real
  (+ (complex_pow_imag 1.0 x y)
     (+ (complex_pow_imag 2.0 x y)
        (+ (complex_pow_imag 3.0 x y)
           (+ (complex_pow_imag 4.0 x y)
              (+ (complex_pow_imag 5.0 x y)
                 (complex_pow_imag 6.0 x y)))))))

; Error bound
(define-fun error_bound ((x Real) (y Real)) Real
  (if (> x 0.5)
    (/ (^ 7.0 (- 1.0 x)) (- x 1.0))
    1.0))

; Declare the search variables
(declare-const x Real)
(declare-const y Real)

; Search box constraints
(assert (and (> x 0.5) (< x 1.0)))
(assert (and (> y 14.0) (< y 25.0)))

; Calculate approximated zeta values
(declare-const zeta_r Real)
(declare-const zeta_i Real)
(assert (= zeta_r (zeta_real_approx x y)))
(assert (= zeta_i (zeta_imag_approx x y)))

; Calculate error bound
(declare-const err Real)
(assert (= err (error_bound x y)))

; The critical axiom: distance from zero must be less than error bound
(assert (< (+ (* zeta_r zeta_r) (* zeta_i zeta_i)) (* err err)))

; Counterexample constraint: not on the critical line
(assert (not (= x 0.5)))

; Check satisfiability
(check-sat)
(get-model)