
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

; Complex power n^{-s} real part
(define-fun complex_pow_real ((n Real) (sigma Real) (t Real)) Real
  (* (exp_approx (* (- sigma) (ln_approx n))) (cos_approx (* t (ln_approx n)))))

; Complex power n^{-s} imaginary part
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
(assert (= t 236.5242296658162))

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
