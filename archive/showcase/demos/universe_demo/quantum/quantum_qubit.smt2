(set-logic QF_AUFLIA)

; Simple quantum qubit model for toy universe extension
; Represent qubit as 2D complex amplitudes, but simplify to real probabilities for SAT feasibility
; Qubit state: |psi> = a|0> + b|1>, with |a|^2 + |b|^2 = 1
; Use reals for amplitudes, assert normalization

(declare-const a_real Real) (declare-const a_imag Real)
(declare-const b_real Real) (declare-const b_imag Real)

; Normalization: |a|^2 + |b|^2 = 1
(assert (= (+ (* a_real a_real) (* a_imag a_imag) (* b_real b_real) (* b_imag b_imag)) 1.0))

; Pauli X gate: |psi> -> X|psi> = b|0> + a|1>
(declare-const x_a_real Real) (declare-const x_a_imag Real)
(declare-const x_b_real Real) (declare-const x_b_imag Real)
(assert (= x_a_real b_real)) (assert (= x_a_imag b_imag))
(assert (= x_b_real a_real)) (assert (= x_b_imag a_imag))

; Measurement in computational basis: probability of |0> = |a|^2
(declare-const prob_0 Real)
(assert (= prob_0 (+ (* a_real a_real) (* a_imag a_imag))))

; For IIT-like measure: define "consciousness" as entanglement or coherence
; Simplified: Phi proportional to off-diagonal coherence |a*b|^2 (magnitude squared)
(declare-const coherence Real)
(assert (= coherence (+ (* (+ (* a_real b_real) (* a_imag b_imag)) (+ (* a_real b_real) (* a_imag b_imag)))
                        (* (+ (* a_real b_imag) (* (- a_imag) b_real)) (+ (* a_real b_imag) (* (- a_imag) b_real))))))

; Assert Phi > 0 for coherent states
(declare-const phi_quantum Real)
(assert (= phi_quantum coherence))
(assert (> phi_quantum 0.0))

; Quantum rules hold, consciousness emerges

(check-sat)