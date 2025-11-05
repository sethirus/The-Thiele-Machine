; Constants for gravitational constant, masses, distance, force
(declare-const G Real)
(declare-const m1 Real)
(declare-const m2 Real)
(declare-const r Real)
(declare-const Force Real)

; Axiom: Gravitational constant G (using Z3-compatible notation)
(assert (= G (/ 667430.0 10000000000000.0)))

; Axiom: Newton's law of universal gravitation F = G * m1 * m2 / r^2
(assert (= Force (/ (* G m1 m2) (* r r))))

; No specific values to force unsat; this is definitional
(check-sat)